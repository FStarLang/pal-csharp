using Pal.Compiler.Passes;
using System.Collections.Immutable;
using System.Text;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// Emits the executable half of a method (doc/translation.md §5, §6).
///
/// <para>
/// Two rules govern everything here. <b>A-normalisation (R6.2):</b> every stateful
/// subexpression — a read of a cell, an array subscript, a call — is let-bound to a
/// fresh temporary, in C#'s left-to-right evaluation order; pure operations stay inline.
/// <b>Structure preservation (§0 rule 2):</b> loops stay loops, both branches of an
/// <c>if</c> are always emitted, and no statement is reordered, merged or elided.
/// </para>
/// </summary>
public sealed class CodeEmitter(
    SpecEmitter spec,
    DiagnosticBag diagnostics,
    IReadOnlyDictionary<string, IrClass>? classes = null,
    IReadOnlyDictionary<string, string>? overrides = null,
    HashSet<string>? slots = null,
    IReadOnlyDictionary<string, ImmutableHashSet<int>>? consumed = null,
    IReadOnlyDictionary<string, ImmutableArray<IrClassType>>? heapIndexed = null,
    IReadOnlyDictionary<string, ImmutableArray<RegionUse>>? regionHeld = null,
    ISet<string>? openMethods = null,
    ISet<string>? raising = null,
    ISet<string>? readOnlyMethods = null,
    IReadOnlyDictionary<string, IrMethod>? methods = null)
{
    /// <summary>R31.14. Every method, by name, for reading a callee's postcondition at a call.</summary>
    public IReadOnlyDictionary<string, IrMethod>? Methods { get; init; }

    /// <summary>R31.11. The ring node members that read their owner, by method name.</summary>
    public IReadOnlyDictionary<string, OwnerBorrow>? OwnerBorrows { get; init; }

    /// <summary>
    /// R27.50. Whether a statement emitted so far may have changed the receiver's model: a
    /// field write, a write to its region, or a call on it to a method that is not
    /// read-only. A loop entered while this is false, which itself leaves the receiver
    /// alone, holds it at its model on entry.
    /// </summary>
    private bool _receiverDirty;

    /// <summary>
    /// R27.50. The last time a call on the open receiver closed it around itself and
    /// reopened it after (R22.15), with the regions the callee held it at (R27.13).
    /// </summary>
    private (Slot Self, ImmutableArray<IrClassType>? Heaps)? _lastReopen;
    // R27.52. Whether the loop being emitted holds the receiver at an existential model.
    private bool _receiverRenamed;
    // R27.50. The lines of the last reopening after a callee that kept the receiver at its
    // model (start and end in `_lines`): an arm that ends with them may drop them instead.
    private (int Start, int End)? _keptReopen;

    /// <summary>R27.50. For each loop being emitted, whether it was entered with the receiver unchanged.</summary>
    private readonly Stack<bool> _pristineLoops = new();

    private bool DirtiesReceiver(IrStmt stmt)
    {
        if (ReceiverWrites(stmt).Record) return true;
        if (_method?.DeclaringClass is { } dc && classes is not null && classes.TryGetValue(dc, out var owner) &&
            RegionsOf(owner).Any(k => WritesRegion(stmt, k.Name, skipReadOnly: true)))
            return true;
        return Check.Statements(stmt).SelectMany(Check.Expressions).SelectMany(Check.Subexpressions)
            .OfType<IrCall>()
            .Any(c => c.HasReceiver && c.Args is [IrVar { Name: Names.This }, ..] &&
                      readOnlyMethods?.Contains(c.Callee) != true);
    }

    /// <summary>
    /// The output, one line at a time, each remembering the C# it came from.
    ///
    /// A list of lines rather than a <c>StringBuilder</c> because <see cref="Capture"/>
    /// emits into this buffer, takes the text back out and re-appends it somewhere else,
    /// and doing that to a character buffer means splitting text back into lines to move
    /// it — which is exactly the operation that would silently misalign a position map.
    /// Lines that are never joined cannot come apart.
    /// </summary>
    private readonly List<EmittedLine> _lines = [];

    /// <summary>The C# a line is currently being emitted for; see <see cref="Statement"/>.</summary>
    private IrLoc? _loc;

    private readonly Dictionary<string, Slot> _slots = [];
    private int _indent = 1;
    private int _temp;
    private int _ghost;
    private int _loop;

    /// <summary>
    /// R5.10. The escape flags of the innermost loop being emitted, or null outside any
    /// loop. <c>Break</c> is allocated before the loop and read by its guard and measure;
    /// <c>Continue</c> is allocated inside the body and reset on every iteration.
    /// </summary>
    private sealed record Escape(string? Break, string? Continue);

    private Escape? _escape;

    /// <summary>
    /// R10.7. The <c>intro_cons</c> owed by each null test currently open, innermost last.
    /// A recursive object is opened by the <em>null test the C# already writes</em>, exactly
    /// as an ordinary receiver is opened by R4.10's bracket, and like that bracket it has to
    /// be closed on every path out of the branch — including a <c>return</c> in the middle
    /// of it, which is why this is a stack rather than a line emitted after the branch.
    /// </summary>
    private readonly List<string> _windows = [];

    /// <summary>
    /// R4.10. The objects this method holds, in declaration order. Each is unfolded once
    /// on entry and re-folded on every exit; between the two the body owns the
    /// representation and may read and write fields.
    /// </summary>
    private ImmutableArray<Slot> _objects = ImmutableArray<Slot>.Empty;

    // The slots that came from the signature. Their invariants appear in this method's
    // own postcondition, so they are the ones a conversion may not give away (R9.15).
    private ImmutableDictionary<string, Slot> _params = ImmutableDictionary<string, Slot>.Empty;

    /// <summary>
    /// R4.14. Objects allocated by this method. Their invariants are owned here and, unless
    /// the reference is returned, are still owned when the method ends — so they must be
    /// dropped. This is where the CLR's garbage collector enters the translation: F15 says
    /// Pulse slprops are affine, so the resource may simply be discarded, but Pulse still
    /// requires the discard to be *written*.
    /// </summary>
    private readonly List<Slot> _objectLocals = [];

    /// <summary>
    /// How many enclosing blocks would have to discard what they declared as they close
    /// (F19). Zero means the nearest enclosing block ends at the method's exit, where the
    /// postcondition is known.
    /// </summary>
    private int _closingBlocks;

    /// <summary>R6.11a. Array locals declared in a nested block, which must be moved out of it.</summary>
    private readonly Dictionary<Slot, IrLoc> _nestedArrays = [];

    private string Fresh() => "t" + _temp++;
    private string FreshValue(string name) => $"v{name}_{_ghost++}";

    private void Line(string text) =>
        _lines.Add(new EmittedLine(new string(' ', _indent * 2) + text + "\n", _loc));

    private string Text() => string.Concat(_lines.Select(l => l.Text));

    /// <summary>
    /// What line of the emitted body each C# construct produced, for mapping an F* error
    /// back to the source. Line numbers are one-based and relative to the body, which is
    /// all this class knows; <c>PulseEmitter</c> shifts them by where the body was placed.
    /// </summary>
    public ImmutableArray<LineOrigin> Origins()
    {
        var origins = ImmutableArray.CreateBuilder<LineOrigin>();
        var line = 1;
        foreach (var emitted in _lines)
        {
            if (emitted.Loc is { } loc) origins.Add(new LineOrigin(line, loc));
            line += emitted.Text.Count(c => c == '\n');
        }
        return origins.ToImmutable();
    }

    /// <summary>The plan of the method being emitted, needed by R13.3's prelude.</summary>
    private MethodPlan? _plan;

    /// <summary>The method being emitted: R19.2's throw closes its objects as a return does.</summary>
    private IrMethod? _method;

    /// <summary>
    /// R19.3. The exceptions that may escape the innermost enclosing construct, as a
    /// predicate of the exception's binder: the method's <c>[Throws]</c> at the top, and
    /// inside a <c>try</c> its own <c>raises</c>. Innermost last.
    /// </summary>
    private readonly List<Func<string, string>> _raises = [];

    /// <summary>R19.4. The exception binder of each enclosing catch clause, innermost last.</summary>
    private readonly List<string> _caught = [];

    /// <summary>How many object locals were declared outside the innermost <c>try</c>.</summary>
    private readonly List<int> _tryMarks = [];

    private int _try;

    public string EmitBody(IrMethod method, MethodPlan plan)
    {
        _plan = plan;
        _method = method;
        _receiverDirty = false;
        _lastReopen = null;
        _receiverRenamed = false;
        _keptReopen = null;
        _raises.Add(plan.ThrowsProp);
        // In declaration order, not `plan.Slots`': see MethodPlan.SlotOrder. `_slots` is
        // a plain Dictionary, so every later walk of it inherits the order set here.
        foreach (var name in plan.SlotOrder) _slots[name] = plan.Slots[name];

        if (method is { IsConstructor: true, ReturnType: IrClassType built })
        {
            // R4.2 applies here too, and the prologue has to precede the initialisers: a
            // constructor's parameter becomes a cell on the same conservative test as any
            // other method's, and until R3.10b nothing had ever handed one to a call, so
            // the omission was unreachable rather than absent.
            foreach (var (cell, source) in plan.Prologue) Line($"let mut {cell} = {source};");
            Construct(method, built);
            return Text();
        }

        // R4.10. Only the *receiver* of the class's own methods is opened. An object that
        // merely passes through — a parameter of a static method, or an argument on its
        // way to a callee — must stay folded, because every function that takes it expects
        // its invariant, not its representation. The receiver is the one object whose
        // fields this body may name at all (PALCS0523 refuses the rest), so the bracket
        // goes exactly where the field accesses are.
        _params = plan.Slots;
        _constructsArrays = false;
        _objects = method.DeclaringClass is not null &&
                   plan.Slots.TryGetValue(Names.This, out var self) &&
                   self.Kind == SlotKind.Object && !self.Open
            ? [self]
            : [];

        // R4.10c. Opened only if the body actually names a field, because a call on `this`
        // needs the invariant *folded* -- that is what the callee's contract requires. A
        // method that only delegates (`int Again() => Get();`, and every computed property
        // that reads through another one, R9.20) touches no field, so opening the bracket
        // around it would hand the callee a representation where it expects an invariant.
        // The comment above has always said the bracket goes where the field accesses are;
        // this is what makes it true.
        if (!TouchesFields(method)) _objects = [];
        else if (_objects is [{ ViewBase: not null }] && SelfCall(method) is { } selfCall)
        {
            // R4.10c, the other half. The bracket has one shape, and the two demands are
            // opposite: a field access needs the invariant *unfolded* and a call on `this`
            // needs it *folded*, because that is what the callee's contract asks for.
            // Closing the bracket around the call would be a proof step the emitter
            // invented — R4.11a's fold has to hold of the state at the fold point, and a
            // mutator's intermediate state is exactly where it does not (R3.10's `Shift`).
            // So this is refused, not approximated; before it was emitted, ill-typed, with
            // no diagnostic at all.
            diagnostics.Error("PALCS0597", selfCall.Loc,
                $"`{Unqualify(method.Name, method.DeclaringClass)}` reads a field of " +
                $"`{method.DeclaringClass}` and also calls " +
                $"`{Unqualify(selfCall.Callee, method.DeclaringClass)}` on the same object. " +
                "The field access needs the invariant " +
                "unfolded and the call needs it folded (doc/translation.md R4.10c), and one " +
                "body cannot have it both ways. Read the field through the method, or inline " +
                "the callee.");
        }

        // R27.50. Two objects of one class held whole are two objects: said once, on entry,
        // where each is still held as the contract hands it over.
        if (classes is not null) EmitDistinct(method, plan);

        // The invariant is abstract to the caller, so the body cannot touch a field until
        // it is unfolded, and the matching `fold` on each exit path re-establishes it.
        foreach (var obj in _objects) OpenReceiver(obj);

        // R4.2: rebind assigned by-value parameters as cells.
        foreach (var (cell, source) in plan.Prologue) Line($"let mut {cell} = {source};");

        var statements = method.Body is IrBlock b ? b.Statements : [method.Body!];
        EmitSequence(statements, method, plan);
        return Text();
    }

    /// <summary>
    /// Emits a statement sequence in <em>tail</em> position: the last statement supplies
    /// the block's value (R5.5). Every earlier statement is emitted for its effect, and
    /// a <c>return</c> among them is an error — Normalize's R5.5b has already moved the
    /// ones it can into branches.
    /// </summary>
    private void EmitSequence(ImmutableArray<IrStmt> statements, IrMethod method, MethodPlan plan)
    {
        statements = [.. statements.Select(SplitShortCircuit)];
        for (var i = 0; i < statements.Length - 1; i++)
        {
            // R22.12. Pulse joins the arms of an unannotated `if` resource by resource, so
            // an arm that replaces an open object's array field leaves the join holding the
            // box and the new array under unrelated existentials. The rest of the block is
            // moved into both arms instead, so that no join is needed.
            if (statements[i] is IrIf split && JoinLoses(split))
            {
                var rest = statements.RemoveRange(0, i + 1);
                // An arm that never completes keeps none of the rest: behind its
                // `unreachable ()` nothing is held, so not even a read typechecks.
                ImmutableArray<IrStmt> Arm(IrStmt? arm)
                {
                    ImmutableArray<IrStmt> own = arm is IrBlock ab ? ab.Statements : arm is null ? [] : [arm];
                    return own is [.., IrThrow or IrReturn or IrExprStmt { Expr: IrCall { DoesNotReturn: true } } or IrGhostStmt { Kind: GhostKind.Unreachable }]
                        ? own : [.. own, .. rest];
                }
                Tail(split with
                {
                    Then = new IrBlock(split.Then.Loc, Arm(split.Then)),
                    Else = new IrBlock(split.Else?.Loc ?? split.Loc, Arm(split.Else)),
                }, method, plan);
                return;
            }
            if (statements[i] is IrReturn early)
            {
                diagnostics.Unsupported(early.Loc, "A `return` that is not the last statement",
                    "pal-csharp translates a method body as a single block, so a `return` " +
                    "must be reachable as the block's value.");
                return;
            }
            Statement(statements[i], plan);
        }

        if (statements.Length > 0) Tail(statements[^1], method, plan);
        else EndOfMethod(method, plan);
    }

    private static bool IsVoid(IrMethod method) => method.ReturnType is IrPrim { Kind: PrimKind.Void };

    private static bool EndsInBareReturn(IrStmt s) => s switch
    {
        IrReturn { Value: null } => true,
        IrBlock { Statements: [.., var last] } => EndsInBareReturn(last),
        _ => false,
    };

    /// <summary>
    /// Emits the statement whose value is the enclosing block's value. Only three shapes
    /// can occupy that position; anything else is emitted for its effect and the block
    /// closes with <c>()</c>, which is well typed exactly when the method returns void.
    /// </summary>
    private void Tail(IrStmt stmt, IrMethod method, MethodPlan plan)
    {
        var outer = _loc;
        _loc = stmt.Loc;
        try { TailCore(stmt, method, plan); } finally { _loc = outer; }
    }

    private void TailCore(IrStmt stmt, IrMethod method, MethodPlan plan)
    {
        switch (stmt)
        {
            case IrReturn { Value: null }:
                if (NeedsEpilogue) CloseObjects(method, plan);
                Line("()");
                return;

            case IrReturn ret:
            {
                // The value is computed *before* the closing `fold`, because computing it
                // may read a field and so needs the representation still open; it is
                // let-bound so that the `fold` can be interposed between the read and the
                // block's value.
                // R34.10. A reassigned array local is taken out of its cell.
                if (ret.Value is IrVar rv && ArrayCellOf(rv) is { } taken)
                {
                    var a = Fresh();
                    Line($"let {a} = Pulse.Lib.CSharp.ArrayCell.take {taken.Binder};");
                    _objectLocals.Remove(taken);
                    _slots[rv.Name] = taken with { Kind = SlotKind.Array, Binder = a };
                    CloseObjects(method, plan, a);
                    Line(a);
                    return;
                }
                var text = Inject(method.ReturnType, ret.Value!, Expr(ret.Value!));
                if (!NeedsEpilogue) { Line(text); return; }

                // A returned object must keep the binder the callee produced it under:
                // re-binding it would leave the context holding its invariant under the
                // old name, which the frame rule cannot match (Error 228). Everything else
                // is let-bound so the epilogue can be interposed before the block's value.
                // R22.28. A returned array is matched by name just as an object is.
                if (IsObjectBinder(text) ||
                    method.ReturnType is IrArrayType && System.Text.RegularExpressions.Regex.IsMatch(text, @"^[A-Za-z_][\w']*$"))
                {
                    if (_objectLocals.FirstOrDefault(l => l.Binder == text) is { Index: not null } ix)
                        Forget(ix);
                    CloseObjects(method, plan, text);
                    Line(text);
                    return;
                }

                var t = Fresh();
                Line($"let {t} = {text};");
                CloseObjects(method, plan, ownedBy: plan.ResultOwned.IsDefaultOrEmpty ? null : t);
                Line(t);
                return;
            }

            case IrBlock b:
                Scoped(() => EmitSequence(b.Statements, method, plan), dropAtEnd: false);
                return;

            // R19.2. `raise` has every type, so a throw is a tail of any method.
            case IrThrow th:
                Throw(th, plan, tail: true);
                return;

            // R22.12. An `if` with no `else` in tail position is split as one with an empty
            // `else`, so that each arm closes the method itself and no join is needed.
            case IrIf { Else: null } bare when JoinLoses(bare):
                Tail(bare with { Else = new IrBlock(bare.Loc, []) }, method, plan);
                return;

            // R33.16. Likewise in a void method when the arm returns (R26.2's
            // `if (__pal_returned) return;` closing a nested block): the missing `else`
            // falls off the end, which is a `return;` too.
            case IrIf { Else: null } guard when IsVoid(method) && EndsInBareReturn(guard.Then):
                Tail(guard with { Else = new IrBlock(guard.Loc, []) }, method, plan);
                return;

            case IrIf { Else: not null } i:
            {
                // R32.4. Each arm ends the method, so a field one arm closes (R27.59) is
                // still open in the other.
                var fieldsOpen = _fieldOpen.ToList();
                void RestoreFieldsOpen()
                {
                    _fieldOpen.Clear();
                    foreach (var (k, v) in fieldsOpen) _fieldOpen[k] = v;
                }
                if (NullTest(i.Cond) is { } window)
                {
                    var dirtyAtWindow = _receiverDirty;
                    NullWindow(window, i, branch => { _receiverDirty = dirtyAtWindow; RestoreFieldsOpen(); Tail(branch!, method, plan); }, tail: true);
                    return;
                }
                if (i.Cond is IrBinary pnb && PlainNullTest(pnb) is { } ptest)
                {
                    var dirtyAtPlain = _receiverDirty;
                    PlainNullWindow(ptest, i, branch => { _receiverDirty = dirtyAtPlain; RestoreFieldsOpen(); Tail(branch!, method, plan); }, tail: true);
                    return;
                }
                var cond = Expr(i.Cond);
                Line($"if ({cond}) {{");
                _indent++;
                // Each arm ends the method, so what one arm moves out of a local (R22.12)
                // is still owned by that local in the other.
                var owned = _objectLocals.ToList();
                var arrays = _slots.Where(p => p.Value.Kind is SlotKind.Array or SlotKind.ArrayCell).ToList();
                // R27.50. Likewise the receiver is as dirty in the other arm as before both.
                var dirty = _receiverDirty;
                Tail(i.Then, method, plan);
                _receiverDirty = dirty;
                _objectLocals.Clear();
                _objectLocals.AddRange(owned);
                RestoreFieldsOpen();
                foreach (var (n, sl) in arrays) _slots[n] = sl;
                _indent--;
                Line("} else {");
                _indent++;
                Tail(i.Else, method, plan);
                _indent--;
                Line("}");
                return;
            }

            // R22.11, in tail position. `unreachable ()` has every type, so it is the
            // block's value, and no epilogue follows it: behind it nothing is held.
            case IrExprStmt { Expr: IrCall { DoesNotReturn: true } dnr }:
                DoesNotReturnCall(dnr, plan);
                Line("unreachable ()");
                return;

            // R27.48. `Pal.Unreachable()` in tail position: proved unreachable, so nothing
            // need be given back.
            case IrGhostStmt { Kind: GhostKind.Unreachable }:
                Line("unreachable ()");
                return;

            default:
                Statement(stmt, plan);
                // The block's value is not the statement above it: it is the point at which
                // the method's postcondition is proved. Attributing it to the last statement
                // reads as an accusation against a statement that is very often fine --
                // `test/pulse_refusals/cases/BorrowNotReturned.cs` writes through a span, and
                // it is the *method* that then cannot state anything about the array. So the
                // epilogue is located at the method, where an unprovable postcondition
                // belongs. An explicit `return` keeps its own location, because there the
                // user did write the exit.
                EndOfMethod(method, plan);
                return;
        }
    }

    /// <summary>
    /// The implicit exit at the bottom of a body: close any open objects and give the block
    /// its unit value, both located at the method rather than at whatever statement happened
    /// to come last.
    /// </summary>
    private void EndOfMethod(IrMethod method, MethodPlan plan)
    {
        var outer = _loc;
        _loc = method.Loc;
        try
        {
            if (NeedsEpilogue) CloseObjects(method, plan);
            if (IsVoid(method)) Line("()");
        }
        finally { _loc = outer; }
    }

    // =======================================================================
    // Objects (R4.10-R4.11a)
    // =======================================================================

    /// <summary>
    /// R4.12. A constructor allocates the representation, establishes the invariant on it
    /// and returns the object. Nothing is freed: Pulse slprops are affine and the CLR is
    /// garbage collected (F15).
    ///
    /// <para>The body is required to be a sequence of field initialisations, because that
    /// is what a record literal can express. A constructor that reads a field it has
    /// written, or calls a method on the half-built object, is refused rather than
    /// approximated: two-phase initialisation needs an invariant that holds of a partial
    /// object, which the scheme does not have.</para>
    /// </summary>
    private void Construct(IrMethod method, IrClassType built)
    {
        // R9.21a. An open class's constructor keeps the return type the user declared, so
        // every `new C(…)` is untouched, and allocates the generated leaf. The two are
        // reconciled once, here, by the ordinary upcast (R9.15) -- the same step the reader
        // would get from `C c = new C__impl(…)` written out.
        var allocated = method.ConstructsLeaf is { } leafName ? new IrClassType(leafName) : built;
        Construct(method, built, allocated);
    }

    private void Construct(IrMethod method, IrClassType built, IrClassType alloc)
    {
        if (classes is null || !classes.TryGetValue(alloc.Name, out var decl))
        {
            // The class is missing because the frontend refused it, and that refusal is the
            // diagnostic the user needs. Reporting the constructor too names a symptom of a
            // cause already reported, and sends the reader to the wrong line.
            if (!diagnostics.HasErrors)
                diagnostics.Unsupported(method.Loc, $"A constructor of `{built.Name}`");
            return;
        }

        // R4.12c. `C(…) : this(args)` with nothing after it *is* the chained constructor's
        // result, so it emits that call and returns it. The object comes back with its
        // invariant folded, which is what this function's own postcondition asks for, so
        // there is nothing between the call and the return -- R9.15d, and the same shape
        // any method returning a class has.
        var statements = method.Body is IrBlock b ? b.Statements : [method.Body!];
        if (statements is [IrExprStmt { Expr: IrCall chained }, ..])
        {
            if (statements.Length > 1)
            {
                ConstructChained(method, decl, built, chained, statements[1..]);
                return;
            }
            Line($"{Expr(chained)}");
            return;
        }

        // R22.9. A body that is more than field initialisations runs as C# runs it: the
        // object is allocated with every field at its default, and the body is then an
        // ordinary method body over the open representation. R24.7: so does one over a
        // class with a nullable array field, whose `null` the open path knows how to own.
        if (alloc.Name == built.Name && decl.Recursion is null &&
            (statements.Any(st => !IsInitialiser(st)) || decl.Fields.Any(f => f.IsNullableArray)))
        {
            ConstructOpen(method, decl, alloc, statements);
            return;
        }

        var initialisers = new Dictionary<string, string>();
        foreach (var stmt in statements)
        {
            if (stmt is IrAssign { Target: IrField { Receiver: IrVar { Name: Names.This } } f } a)
            {
                initialisers[f.Field] = Expr(a.Value);
                continue;
            }
            // R9.21c. `D(…) : base(args)` is inlined by binding the base constructor's
            // parameters to the arguments and then running its assignments, so a leading
            // `let` is part of a constructor body. Nothing else is: an assignment still
            // may not run before the invariant holds.
            if (stmt is IrLocalDecl { Init: not null } d && initialisers.Count == 0)
            {
                var bound = Names.Local(d.Name);
                Line($"let {bound} = {Inject(d.Type, d.Init, Expr(d.Init))};");
                _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Value, bound);
                continue;
            }
            if (stmt is IrBlock { Statements.IsEmpty: true }) continue;
            diagnostics.Unsupported(stmt.Loc, "A constructor statement that is not a field initialisation",
                "A constructor may only assign its own fields: the object's invariant does " +
                "not hold until every field has a value, so nothing else can run first.");
            return;
        }

        var fields = new List<string>();
        foreach (var (field, i) in decl.Fields.Select((f, i) => (f, i)))
        {
            // R22.9. C# zero-initialises a field the constructor does not assign; a field
            // with no default value (an array, an object) is still refused.
            if (!initialisers.TryGetValue(field.Name, out var value) &&
                field.Type is IrPrim or IrTypeParamType or IrNamedType)
                value = Default(field.Type);
            // R27.6. A pointer into a region starts null, in a region that starts empty.
            // Typed (R31.2): in a ring's owner nothing else names the type arguments.
            if (value is null && IsRegionType(field.Type))
                value = $"(B.null #{PulseEmitter.RegionRaw((IrClassType)field.Type!)})";
            if (value is null)
            {
                diagnostics.Unsupported(method.Loc,
                    $"A constructor that leaves `{field.Name}` uninitialised",
                    "Assign every field: the invariant is established over the whole " +
                    "representation, so a default-valued field would have to satisfy it by luck.");
                return;
            }
            fields.Add((i == 0 ? Names.ClassProjection(decl.Name, field.Name) : Names.Field(field.Name))
                       + " = " + value);
        }

        Line($"let {Names.Result} = B.alloc ({{ {string.Join("; ", fields)} }});");
        // R10.6b. `new` never returns null in C#, and under R10.2 that is a *typing*
        // obligation rather than a fact about the encoding: the constructor returns
        // `class_C`, the non-null refinement, while `B.alloc` returns `class_C__opt`.
        // The step that bridges them is `B.pts_to_not_null`, a Pulse library lemma
        // applied to the `pts_to` the allocation just produced. The emitter is not
        // inventing a proof here — it is discharging, once and uniformly, the C#
        // guarantee that the surface type already states.
        Line($"B.pts_to_not_null {Names.Result};");

        // R10.6a. Allocation is the one place a new cell enters the induction, and R10.4's
        // `intro_cons` is R3.10b's `fold` — the sub-object's invariant is already in the
        // context, because R4.12b's caller gave it away when it passed the reference.
        if (decl.Recursion is not null)
        {
            Line($"{Names.ClassModule(decl.Name)}.{Names.ClassIntro(decl.Name)} {Names.Result};");
            Line(Names.Result);
            return;
        }

        var slot = new Slot(Names.This, alloc, SlotKind.Object, Names.Result)
        {
            PreModel = null,
            PostModel = "post_" + Names.This,
        };
        foreach (var k in RegionsOf(decl))
            Line($"{Frontend.Region.Module}.empty #{PulseEmitter.RegionRaw(k)} ();");
        Line($"fold {Inv(alloc)} {Names.Result} {ModelWitness(decl, slot)};");
        if (alloc.Name != built.Name)
        {
            var up = Fresh();
            // R9.16. The conversion keeps the index, and a *returned* reference wants the
            // plain invariant -- which is what this constructor's own postcondition, and
            // every `new C(…)` in the program, is written against.
            if (UpcastChain(alloc.Name, Names.Result, null, null, built, Names.This, up)
                is { Index: not null } ix)
                Line($"{Names.ClassModule(built.Name)}.{Names.ClassForgetImpl(built.Name)} " +
                     $"{up} {ix.Index};");
            Line(up);
            return;
        }
        Line(Names.Result);
    }


    private static bool IsInitialiser(IrStmt stmt) => stmt is
        IrAssign { Target: IrField { Receiver: IrVar { Name: Names.This } } } or
        IrLocalDecl { Init: not null } or
        IrBlock { Statements.IsEmpty: true };

    /// <summary>
    /// R22.9. The constructor of C#'s own semantics: allocate with every field at its
    /// default, then run the body over the open object, and fold at the end.
    ///
    /// <para>The CLR's default for an array field is <c>null</c>, which the scheme's
    /// non-null array type has no value for. The allocation stands in a fresh empty
    /// array, and the stand-in is sound only because it is never observed: a body that
    /// does not assign such a field on every path that completes is refused.</para>
    /// </summary>
    /// <summary>
    /// R27.45. <c>C(…) : this(args) { body }</c>. The chained constructor returns the object
    /// with its invariant folded at some model; the body then runs as an instance method's
    /// does, over that object opened (R4.10), and the object is closed at the end like the
    /// one R22.9 builds. The chained constructor's postcondition is all the body knows of
    /// the object at the start, which is exactly C#'s order of evaluation.
    /// </summary>
    private void ConstructChained(IrMethod method, IrClass decl, IrClassType built, IrCall chained,
        ImmutableArray<IrStmt> rest)
    {
        var self = new IrVar(method.Loc, Names.This) { Type = built };
        if (rest.Any(LoopOrTryReturn))
        {
            diagnostics.Unsupported(method.Loc, "A `return` inside a loop or `try` in a constructor");
            return;
        }
        var obj = Expr(chained);
        var m = FreshValue(built.Name);
        Line($"with {m}. assert ({Inv(built)} {obj} {m});");
        var slot = new Slot(Names.This, built, SlotKind.Object, obj)
        {
            PreModel = m,
            PostModel = "post_" + Names.This,
        };
        Line(Unfold(slot) + ";");
        _slots[Names.This] = slot;
        _objects = [slot];
        _objectResults.Remove(obj);
        EmitSequence(CloseWith(rest, self), method, _plan!);
    }

    private static bool LoopOrTryReturn(IrStmt s) => s switch
    {
        IrBlock b => b.Statements.Any(LoopOrTryReturn),
        IrIf i => LoopOrTryReturn(i.Then) || i.Else is { } e && LoopOrTryReturn(e),
        IrReturn => false,
        _ => ContainsReturn(s),
    };

    /// <summary>
    /// R27.45. The body of a chained constructor as a block that returns the object: every
    /// <c>return;</c> becomes <c>return this;</c>, and every path that falls off the end
    /// gains one. R5.5b has already made a guard <c>if (c) { …; return; }</c> the
    /// <c>if</c>/<c>else</c> it stands for, so each return is in tail position.
    /// </summary>
    private static ImmutableArray<IrStmt> CloseWith(ImmutableArray<IrStmt> body, IrExpr self)
    {
        var stmts = body.Select(s => Returns(self)(s)).ToImmutableArray();
        if (stmts.IsEmpty) return [new IrReturn(self.Loc, self)];
        var last = stmts[^1];
        return [.. stmts.Take(stmts.Length - 1), .. Close(last, self)];
    }

    private static ImmutableArray<IrStmt> Close(IrStmt last, IrExpr self) => last switch
    {
        IrReturn or IrThrow or IrGhostStmt { Kind: GhostKind.Unreachable } or
            IrExprStmt { Expr: IrCall { DoesNotReturn: true } } => [last],
        IrBlock b => [b with { Statements = CloseWith(b.Statements, self) }],
        IrIf i => [i with
        {
            Then = new IrBlock(i.Then.Loc, CloseWith([i.Then], self)),
            Else = new IrBlock(i.Loc, CloseWith(i.Else is { } e ? [e] : [], self)),
        }],
        _ => [last, new IrReturn(last.Loc, self)],
    };

    private static Func<IrStmt, IrStmt> Returns(IrExpr self) => s => s switch
    {
        IrReturn { Value: null } r => r with { Value = self },
        IrBlock b => b with { Statements = [.. b.Statements.Select(Returns(self))] },
        IrIf i => i with { Then = Returns(self)(i.Then), Else = i.Else is { } e ? Returns(self)(e) : null },
        _ => s,
    };

    private void ConstructOpen(IrMethod method, IrClass decl, IrClassType alloc, ImmutableArray<IrStmt> statements)
    {
        if (statements.Any(ContainsReturn))
        {
            diagnostics.Unsupported(method.Loc, "A `return` in a constructor");
            return;
        }
        var assigned = Assigned(statements);
        var fields = new List<string>();
        foreach (var (field, i) in decl.Fields.Select((f, i) => (f, i)))
        {
            string value;
            switch (field.Type)
            {
                // R24.7. A nullable array field the constructor leaves alone is `null`,
                // which owns nothing; one it assigns starts out `null` too, and the
                // assignment drops that.
                case IrArrayType nat when field.IsNullableArray:
                    value = Fresh();
                    Line($"let {value} = NA.alloc_null ({Types.Render(nat.Element)}) ();");
                    break;
                case IrArrayType at when assigned is null || assigned.Contains(field.Name):
                    value = Fresh();
                    Line($"let {value} = alloc_empty #({Types.Render(at.Element)}) ();");
                    break;
                case IrPrim or IrTypeParamType or IrNamedType:
                    value = Default(field.Type);
                    break;
                // R33.25. A nullable reference field starts out `null`, as the CLR's does.
                case IrOptionType none:
                    value = $"(None #{Types.Atom(none.Inner)})";
                    break;
                // R25.1. A comparer's stand-in is the default comparer, under the same
                // condition as an array's: it is never observed.
                case IrUserSpecType { Args: [var cmpElement] } cmp
                    when Frontend.Sorted.IsComparer(cmp) && (assigned is null || assigned.Contains(field.Name)):
                    value = $"({Frontend.Sorted.Order}.default_comparer {Types.Atom(cmpElement)})";
                    break;
                default:
                    diagnostics.Unsupported(method.Loc,
                        $"A constructor that does not assign `{field.Name}` on every path",
                        "C# leaves the field `null`, which its type has no value for " +
                        "(doc/translation.md R22.9).");
                    return;
            }
            fields.Add((i == 0 ? Names.ClassProjection(decl.Name, field.Name) : Names.Field(field.Name))
                       + " = " + value);
        }
        Line($"let {Names.Result} = B.alloc ({{ {string.Join("; ", fields)} }});");
        Line($"B.pts_to_not_null {Names.Result};");

        var slot = new Slot(Names.This, alloc, SlotKind.Object, Names.Result)
        {
            PreModel = null,
            PostModel = "post_" + Names.This,
        };
        _slots[Names.This] = slot;
        _objects = [slot];
        _constructsArrays = decl.Fields.Any(f => f.Type is IrArrayType);
        var self = new IrVar(method.Loc, Names.This) { Type = alloc };
        EmitSequence([.. statements, new IrReturn(method.Loc, self)], method, _plan!);
    }

    /// <summary>
    /// R22.12. Whether Pulse's join after this <c>if</c> would lose what the method needs:
    /// an open object's array field replaced, an array's contents copied into (R22.20), or a
    /// closed receiver's model moved by a call (R25.10).
    /// </summary>
    private bool JoinLoses(IrIf i) =>
        (_objects.Length > 0 && (ReplacesArrayField(i) || CallsOpenReceiver(i) || ThrowGuard(i))) || CopiesArray(i) ||
        // R32.12. A wrapping struct's guard tests what a call of the wrapped struct returned.
        (ThrowGuard(i) && Check.Subexpressions(i.Cond).Any(e => e is IrCall)
            && _method?.Parameters.Any(p => p.Name == Frontend.BorrowContext.Self) == true) ||
        MutatesClosedReceiver(i) || MovesRegion(i) || BreaksLoop(i) || PassesLambda(i) ||
        // R32.14. A view's member called with the record by reference rebinds the record.
        Check.Statements(i).SelectMany(Check.Expressions).Any(PassesRefSelf) ||
        WritesOpenRecord(i);

    /// <summary>
    /// R32.6. An arm that passes a lambda to a <c>[Callback]</c> parameter (R27.39): what the
    /// call ensures of the trace, and so of the lambda's captures, is stated over an
    /// existential trace, and Pulse's join keeps it of one arm only.
    /// </summary>
    private static bool PassesLambda(IrStmt s) =>
        Check.Statements(s).SelectMany(Check.Expressions).SelectMany(Check.Subexpressions)
            .Any(e => e is IrLambdaRef);

    /// <summary>
    /// R33.16. An arm that replaces the record of an `[Open]` receiver owning arrays: their
    /// `pts_to`s are reached through the record, and Pulse's join generalises the record
    /// afresh, leaving them reached through one it cannot relate to it.
    /// </summary>
    private bool WritesOpenRecord(IrIf i) =>
        (_constructsArrays || _slots.Values.Any(s => s is { Open: true } && s.OpenFields.Any(f => f.Type is IrArrayType))) &&
        ReceiverWrites(i).Record;

    /// <summary>
    /// R33.25. The constructor being emitted builds an object that owns arrays: like an
    /// `[Open]` receiver's, its record is what reaches them.
    /// </summary>
    private bool _constructsArrays;

    /// <summary>
    /// R27.54. An arm with a loop that breaks: the break flag is a mutable local, which Pulse
    /// allocates only where the post-condition is known, that is, in tail position.
    /// </summary>
    private static bool BreaksLoop(IrStmt s) =>
        Check.Statements(s).Any(t => t is IrWhile { Body: var b } && Check.Statements(b).Any(u => u is IrBreak));

    /// <summary>
    /// R27.38. `if (c) throw …;` with nothing else: Pulse's join of the arms keeps no pure
    /// fact of either, so what follows would not know `!c` (that a field read through is
    /// not null). The rest of the block is the `else` instead.
    /// </summary>
    private static bool ThrowGuard(IrIf i) =>
        i.Else is null or IrBlock { Statements.IsEmpty: true } &&
        (i.Then is IrThrow || i.Then is IrBlock { Statements: [.., IrThrow] });

    /// <summary>
    /// R27.16. Whether an arm allocates in, writes, or calls a method that writes a region:
    /// the heap after it is a fresh existential at the join, and what the arm proved about
    /// it would be lost.
    /// </summary>
    private bool MovesRegion(IrStmt s) =>
        classes is not null &&
        Check.Statements(s).Any(t =>
            t is IrAssign { Target: IrField { Receiver.Type: IrClassType k } } && IsRegionType(k) ||
            // R31.10. A write of a ring's entry pointer (the owner's `head`): the ring
            // lemma after the join needs which node it now is.
            t is IrAssign { Target: IrField { Type: IrClassType r } } &&
                classes.TryGetValue(r.Name, out var rd) && rd.IsCyclic ||
            Check.Expressions(t).SelectMany(Check.Subexpressions)
                .Any(e => e is IrAlloc ||
                          e is IrCall c && regionHeld is not null &&
                          regionHeld.TryGetValue(c.Callee, out var uses) && uses.Any(u => u.Mutates)));

    /// <summary>
    /// R25.10. Whether an arm calls a method that moves a receiver's model: the call leaves
    /// the receiver's post-state under an existential, and Pulse's join generalises it afresh,
    /// losing both what the call ensured about it and, in the other arm, that it is unchanged.
    /// </summary>
    private static bool MutatesClosedReceiver(IrStmt s) =>
        Passes.Check.Statements(s).SelectMany(Passes.Check.Expressions)
            .SelectMany(Passes.Check.Subexpressions).OfType<IrCall>()
            .Any(c => c.HasReceiver && c.MutatesReceiver && c.Args is [IrVar, ..]);

    /// <summary>
    /// R22.15, R22.12. A <c>return</c> or declaration whose value is <c>a &amp;&amp; b</c>,
    /// <c>a || b</c> or <c>c ? x : y</c> with an arm that calls a method on an open
    /// receiver is the <c>if</c> it abbreviates, so that R22.12 moves what follows into
    /// both arms rather than leave Pulse to join a reopened receiver with an untouched one.
    /// </summary>
    private IrStmt SplitShortCircuit(IrStmt s)
    {
        if (s is IrIf { Else: null, Cond: IrBinary { Op: BinOp.Or } or } guard && IsThrowBlock(guard.Then))
            return SplitGuard(guard, or);
        var value = s switch
        {
            IrReturn r => r.Value, IrLocalDecl d => d.Init,
            // R27.24. `x = c ? f() : g()` with arms that move a region is its `if` too.
            IrAssign { Target: IrVar, Value: IrConditional } asn => asn.Value,
            // R27.34. So is `v.f = c ? f() : g()`: reading the local `v` first or in each
            // arm is the same, since no call can assign it.
            IrAssign { Target: IrField { Receiver: IrVar }, Value: IrConditional } asn => asn.Value,
            _ => null,
        };
        (IrExpr Cond, IrExpr Then, IrExpr Else)? arms = value switch
        {
            IrBinary { Op: BinOp.And } b => (b.Left, b.Right, new IrLiteral(b.Loc, false) { Type = b.Type }),
            IrBinary { Op: BinOp.Or } b => (b.Left, new IrLiteral(b.Loc, true) { Type = b.Type }, b.Right),
            IrConditional c => (c.Cond, c.Then, c.Else),
            _ => null,
        };
        bool Splits(IrExpr arm) =>
            _objects.Length > 0 && CallsOpenReceiver(new IrExprStmt(arm.Loc, arm)) ||
            value is IrConditional && MovesRegion(new IrExprStmt(arm.Loc, arm)) ||
            // R32.14. Or calls a view's member that takes the view's record by reference.
            value is IrConditional && PassesRefSelf(arm);
        if (arms is not { } a || !Splits(a.Then) && !Splits(a.Else))
            return s;
        IrStmt With(IrExpr v) => s switch
        {
            IrReturn r => r with { Value = v },
            IrLocalDecl d => d with { Init = v },
            IrAssign asg => asg with { Value = v },
            _ => s,
        };
        return new IrIf(s.Loc, a.Cond, With(a.Then), With(a.Else));
    }

    /// <summary>
    /// R23.8. A guard <c>if (a || b) throw ...;</c> is <c>if (a) throw ...; else if (b) throw ...;</c>.
    /// Emitted as one <c>if</c>, a <c>b</c> that needs statements (an array's length, a
    /// field read) makes the condition a bound <c>bool</c> that Pulse knows nothing about,
    /// and what follows the guard cannot use its failure; split, each disjunct's failure
    /// is a path condition of its own. The throw is duplicated, which is harmless: it is
    /// reached on exactly the paths it was.
    /// </summary>
    private static IrIf SplitGuard(IrIf guard, IrBinary or)
    {
        IrIf Part(IrExpr cond) => cond is IrBinary { Op: BinOp.Or } inner
            ? SplitGuard(guard with { Cond = inner }, inner)
            : guard with { Cond = cond };
        var right = Part(or.Right);
        var left = Part(or.Left);
        return Attach(left, right);

        static IrIf Attach(IrIf chain, IrStmt tail) => chain.Else is IrIf next
            ? chain with { Else = Attach(next, tail) }
            : chain with { Else = tail };
    }

    private static bool IsThrowBlock(IrStmt s) => s switch
    {
        IrThrow => true,
        IrExprStmt { Expr: IrCall { DoesNotReturn: true } } => true,
        IrGhostStmt { Kind: GhostKind.Unreachable } => true,
        IrBlock { Statements: [.., var last] } => IsThrowBlock(last),
        _ => false,
    };

    /// <summary>R22.15. Whether an arm calls a method on an open receiver, which reopens it afresh.</summary>
    private bool CallsOpenReceiver(IrStmt s) =>
        Passes.Check.Statements(s).SelectMany(Passes.Check.Expressions)
            .SelectMany(Passes.Check.Subexpressions).OfType<IrCall>()
            .Any(c => c.HasReceiver && c.Args is [IrVar r, ..] &&
                      _objects.Any(o => o.Name == r.Name && o.ViewBase is null));

    private static bool CopiesArray(IrStmt s) => s switch
    {
        IrArrayOp => true,
        IrBlock b => b.Statements.Any(CopiesArray),
        IrIf i => CopiesArray(i.Then) || i.Else is { } e && CopiesArray(e),
        _ => false,
    };

    /// <summary>R22.12. Whether a statement assigns an array-typed field of an object.</summary>
    private bool ReplacesArrayField(IrStmt s) => s switch
    {
        IrAssign { Target: IrField { Receiver: IrVar rv } f } =>
            _slots.TryGetValue(rv.Name, out var o) && o.Type is IrClassType k &&
            FieldType(k, f.Field) is IrArrayType,
        IrBlock b => b.Statements.Any(ReplacesArrayField),
        IrIf i => ReplacesArrayField(i.Then) || i.Else is { } e && ReplacesArrayField(e),
        _ => false,
    };

    private static bool ContainsReturn(IrStmt s) => s switch
    {
        IrReturn => true,
        IrBlock b => b.Statements.Any(ContainsReturn),
        IrIf i => ContainsReturn(i.Then) || i.Else is { } e && ContainsReturn(e),
        IrTry t => ContainsReturn(t.Body) || t.Catches.Any(c => ContainsReturn(c.Body)),
        _ => false,
    };

    /// <summary>
    /// R22.9. The fields assigned on every path through <paramref name="statements"/> that
    /// completes normally; <c>null</c> when no path does.
    /// </summary>
    private static HashSet<string>? Assigned(IEnumerable<IrStmt> statements)
    {
        var acc = new HashSet<string>();
        foreach (var s in statements)
        {
            var one = Assigned(s);
            if (one is null) return null;
            acc.UnionWith(one);
        }
        return acc;
    }

    private static HashSet<string>? Assigned(IrStmt s)
    {
        switch (s)
        {
            case IrAssign { Target: IrField { Receiver: IrVar { Name: Names.This } } f }:
                return [f.Field];
            case IrBlock b:
                return Assigned(b.Statements);
            case IrThrow:
                return null;
            case IrIf { Else: { } e } i:
            {
                var t = Assigned(i.Then);
                var f = Assigned(e);
                if (t is null) return f;
                if (f is null) return t;
                t.IntersectWith(f);
                return t;
            }
            default:
                return [];
        }
    }

    /// <summary>Resolves <c>$&amp;(x)</c> to the Pulse name holding <c>x</c>.</summary>
    private string? Binder(string name) =>
        _slots.TryGetValue(name, out var slot) ? slot.Binder : null;

    private bool IsObjectBinder(string text) =>
        _objectLocals.Any(l => l.Binder == text) || _objects.Any(o => o.Binder == text) ||
        // R10.6b. A method may hand back an object it was *given*, which is what a
        // traversal that returns one of its arguments does. The binder rule is the same:
        // re-binding it would leave the invariant in the context under the old name.
        _slots.Values.Any(s => s.Kind is SlotKind.Object && s.Binder == text) ||
        // R10.6c. A call's result is held under the binder the call bound it to.
        _objectResults.Contains(text);

    /// <summary>R10.6c. Binders that a call produced an object under.</summary>
    private readonly HashSet<string> _objectResults = new(StringComparer.Ordinal);

    private bool IsRegionType(IrType? t) =>
        t is IrClassType k && classes is not null && classes.TryGetValue(k.Name, out var d) && d.IsRegion;

    /// <summary>R27.4. The region classes a class owns a region of, one per class.</summary>
    private IEnumerable<IrClassType> RegionsOf(IrClass decl) =>
        decl.Fields.Select(f => f.Type).Where(IsRegionType).Cast<IrClassType>()
            .GroupBy(k => k.Name).Select(g => g.First());

    /// <summary>R27.5. Whether a statement writes a field of an object of a region class.</summary>
    // R27.50. With skipReadOnly, a call to a read-only method does not count: it leaves
    // every region it is handed as it found it. This only decides whether a loop states
    // an unchanged model, which F* then checks, so erring costs a proof, never soundness.
    private bool WritesRegion(IrStmt body, string regionClass, bool skipReadOnly = false) =>
        Check.Statements(body).Any(s =>
            s is IrAssign { Target: IrField { Receiver.Type: IrClassType k } } && k.Name == regionClass ||
            Check.Expressions(s).SelectMany(Check.Subexpressions)
                .Any(e => e is IrAlloc al && al.Class == regionClass ||
                          // R27.16. A call writes the region exactly when its callee does; a
                          // callee that holds no region of its own is assumed to.
                          // R27.39. A callback is handed the region at a fixed heap and gives it back.
                          e is IrCall c && c.Kind != CalleeKind.Callback &&
                          !(skipReadOnly && readOnlyMethods?.Contains(c.Callee) == true) && (regionHeld is null || !regionHeld.TryGetValue(c.Callee, out var uses) ||
                                            uses.Any(u => u.Region.Name == regionClass && u.Mutates))));

    private static string Inv(IrClassType c) =>
        $"{Names.ClassModule(c.Name)}.{Names.ClassInv(c.Name)}";

    /// <summary>
    /// R5.12. The receiver's resources <em>as R4.10 left them</em>: a <c>Box</c> holding the
    /// representation record, and one <c>A.pts_to</c> for every array the class owns.
    ///
    /// A loop in the unfolded window has to carry exactly these, because they are what its
    /// body touches. All of them are existential: R3.6 writes a whole record, so the record
    /// binder changes on any field write, and an element write changes an array's contents.
    /// The array *references* survive that, because a record update is definitionally equal
    /// to the original in every field it does not mention.
    ///
    /// Each field is bound in the invariant's scope under <c>this.f</c>, so a user writing
    /// <c>Pal.Invariant("i &lt;= top")</c> inside the method means the representation's
    /// <c>top</c> — the same reading R3.9b gives a class-level <c>[Invariant]</c>, and for
    /// the same reason. An array field denotes its contents (R3.10a).
    ///
    /// What is <em>not</em> carried is the class's own <c>[Invariant]</c> clauses. They may
    /// be transiently false — that is what the window is for — so the emitter states only
    /// what it owns: the resources, and the length bound that comes from C#'s array type
    /// rather than from anything the user wrote. Every other proposition the loop needs is
    /// the user's to state, which is R5.8's rule unchanged.
    /// </summary>
    private static bool CallsOnReceiver(IrStmt body) =>
        Passes.Check.Statements(body)
            .SelectMany(Passes.Check.Expressions)
            .SelectMany(Passes.Check.Subexpressions)
            .Any(e => e is IrCall { HasReceiver: true, Args: [IrVar { Name: Names.This }, ..] });

    private void Representation(
        Slot receiver,
        IrStmt body,
        SpecScope scope,
        SpecScope measureScope,
        ImmutableArray<string>.Builder resources,
        ImmutableArray<string>.Builder existentials,
        ImmutableArray<string>.Builder pure,
        List<(string Name, string Resource)> fixedNames)
    {
        var klass = (IrClassType)receiver.Type;
        var (writesRecord, written) = ReceiverWrites(body);
        // R27.50. Entered with the receiver unchanged since the method began, and leaving it
        // alone: the receiver is still at its model on entry.
        var unchanged = receiver.PostModel == receiver.PreModel ||
                        _pristineLoops.Count > 0 && _pristineLoops.Peek();
        // R27.38. A call that closes the receiver around itself (R22.15's self-call, or a
        // raising callee's bracket) reopens it at a fresh record: the record cannot be
        // named before the loop. A read-only receiver says instead that the record is still
        // one its model abstracts, which is what folding it back at that model needs.
        var reopened = Reopens(receiver, body);
        writesRecord |= reopened;

        var record = FreshValue("rep");
        var recordResource = $"B.pts_to {receiver.Binder} {receiver.PermArg}{record}";
        resources.Add(recordResource);
        if (writesRecord) existentials.Add(record);
        else fixedNames.Add((record, recordResource));
        var heapsOfRecord = new List<string>();
        // R33.20. A record the loop writes, across a call of an `[Open]` method on it, keeps
        // the fields neither the loop nor that callee assigns. A loop without such a call
        // states what it keeps itself (R5.8), and an unneeded frame only burdens its proofs.
        if (writesRecord && classes is not null && classes.TryGetValue(klass.Name, out var framed) &&
            CallsOnReceiver(body) &&
            MethodPlan.OpenAssigned(body, methods, []) is { } loopAssigned &&
            framed.Fields.Where(f => !loopAssigned.Contains(f.Name)).ToList() is { Count: > 0 } kept)
        {
            var before = FreshValue("rep");
            Line($"with {before}. assert (B.pts_to {receiver.Binder} {receiver.PermArg}{before});");
            foreach (var f in kept)
            {
                var proj = Names.ClassProjection(klass.Name, f.Name);
                pure.Add($"{record}.{proj} == {before}.{proj}");
            }
        }

        // F3. A `decreases` measure may name a field only when the loop leaves it alone,
        // because then the record has a name from before the loop. A loop that writes a
        // field quantifies the record existentially, and F3 forbids a measure that mentions
        // the invariant's existentials — so the binding is simply absent, and naming the
        // field in a measure is refused where it is written.
        void BindBoth(string key, Term term, bool stable)
        {
            scope.Bind(key, term);
            if (stable) measureScope.Bind(key, term);
        }

        if (classes is null || !classes.TryGetValue(klass.Name, out var decl)) return;

        // R27.4. The region the receiver owns is carried beside its record. A loop that
        // writes no region object leaves the heap where it was, so it is named once.
        foreach (var k in RegionsOf(decl))
        {
            var heap = FreshValue(Frontend.Region.HeapBinder(k.Name));
            var regionResource = PulseEmitter.RegionAt(k,
                receiver.Fraction ?? "1.0R", heap);
            resources.Add(regionResource);
            var still = !WritesRegion(body, k.Name) && !(reopened && receiver.Heaps.IsEmpty);
            if (still) fixedNames.Add((heap, regionResource));
            else existentials.Add(heap);
            heapsOfRecord.Add(heap);
            BindBoth(Frontend.Region.HeapName(k.Name), new Term(heap, TermKind.Other), still);
            // R27.25. A loop that moves the heap measures it by a ghost read, which Pulse
            // evaluates against the invariant as it does `!r`.
            if (!still)
                measureScope.Bind(Frontend.Region.HeapName(k.Name), new Term(
                    $"({Frontend.Region.Module}.current #({PulseEmitter.RegionRaw(k)}) ())", TermKind.Other));
        }

        if (reopened && unchanged && receiver.ViewBase is null &&
            decl.Fields.All(f => IsRegionType(f.Type) || f.Type is not (IrArrayType or IrClassType)))
        {
            var selfArg = PulseEmitter.InvariantNamesThis(decl) ? receiver.Binder + " " : "";
            pure.Add($"{Names.ClassModule(klass.Name)}.{Names.ClassAbs(klass.Name)} {selfArg}{record} " +
                     $"{string.Concat(heapsOfRecord.Select(h => h + " "))}{receiver.PreModel}");
            // R27.50. The receiver is at its model throughout, so a measure reads it there.
            if (receiver.PreModel is { } pm)
                measureScope.Bind(receiver.Name, new Term($"(reveal {pm})", TermKind.Math, receiver.Type));
        }
        // R27.52. A loop that changes the receiver through calls on it, and reads its fields
        // in between, holds it open at a record its invariant abstracts at some model; the
        // invariant names the receiver's specs at that model.
        else if (reopened && !unchanged && receiver.ViewBase is null && heapsOfRecord.Count > 0 &&
                 decl.Invariants.IsEmpty &&
                 decl.Fields.All(f => IsRegionType(f.Type) || f.Type is not (IrArrayType or IrClassType)))
        {
            var m = FreshValue(klass.Name);
            var args = $"{(PulseEmitter.InvariantNamesThis(decl) ? receiver.Binder + " " : "")}{record}{string.Concat(heapsOfRecord.Select(h => " " + h))}";
            existentials.Add($"({m}: {PulseEmitter.SubModelType(klass)})");
            resources.Add($"pure ({m} == {Names.ClassModule(klass.Name)}.{Names.ClassAbsModel(klass.Name)} {args})");
            pure.Add($"{Names.ClassModule(klass.Name)}.{Names.ClassAbsRep(klass.Name)} {args}");
            scope.Bind(receiver.Name, new Term(m, TermKind.Math, receiver.Type));
            _receiverRenamed = true;
        }

        foreach (var f in decl.Fields)
        {
            var projection = $"{record}.{Names.ClassProjection(klass.Name, f.Name)}";
            if (IsRegionType(f.Type))
            {
                BindBoth($"{Names.This}.{f.Name}",
                    new Term(projection, TermKind.Other, f.Type), !writesRecord);
                // R27.25. A written record is read in a measure as `!this` is.
                if (writesRecord)
                    measureScope.Bind($"{Names.This}.{f.Name}", new Term(
                        $"(B.op_Bang {receiver.Binder}).{Names.ClassProjection(klass.Name, f.Name)}",
                        TermKind.Other, f.Type));
                continue;
            }
            if (f.Type is IrClassType)
            {
                // R3.10b. A sub-object is carried by its invariant, at its model, exactly
                // as an array is carried by its `A.pts_to` at its contents. Inside the
                // loop it is still *folded*, so the body may call its methods.
                var sub = FreshValue(Names.SubModel(f.Name));
                var subResource = PulseEmitter.SubInvAt(f.Type, projection, receiver.PermArg, sub);
                resources.Add(subResource);
                var settled = !writesRecord && !written.Contains(f.Name);
                if (settled) fixedNames.Add((sub, subResource));
                else existentials.Add(sub);
                BindBoth($"{Names.This}.{f.Name}", new Term(sub, TermKind.Math, f.Type), settled);
                continue;
            }
            // R33.27. An array a live span borrowed is held by the span, which the loop
            // carries as a local; the borrow's receipt is framed around it.
            if (f.Type is IrArrayType && receiver.Name == Names.This &&
                _slots.Values.Any(s => s is { Kind: SlotKind.Span } && s.BorrowedField == f.Name))
            {
                scope.Bind(SpecEmitter.ArrayRefKey($"{Names.This}.{f.Name}"),
                    new Term(projection, TermKind.Other, f.Type));
                continue;
            }
            if (f.Type is IrArrayType)
            {
                var contents = FreshValue(Names.Contents(f.Name));
                var resource = $"{PulseEmitter.ArrayPts(f)} {projection} {receiver.PermArg}{contents}";
                resources.Add(resource);
                var stable = !writesRecord && !written.Contains(f.Name) && !written.Contains(AnyArray);
                if (stable)
                {
                    fixedNames.Add((contents, resource));
                }
                else
                {
                    existentials.Add(contents);

                    // No C# operation changes the length of an array it has been handed, so
                    // a loop that only writes *elements* leaves the length where it was. The
                    // invariant has to say so all the same, because the contents are
                    // existentially quantified and an existential remembers nothing. Naming
                    // the length before the loop is what gives it something to be equal to.
                    // Like the bound below, this conjunct comes from C#'s array type rather
                    // than from anything the user wrote, which is why the emitter states it.
                    if (!writesRecord)
                    {
                        var entry = FreshValue(Names.Contents(f.Name));
                        fixedNames.Add((entry, resource.Replace(contents, entry)));
                        pure.Add($"Seq.length {contents} == Seq.length {entry}");
                        // A measure may still name the array's length (R24.7's alias of a
                        // field makes `a.Length` this field's): the length before the loop.
                        measureScope.Bind($"{Names.This}.{f.Name}", new Term(entry, TermKind.Seq, f.Type));
                    }
                }
                pure.Add($"Seq.length {contents} <= 2147483647");
                BindBoth($"{Names.This}.{f.Name}", new Term(contents, TermKind.Seq, f.Type), stable);
                BindBoth(SpecEmitter.ArrayRefKey($"{Names.This}.{f.Name}"),
                    new Term(projection, TermKind.Other, f.Type), !writesRecord);
            }
            else
            {
                BindBoth($"{Names.This}.{f.Name}",
                    new Term(projection, MethodPlan.KindOf(f.Type), f.Type), !writesRecord);
                if (writesRecord && RegionsOf(decl).Any())
                    measureScope.Bind($"{Names.This}.{f.Name}", new Term(
                        $"(B.op_Bang {receiver.Binder}).{Names.ClassProjection(klass.Name, f.Name)}",
                        MethodPlan.KindOf(f.Type), f.Type));
            }
        }
    }

    /// <summary>
    /// R27.38. Whether the loop body closes <paramref name="receiver"/> around a call and
    /// reopens it: a call on it (R22.15), or a raising call while it is held read-only.
    /// </summary>
    private bool Reopens(Slot receiver, IrStmt body) =>
        Check.Statements(body).SelectMany(Check.Expressions).SelectMany(Check.Subexpressions)
            .OfType<IrCall>()
            .Any(c => c.HasReceiver && c.Args is [IrVar { Name: var n }, ..] && n == receiver.Name &&
                      receiver.ViewBase is null && openMethods?.Contains(c.Callee) != true ||
                      raising?.Contains(c.Callee) == true && !c.DoesNotReturn && receiver.Fraction is not null &&
                      receiver.ViewBase is null && receiver.PostModel == receiver.PreModel);

    /// <summary>
    /// What a loop body does to the receiver, which decides which halves of R5.12's
    /// representation have to be existentially quantified. A field assignment replaces the
    /// whole record (R3.6), so it unsettles everything; an element write unsettles only
    /// that array's contents; handing an owned array to a callee is treated as an element
    /// write, because the callee may write it.
    /// </summary>
    private const string AnyArray = "*";

    private bool IsArrayCell(string name) =>
        _slots.TryGetValue(name, out var s) && s.Kind == SlotKind.Cell && s.Type is IrArrayType;

    private (bool Record, HashSet<string> Arrays) ReceiverWrites(IrStmt body)
    {
        var arrays = new HashSet<string>(StringComparer.Ordinal);
        var record = false;

        foreach (var stmt in Check.Statements(body))
        {
            if (stmt is IrAssign a)
            {
                switch (Normalize.ElementTarget(a.Target))
                {
                    case IrField { Receiver: IrVar { Name: Names.This }, Field: var f }:
                        record = true;
                        arrays.Add(f);
                        break;
                    case IrElement { Array: IrField { Receiver: IrVar { Name: Names.This }, Field: var g } }:
                        arrays.Add(g);
                        break;
                    // R26.10. An element write through a local holding an array may be a
                    // write through an alias of any of the receiver's arrays.
                    case IrElement { Array: IrVar v } when IsArrayCell(v.Name):
                        arrays.Add(AnyArray);
                        break;
                }
            }

            foreach (var node in Check.Expressions(stmt).SelectMany(Check.Subexpressions))
            {
                if (node is not IrCall call) continue;
                // R27.23. An `[Open]` callee is handed the receiver's record and may write it.
                // R33.16. And the arrays it owns.
                if (call.HasReceiver && openMethods?.Contains(call.Callee) == true &&
                    call.Args is [IrVar { Name: Names.This }, ..])
                {
                    record = true;
                    arrays.Add(AnyArray);
                }
                for (var i = 0; i < call.Args.Length; i++)
                {
                    if (call.Args[i] is IrVar av && IsArrayCell(av.Name)) arrays.Add(AnyArray);
                    if (call.Args[i] is not IrField { Receiver: IrVar { Name: Names.This }, Field: var h })
                        continue;

                    // The one case a field survives being handed to a callee: it is the
                    // receiver of an instance method R4.11 has already found read-only, so
                    // the callee's own postcondition says its model did not move. Anything
                    // else — an array passed as data, a mutating method, a static callee —
                    // is assumed to write it, which is the strict direction and costs only
                    // an existential.
                    if (i == 0 && call.HasReceiver && !call.MutatesReceiver) continue;
                    arrays.Add(h);
                }
            }
        }

        return (record, arrays);
    }


    /// <summary>
    /// R9.18. The base classes between <paramref name="derived"/> and
    /// <paramref name="ancestor"/>, nearest first and <paramref name="ancestor"/> last, or
    /// <c>null</c> if it is not one. The chain is what makes a conversion across several
    /// levels the composition of the one-edge rule rather than a rule of its own.
    /// </summary>
    private ImmutableArray<string>? Ancestors(string? derived, string? ancestor)
    {
        if (derived is null || ancestor is null || classes is null) return null;
        var chain = ImmutableArray.CreateBuilder<string>();
        for (var at = derived; classes.TryGetValue(at, out var c) && c.BaseClass is { } up;)
        {
            chain.Add(up);
            if (up == ancestor) return chain.ToImmutable();
            at = up;
        }
        return null;
    }

    /// <summary>
    /// R9.15. The upcast, wherever C# inserts a reference conversion: the object is held
    /// at its own class, its invariant is read at the base's model through R9.14's view,
    /// and the conversion returns the reference the base-typed context is given.
    ///
    /// <para>It is written once and used at every conversion site — a local declaration,
    /// an argument, a <c>return</c> — because that is what the frontend now records
    /// (R9.15) and what makes those three positions the same rule rather than three.</para>
    ///
    /// <para>The conversion <b>consumes</b> the derived reference. C# would leave both
    /// names usable, but the derived object's invariant *becomes* the base's, so the old
    /// name owns nothing afterwards; it is marked cast, and PALCS0548 says so at the next
    /// use rather than letting Pulse fail on a resource that is no longer there.</para>
    /// </summary>
    private Slot? Upcast(IrLoc loc, IrExpr operand, IrClassType target, string name, string binder)
    {
        var derived = (operand.Type as IrClassType)?.Name;

        // R9.18. C# writes one conversion where the hierarchy has several edges, and the
        // translation writes one per edge: a conversion to a base is the composition of the
        // conversions along the chain, in order. That is the one-edge rule applied
        // repeatedly and nothing else — the intermediate references are the same ones the
        // reader would get by writing the conversions out.
        if (Ancestors(derived, target.Name) is not { } chain)
        {
            diagnostics.Unsupported(loc,
                $"Converting a `{derived}` to a `{target.Name}`",
                "R9.15 converts a reference to a base class, and `" + target.Name +
                "` is not one of `" + derived + "`'s.");
            return null;
        }

        string impl;
        string? from = null;
        // R9.15e. A chain may be walked in pieces — `Rect r = new Rect__impl(6);` then
        // `AtMiddle(r)` is two conversions over one value — so the name the earlier piece
        // bound the model under is picked up from the slot, exactly as the index is.
        string? held = null;
        if (operand is IrVar v && Lookup(v.Name) is { Kind: SlotKind.Object } src)
        {
            // R9.15c. The conversion *moves* the invariant onto the base reference, so a
            // method that converts one of its own parameters no longer owns what R4.10's
            // epilogue owes back — unless it takes it back with a cast down (R9.16).
            // Which of the two it is, is a separation-logic question about what is owned
            // where, and Pulse is the one that answers it: the epilogue simply cannot be
            // proved. This was briefly PALCS0549 here; see
            // `test/pulse_refusals/cases/UpcastParameter.cs` for why it is not any more.

            impl = src.Binder;
            from = src.Index;
            held = src.PreModel;
            _slots[v.Name] = src with { Kind = SlotKind.Value, Index = null, Cast = target.Name };
            _objectLocals.RemoveAll(l => l.Binder == src.Binder);
        }
        else if (operand is IrCall { Kind: CalleeKind.Method } call) { impl = Fresh(); Call(call, impl); }
        else { impl = Fresh(); Line($"let {impl} = {Expr(operand)};"); }

        return UpcastChain(derived!, impl, from, held, target, name, binder);
    }

    /// <summary>
    /// R9.18. One edge per class boundary, in order. Split out of <see cref="Upcast"/> so
    /// that R9.21a's constructor, which has a binder rather than an expression to convert,
    /// walks the very same chain.
    /// </summary>
    private Slot? UpcastChain(
        string derived, string impl, string? from, string? held,
        IrClassType target, string name, string binder)
    {
        if (Ancestors(derived, target.Name) is not { } chain) return null;
        Slot? slot = null;
        var current = derived;
        for (var i = 0; i < chain.Length; i++)
        {
            var last = i == chain.Length - 1;
            var step = last ? binder : Fresh();
            slot = UpcastStep(current, impl, from, new IrClassType(chain[i]), last ? name : step, step, held);
            impl = step;
            from = slot.Index;
            held = slot.PreModel;
            current = chain[i];
        }
        return slot;
    }

    /// <summary>R9.15, one edge: from <paramref name="derived"/> to its immediate base.</summary>
    /// <param name="held">
    /// R9.15e. The name the previous edge bound this value's model under, when there was
    /// one. A chain of edges has to carry it: each edge names the model it produces, and
    /// the next edge forgets *that* name rather than re-deriving the expression.
    /// </param>
    private Slot UpcastStep(
        string derived, string impl, string? from, IrClassType target, string name, string binder,
        string? held = null)
    {
        var mod = Names.ClassModule(derived);

        // R9.18. An *abstract* class's reference already is a reference: there is no
        // representation to view and no vtable to build, and the conversion changes the
        // invariant and not the value. So the whole of it is the cast R9.18 emits beside
        // the class, and the only choice here is whether the object record is known.
        if (classes is not null && classes[derived].IsAbstract)
        {
            // R9.15e. `Rebase` rewrites `forget` applied to a *name*, so when nothing has
            // named this value's model yet — it came from a call, not from a slot — the
            // name is asked for here. Naming a model the invariant already existentially
            // quantifies is R9.6's `with`, not a proof step.
            if (held is null)
            {
                held = FreshValue(name);
                Line($"with {held}. assert ({mod}.{Names.ClassInv(derived)} {impl} {held});");
            }
            if (from is null)
            {
                Line($"let {binder} = {mod}.{Names.UpcastTo(derived, target.Name)} {impl};");
                return new Slot(name, target, SlotKind.Object, binder)
                {
                    PreModel = Rebase(mod, derived, target, held),
                };
            }
            Line($"let {binder} = {mod}.{Names.UpcastToAt(derived, target.Name)} {impl} {from};");
            return new Slot(name, target, SlotKind.Object, binder)
            {
                Index = $"(hide ({mod}.{Names.ClassView(derived)} (reveal {from})))",
                Sub = from,
                PreModel = Rebase(mod, derived, target, held),
            };
        }

        // The view is folded at the forgetting of whatever model the value is held at,
        // which is the same expression R9.6 read off the `[Model]` override. Only the
        // prover can name that model, which is what the `with` is for: it is the naming
        // R9.6 needs, not a proof step.
        var own = FreshValue(name);
        Line($"with {own}. assert ({mod}.{Names.ClassInv(derived)} {impl} {own});");

        // R9.15e. The forgotten model is bound to a name *of the base's model type* before
        // the fold, rather than left as an application of `forget` inside it. Every class
        // has its own `__model` refinement (R9.5), so a term only known at the derived
        // class's refinement is one the base's spec functions cannot be unfolded on. The
        // reference this cast produces is owned at whatever names its model, and that name
        // is what a later caller's implicit is instantiated with; binding it here is what
        // keeps the base's own vocabulary applicable to it afterwards.
        var basis = FreshValue(target.Name);
        Line($"let {basis} : erased ({Names.ClassModule(target.Name)}.{Names.ClassModel(target.Name)}) = " +
             $"hide ({mod}.{Names.ClassForget(derived)} {own});");
        Line($"fold ({mod}.{Names.ClassAsBase(derived, target.Name)} {impl} (reveal {basis}));");
        Line($"let {binder} = {Names.VtblModule(derived)}." +
             $"{Names.UpcastToAt(derived, target.Name)} {impl};");

        // R9.16. The conversion keeps the index, so the object record this reference
        // stands for stays known and a later cast back is provable. Where the plain
        // invariant is wanted instead, `Forget` drops it — one ghost step, at the point
        // that wants it, and nothing recovers it afterwards.
        var index = $"(hide ({Names.VtblModule(derived)}.{Names.ClassObjOf(derived)} {impl}))";
        return new Slot(name, target, SlotKind.Object, binder) { Index = index, PreModel = basis };
    }

    /// <summary>
    /// R9.15e, for an edge out of an *abstract* class. There is nothing to fold here — the
    /// cast is one generated ghost function (R9.18) whose <c>ensures</c> is written at
    /// <c>class_D__forget m</c> — so the base model cannot be named before it is produced.
    /// It is named after, and the resource moved onto the name.
    ///
    /// <para>The move is what matters. Where the forgetting is the identity, Pulse reduces
    /// <c>class_D__forget m</c> back to <c>m</c> and instantiates a later caller's implicit
    /// with that, which is a term at <em>D</em>'s model refinement and not the base's; the
    /// <c>rewrite each</c> is what stops it, because a binder has no further reduct. It
    /// mentions neither the index nor the permission, so it is the same one step whatever
    /// the reference is held at.</para>
    ///
    /// <para>Returns null only when no name was available at all.</para>
    /// </summary>
    private string? Rebase(string mod, string derived, IrClassType target, string? held)
    {
        if (held is null) return null;
        var basis = FreshValue(target.Name);
        var forgotten = $"({mod}.{Names.ClassForget(derived)} (reveal {held}))";
        Line($"let {basis} : erased ({Names.ClassModule(target.Name)}.{Names.ClassModel(target.Name)}) = " +
             $"hide {forgotten};");
        Line($"rewrite each {forgotten} as (reveal {basis});");
        return basis;
    }

    /// <summary>
    /// R9.15, in expression position. The conversion is a statement — it moves a resource
    /// and binds a new name — so the value it produces is an anonymous object local: owned
    /// here, dropped where the block closes unless it is returned.
    /// </summary>
    private string UpcastExpr(IrConvert cv, IrClassType target)
    {
        var binder = Fresh();
        if (Upcast(cv.Loc, cv.Operand, target, binder, binder) is not { } slot) return "()";
        _objectLocals.Add(slot);
        return binder;
    }

    /// <summary>
    /// R9.16. <c>D x = (D) b;</c>. The cast is justified by <paramref name="source"/>'s
    /// index — the object record it is known to stand for — which is exactly the knowledge
    /// C# would test for at runtime, and which R9.15a's conversion kept. A base reference
    /// with no index is one whose dynamic type the translation does not know, and the cast
    /// is refused rather than emitted for Pulse to fail on.
    ///
    /// <para>The result is handed back at the base's model, through R9.14's view; opening
    /// that view immediately turns it into an ordinary M2 object local, and leaves in
    /// context the equation relating the two models — which is what lets the caller keep
    /// reasoning about the value it cast.</para>
    /// </summary>
    private void Downcast(IrLocalDecl d, IrClassType target, IrVar source, string binder)
    {
        if (Lookup(source.Name) is not { Kind: SlotKind.Object, Type: IrClassType from } obj ||
            Ancestors(target.Name, from.Name) is not { } up)
        {
            diagnostics.Unsupported(d.Loc, $"Casting a `{Lookup(source.Name)?.Type}` to `{target.Name}`",
                "R9.16 casts a reference to a subclass, and `" + target.Name +
                "` is not one of `" + Lookup(source.Name)?.Type + "`'s.");
            return;
        }

        // R9.18, mirroring R9.15's chain: a cast across several levels is the composition
        // of the one-level casts, applied from the base downwards. Each recovers one
        // record, and the knowledge each gives back is the knowledge the matching upcast
        // kept — which is why the last one is the first that can name the leaf's model.
        for (var i = up.Length - 2; i >= 0; i--)
        {
            var step = Fresh();
            if (DowncastStep(d.Loc, obj, new IrClassType(up[i]), step, step) is not { } mid) return;
            _slots[step] = mid;
            _objectLocals.Add(mid);
            obj = mid;
        }

        if (DowncastStep(d.Loc, obj, target, d.Name, binder) is not { } local) return;
        _slots[d.Name] = local;
        _objectLocals.Add(local);
    }

    /// <summary>R9.16, one edge: from <paramref name="obj"/>'s class to its immediate subclass.</summary>
    private Slot? DowncastStep(IrLoc loc, Slot obj, IrClassType target, string name, string binder)
    {
        var source = obj;
        var from = (IrClassType)obj.Type;

        // R9.18. Casting down to an intermediate class needs the record *it* was upcast
        // from, not the one the base reference is indexed by: they are different records,
        // related by the view, and only the first says which quadrilateral this is.
        if (classes is not null && classes[target.Name].IsAbstract ? obj.Sub is null : obj.Index is null)
        {
            diagnostics.Error("PALCS0547", loc,
                $"`{source.Name}` is not known to be a `{target.Name}`, so this cast might " +
                "throw. R9.16 proves only the casts whose runtime test is redundant: the " +
                $"reference must have been converted from a `{target.Name}` in this method.");
            return null;
        }

        // The model the reference is held at has to be named before the cast: the view the
        // cast hands back is indexed by it, and only the prover knows what it is.
        var pre = FreshValue(source.Name);
        Line($"with {pre}. assert ({obj.Resource(pre)});");

        var own = FreshValue(name);
        var mod = Names.ClassModule(target.Name);
        string? sub = null;

        // R9.18. Casting down to an *intermediate* class. The cast lives beside that class
        // rather than in a vtable module, because there is no vtable: what is recovered is
        // the object record the reference was upcast from, which the upcast kept, and the
        // model comes back existentially because forgetting is not injective.
        if (classes is not null && classes[target.Name].IsAbstract)
        {
            sub = obj.Sub;
            Line($"let {binder} = {mod}.{Names.DowncastFrom(target.Name, from.Name)} {obj.Binder};");
            Line($"with {own}. assert ({mod}.{Names.ClassInvAt(target.Name)} " +
                 $"{binder} {sub} {obj.Fraction ?? "1.0R"} {own});");
        }
        else
        {
            Line($"let {binder} = {Names.VtblModule(target.Name)}." +
                 $"{Names.DowncastFrom(target.Name, from.Name)} {obj.Binder};");
            Line($"unfold ({mod}.{Names.ClassAsBase(target.Name, from.Name)} " +
                 $"{binder} {obj.PermArg}{pre});");
            Line($"with {own}. assert ({mod}.{Names.ClassInv(target.Name)} {binder} {obj.PermArg}{own});");
        }

        // The base reference owns nothing now: its invariant *became* the derived one.
        // C# would let it be read again, so saying so is the emitter's job (PALCS0548).
        _slots[source.Name] = obj with { Kind = SlotKind.Value, Index = null, Cast = target.Name };
        _objectLocals.RemoveAll(s => s.Binder == obj.Binder);

        return new Slot(name, target, SlotKind.Object, binder)
        { Fraction = obj.Fraction, PreModel = own, PostModel = own, Index = sub };
    }

    /// <summary>
    /// R9.16. Drops a slot's index, where what wants the resource wants the plain
    /// invariant: an argument at a base-typed parameter, or a returned reference. One
    /// ghost step, and irreversible — which is why it is emitted at the point that needs
    /// it and not at the conversion.
    /// </summary>
    private void Forget(Slot obj)
    {
        // The model is left implicit on purpose. Naming it with a `with` first would bind
        // it to an opaque witness, and everything the context knew about the model — that
        // it is *this* leaf's forgetting of *that* constructor's post-state — would be cut
        // at exactly the point a caller still needs it (F34's lesson, one level up).
        var klass = (IrClassType)obj.Type;
        Line($"{Names.ClassModule(klass.Name)}.{Names.ClassForgetImpl(klass.Name)} " +
             $"{obj.Binder} {obj.Index};");
        var plain = obj with { Index = null };
        _slots[obj.Name] = plain;
        for (var i = 0; i < _objectLocals.Count; i++)
            if (_objectLocals[i].Binder == obj.Binder) _objectLocals[i] = plain;
    }

    /// <summary>
    /// R4.10c. Whether a body names a field of its receiver, which is the only reason to
    /// open the fold/unfold bracket.
    /// </summary>
    /// <remarks>
    /// A constructor is excluded: it builds the representation rather than reading one,
    /// and <see cref="Construct"/> handles it before this point is reached.
    /// </remarks>
    /// <summary>
    /// R27.50. For each pair of objects of a class the body compares by reference, both held
    /// whole (not read-only, not opened, not through a view): <c>class_C__distinct</c>, at the
    /// heap-indexed form when the class owns regions.
    /// </summary>
    private void EmitDistinct(IrMethod method, MethodPlan plan)
    {
        foreach (var name in PulseEmitter.ComparedClasses(method, classes!))
        {
            if (!classes!.TryGetValue(name, out var decl) || decl.BaseClass is not null) continue;
            var regions = RegionsOf(decl).Any();
            var held = plan.SlotOrder.Select(n => plan.Slots[n])
                .Where(s => s is { Kind: SlotKind.Object, Open: false, ViewBase: null, Index: null, Fraction: null } &&
                            s.Type is IrClassType { Nullable: false } t && t.Name == name &&
                            (regions || s.Heaps.IsEmpty))
                .ToList();
            var module = Names.ClassModule(name);
            for (var i = 0; i < held.Count; i++)
            for (var j = i + 1; j < held.Count; j++)
            {
                var (x, y) = (held[i], held[j]);
                foreach (var s in new[] { x, y })
                    if (regions && s.Heaps.IsEmpty) Line($"{module}.{Names.ClassToHeap(name)} {s.Binder};");
                Line($"{module}.{Names.ClassDistinct(name)} {x.Binder} {y.Binder};");
                foreach (var s in new[] { y, x })
                    if (regions && s.Heaps.IsEmpty) Line($"{module}.{Names.ClassOfHeap(name)} {s.Binder};");
            }
        }
    }

    private bool TouchesFields(IrMethod method) =>
        method.Body is not null
        && Check.Statements(method.Body)
            .SelectMany(Check.Expressions)
            .SelectMany(Check.Subexpressions)
            .Any(e => e is IrField { Receiver: IrVar { Name: var n } } && n == Names.This ||
                      // R33.15. An `[Open]` callee takes the receiver as the opened
                      // invariant holds it.
                      e is IrCall { HasReceiver: true, Args: [IrVar { Name: Names.This }, ..] } oc &&
                      openMethods?.Contains(oc.Callee) == true ||
                      // R27.13. A node of the receiver's region is read in the receiver's
                      // region, which only the opened invariant holds.
                      e is IrField { Receiver.Type: IrClassType k } && IsRegionType(k) &&
                      method.DeclaringClass is { } dc && classes is not null &&
                      classes.TryGetValue(dc, out var owner) && RegionsOf(owner).Any(r => r.Name == k.Name));

    /// <summary>R2.1's type qualifier removed, so a diagnostic names what the user wrote.</summary>
    private static string Unqualify(string name, string? klass) =>
        klass is not null && name.StartsWith(klass + "_", StringComparison.Ordinal)
            ? name[(klass.Length + 1)..]
            : name;

    /// <summary>
    /// R4.10c. A call on the receiver from inside one of its own methods, if there is one.
    /// </summary>
    private static IrCall? SelfCall(IrMethod method) =>
        method.Body is null ? null
        : Check.Statements(method.Body)
            .SelectMany(Check.Expressions)
            .SelectMany(Check.Subexpressions)
            .OfType<IrCall>()
            .FirstOrDefault(c => c is { HasReceiver: true, Args: [IrVar { Name: var n }, ..] }
                                 && n == Names.This);

    private static string Unfold(Slot obj) => obj.Heaps.IsEmpty
        ? $"unfold {Inv((IrClassType)obj.Type)} {obj.Binder} {obj.PermArg}{obj.PreModel}"
        : $"unfold {InvHeap((IrClassType)obj.Type)} {obj.Binder} {obj.PermArg}{obj.PreModel} " +
          string.Join(" ", obj.Heaps.Select(h => h.Pre));

    private static string InvHeap(IrClassType c) =>
        $"{Names.ClassModule(c.Name)}.{Names.ClassInvHeap(c.Name)}";

    /// <summary>
    /// R27.44. Opens another object of the receiver's class around <paramref name="inside"/>,
    /// through its own invariant, and closes it at the same model. Its heaps are named
    /// explicitly, so the fold cannot pick up the receiver's region by mistake.
    /// </summary>
    private void PeerOpen(Slot obj, IrClassType oc, Action inside, Func<IReadOnlyList<string>, IReadOnlyList<string>>? after = null)
    {
        var decl = classes![oc.Name];
        var regions = RegionsOf(decl).ToList();
        var model = obj.PreModel;
        if (regions.Count == 0)
        {
            // R33.28. A local has no model named on entry: the bracket names the one it holds.
            if (string.IsNullOrEmpty(model))
            {
                model = FreshValue(obj.Name);
                Line($"with {model}. assert ({Inv(oc)} {obj.Binder} {obj.PermArg}{model});");
            }
            Line($"unfold {Inv(oc)} {obj.Binder} {obj.PermArg}{model};");
            inside();
            Line($"fold {Inv(oc)} {obj.Binder} {obj.PermArg}{model};");
            return;
        }
        var hs = regions.Select(k => FreshValue(Frontend.Region.HeapBinder(k.Name))).ToList();
        var module = Names.ClassModule(oc.Name);
        Line($"{module}.{Names.ClassToHeap(oc.Name)} {obj.Binder};");
        var args = $"{obj.Binder} {obj.PermArg}{model} {string.Join(" ", hs)}";
        Line($"with {string.Join(" ", hs)}. assert ({InvHeap(oc)} {args});");
        Line($"unfold {InvHeap(oc)} {args};");
        _peerHeaps.Push(regions.Select((k, i) => (k, hs[i])).ToList());
        inside();
        _peerHeaps.Pop();
        var post = after?.Invoke(hs) ?? hs;
        Line($"fold {InvHeap(oc)} {obj.Binder} {obj.PermArg}{model} {string.Join(" ", post)};");
        Line($"{module}.{Names.ClassOfHeap(oc.Name)} {obj.Binder};");
    }

    /// <summary>
    /// R33.28. A statement that writes a field of another object of the receiver's class --
    /// a field, an element of an array field, or the destination of an array copy -- held
    /// whole by a local or parameter without regions.
    /// </summary>
    private (Slot Slot, IrClass Class)? PeerWritten(IrStmt stmt)
    {
        var target = PeerTarget(stmt);
        if (target is not { Peer: true, Receiver: IrVar pv } || pv.Name == Names.This ||
            _peerOpen.Contains(pv.Name) || _objects.Any(o => o.Name == pv.Name) ||
            !_slots.TryGetValue(pv.Name, out var slot) ||
            slot is not { Kind: SlotKind.Object, Open: false, Type: IrClassType oc } ||
            classes is null || !classes.TryGetValue(oc.Name, out var decl) || RegionsOf(decl).Any())
            return null;
        return (slot, decl);
    }

    private static IrField? PeerTarget(IrStmt stmt) => stmt switch
    {
        IrAssign { Target: IrField { Peer: true } f } => f,
        IrAssign { Target: IrElement { Array: IrField { Peer: true } f } } => f,
        IrArrayOp { Written: IrField { Peer: true } f } => f,
        _ => null,
    };

    /// <summary>
    /// R33.28. Opens the object around a statement that writes one of its fields, at the
    /// model its invariant holds, and closes it at the model of what the statement left.
    /// </summary>
    private void PeerWrite(Slot obj, IrClass decl, Action inside)
    {
        var oc = (IrClassType)obj.Type;
        var model = FreshValue(obj.Name);
        Line($"with {model}. assert ({Inv(oc)} {obj.Binder} {obj.PermArg}{model});");
        Line($"unfold {Inv(oc)} {obj.Binder} {obj.PermArg}{model};");
        _peerOpen.Add(obj.Name);
        try { inside(); } finally { _peerOpen.Remove(obj.Name); }
        Line($"fold {Inv(oc)} {obj.Binder} {obj.PermArg}{ModelWitness(decl, obj)};");
    }

    private readonly Stack<List<(IrClassType Region, string Heap)>> _peerHeaps = new();
    private readonly HashSet<string> _peerOpen = [];

    /// <summary>
    /// R27.44. A call that takes a pointer read from a field of another object of the
    /// receiver's class: the call runs in that object's region, so it is emitted inside
    /// <see cref="PeerOpen"/>. Returns the object and the region class.
    /// </summary>
    private (Slot Slot, IrClassType Region)? PeerRegionCall(IrCall call)
    {
        foreach (var a in call.Args)
        {
            var e = a;
            while (e is IrField { Receiver: IrField inner } && IsRegionType(inner.Type)) e = inner;
            if (e is IrField { Receiver: IrVar pv, Peer: true } pf && IsRegionType(pf.Type) &&
                pv.Name != Names.This && !_peerOpen.Contains(pv.Name) &&
                !_objects.Any(o => o.Name == pv.Name) &&
                _slots.TryGetValue(pv.Name, out var ps) && ps is { Kind: SlotKind.Object, Type: IrClassType } &&
                pf.Type is IrClassType k)
                return (ps, k with { Nullable = false });
        }
        return null;
    }

    /// <summary>
    /// R27.44. A call in another owner's region. The receiver's own region of the same
    /// class, if the context holds it bare, is parked around the call so that the callee's
    /// region is unambiguous. A region pointer the call returns is a tree it built fresh
    /// (<c>Reshaped(null, Result)</c>, checked by <c>RegionMove.move</c>): it is moved into the
    /// receiver's region, so that the receiver can store it, and the other owner is closed
    /// over what is left — which is what it held before the call.
    /// </summary>
    private string PeerCall(IrCall call, string binder, Slot peer, IrClassType k)
    {
        var oc = (IrClassType)peer.Type;
        var thisBare = _objects.Any(o => o.Name == Names.This && o.Type is IrClassType tc &&
                                         classes!.TryGetValue(tc.Name, out var td) &&
                                         RegionsOf(td).Any(r => r.Name == k.Name)) ||
                       _slots.Values.Any(s => s is { Open: true } && s.OpenHeaps.Any(r => r.Name == k.Name)) ||
                       _plan!.Held.Any(u => u.Region.Name == k.Name);
        string? parked = null;
        if (thisBare)
        {
            parked = FreshValue(Frontend.Region.HeapBinder(k.Name));
            Line($"with {parked}. assert ({PulseEmitter.RegionAt(k, "1.0R", parked)});");
            Line($"{MoveModule}.park {parked};");
        }
        var result = binder;
        string? postHeap = null;
        PeerOpen(peer, oc, () =>
        {
            _peerOpen.Add(peer.Name);
            result = Call(call, binder);
            _peerOpen.Remove(peer.Name);
            var h1 = FreshValue(Frontend.Region.HeapBinder(k.Name));
            Line($"with {h1}. assert ({PulseEmitter.RegionAt(k, "1.0R", h1)});");
            postHeap = h1;
            if (parked is null) return;
            Line($"{MoveModule}.unpark {parked};");
            if (call.ResultType is IrClassType rt && rt.Name == k.Name)
            {
                var h0 = _peerHeaps.Peek().First(p => p.Region.Name == k.Name).Heap;
                var lr = RegionShape(k);
                Line($"{MoveModule}.move {lr} {h0} {h1} {parked} {result};");
                postHeap = $"({MoveModule}.moved_from {lr} {h1} {result})";
            }
        }, hs =>
        {
            var regions = RegionsOf(classes![oc.Name]).ToList();
            return hs.Select((h, i) => regions[i].Name == k.Name && postHeap is not null ? postHeap : h).ToList();
        });
        return result;
    }

    private const string MoveModule = "Pulse.Lib.CSharp.RegionMove";

    /// <summary>
    /// R27.55. <c>f = o.g;</c>, with <c>f</c> a region field of the receiver and <c>o</c> an
    /// object local of an owner class whose <c>g</c> is a pointer of the same region class:
    /// the receiver adopts <c>o</c>'s tree. <c>o</c> is opened for good: its record is held
    /// bare from here on, so its other fields can still be read, and the boxes of the tree
    /// <c>g</c> roots move into the receiver's region (<c>RegionMove.adopt</c>, which needs
    /// the tree unshared, as <c>o</c>'s invariant says it is). What remains of <c>o</c>'s
    /// regions is dropped; <c>o</c> is never closed again, so nothing can call its methods.
    /// </summary>
    private void Adopt(IrAssign a)
    {
        if (a.Target is not IrField { Receiver: IrVar { Name: Names.This } } tf || !IsRegionType(tf.Type) ||
            a.Value is not IrField { Receiver: IrVar dv } df || dv.Name == Names.This ||
            !IsRegionType(df.Type) || df.Type is not IrClassType k ||
            !_slots.TryGetValue(dv.Name, out var ds) || ds is not { Kind: SlotKind.Object, Type: IrClassType dc, Open: false } ||
            _peerOpen.Contains(dv.Name) || !_objectLocals.Any(l => l.Name == dv.Name && l.Binder == ds.Binder) ||
            !classes!.TryGetValue(dc.Name, out var ddecl))
            return;
        k = k with { Nullable = false };
        var regions = RegionsOf(ddecl).ToList();
        if (!regions.Any(r => r.Name == k.Name)) return;
        var into = FreshValue(Frontend.Region.HeapBinder(k.Name));
        Line($"with {into}. assert ({PulseEmitter.RegionAt(k, "1.0R", into)});");
        Line($"{MoveModule}.park {into};");
        var hs = regions.Select(r => FreshValue(Frontend.Region.HeapBinder(r.Name))).ToList();
        var model = FreshValue(dv.Name);
        var module = Names.ClassModule(dc.Name);
        Line($"{module}.{Names.ClassToHeap(dc.Name)} {ds.Binder};");
        var args = $"{ds.Binder} {model} {string.Join(" ", hs)}";
        Line($"with {model} {string.Join(" ", hs)}. assert ({InvHeap(dc)} {args});");
        Line($"unfold {InvHeap(dc)} {args};");
        var t = Fresh();
        Line($"let {t} = B.op_Bang {ds.Binder};");
        Line($"{MoveModule}.unpark {into};");
        var lr = RegionShape(k);
        var x = $"{t}.{Names.ClassProjection(dc.Name, df.Field)}";
        for (var i = 0; i < regions.Count; i++)
        {
            var r = regions[i];
            if (r.Name == k.Name)
            {
                Line($"{MoveModule}.adopt {lr} {hs[i]} {into} {x};");
                Line($"drop_ ({PulseEmitter.RegionAt(r, "1.0R", $"({MoveModule}.moved_from {lr} {hs[i]} {x})")});");
            }
            else
                Line($"drop_ ({PulseEmitter.RegionAt(r, "1.0R", hs[i])});");
        }
        var opened = ds with { Open = true };
        _slots[dv.Name] = opened;
        var at = _objectLocals.FindIndex(l => l.Name == dv.Name && l.Binder == ds.Binder);
        _objectLocals[at] = opened;
    }

    /// <summary>R27.44. The child projections of a region class, applied to its type arguments.</summary>
    private static string RegionShape(IrClassType k)
    {
        string App(string f) => k.TypeArguments.Length == 0
            ? $"{Names.ClassModule(k.Name)}.{f}"
            : $"({Names.ClassModule(k.Name)}.{f}{string.Concat(k.TypeArguments.Select(t => " #" + Types.Atom(t)))})";
        return $"{App(Frontend.Region.LeftOf(k.Name))} {App(Frontend.Region.RightOf(k.Name))}";
    }

    /// <summary>R27.13. The heaps the last <see cref="ModelWitness"/> read the regions at.</summary>
    private ImmutableArray<string> _witnessHeaps = [];

    /// <summary>
    /// R4.10's fold/unfold bracket, opened. R9.14: an <c>override</c> is handed its
    /// receiver at the base's model, so there is one bracket more to open — the view
    /// first, then the class's own invariant inside it. The <c>with</c> is how the body
    /// gets a name for its own model, which the view existentially quantifies.
    /// </summary>
    private void OpenReceiver(Slot obj)
    {
        var klass = (IrClassType)obj.Type;
        if (obj.ViewBase is not { } b) { Line(Unfold(obj) + ";"); return; }

        Line($"unfold {Names.ClassModule(klass.Name)}." +
             $"{Names.ClassAsBase(klass.Name, b)} {obj.Binder} {obj.PermArg}{obj.PreModel};");
        Line($"with {obj.OwnModel}. assert ({Inv(klass)} {obj.Binder} {obj.PermArg}{obj.OwnModel});");
        Line($"unfold {Inv(klass)} {obj.Binder} {obj.PermArg}{obj.OwnModel};");
    }

    /// <summary>
    /// R4.11a — the fold witness. A read-only method re-folds at the binder it was handed:
    /// its model did not change, and re-folding at a *recomputed* model instead leaves
    /// Pulse two syntactically different indices to reconcile, which it will not do
    /// (Error 228). A mutator has no such binder to appeal to, so it re-folds at the
    /// abstraction function applied to the representation it has just written — the same
    /// expression the class module puts in the invariant, evaluated at the post-state.
    /// </summary>
    private bool NeedsEpilogue => _objects.Length > 0 || _objectLocals.Count > 0 || _windows.Count > 0 || _heldPeers.Count > 0;

    /// <summary>
    /// R4.14. Discards the invariant of every object this method allocated and did not
    /// hand back. <c>with m. assert …</c> names the existential witness the context is
    /// holding, which <c>drop_</c> needs because it takes an slprop and not a name.
    /// </summary>
    /// <summary>
    /// R4.14's scope rule. An object local's resource is discarded where C# says its name
    /// goes out of scope — at the end of the block that declares it — and not merely at
    /// the end of the method. A block that is *not* in tail position drops what it
    /// declared as it closes; one that is leaves the discard to the return, which knows
    /// which object is being handed back.
    ///
    /// Either way the block's declarations leave the list on the way out. Without that,
    /// an object allocated in one arm of an `if` would be dropped in the other, where its
    /// binder does not exist.
    /// </summary>
    private void Scoped(Action emit, bool dropAtEnd)
    {
        var mark = _objectLocals.Count;
        // A slot is a *binding*, and a binding introduced inside a block is out of scope
        // once the block closes. Nothing outside may name it — in particular R5.13's
        // resource-naming bracket, which would otherwise assert `pts_to` for a cell whose
        // Pulse binder no longer exists.
        var declared = new HashSet<string>(_slots.Keys);
        var peers = _heldPeers.Count;
        if (dropAtEnd) _closingBlocks++;
        emit();
        // R27.49. A peer held at its heaps in this block is held plain again past it: the
        // block's tail handed it back (R27.41 refuses a held struct in a non-tail block).
        foreach (var peer in _heldPeers.Skip(peers))
            if (_slots.TryGetValue(peer.Name, out var now) && now.Binder == peer.Binder)
                _slots[peer.Name] = now with { Heaps = [] };
        if (_heldPeers.Count > peers) _heldPeers.RemoveRange(peers, _heldPeers.Count - peers);
        if (dropAtEnd)
        {
            _closingBlocks--;
            foreach (var local in _objectLocals.Skip(mark).Where(_nestedArrays.ContainsKey))
                diagnostics.Error("PALCS0623", _nestedArrays[local],
                    $"`{local.Name}` is initialised with a fresh array in a nested block and " +
                    "still owns it where the block closes. The array would be discarded there, " +
                    "and a block in statement position has no postcondition for the discard to " +
                    "be checked against (F19). Move it into a field before the block ends, or " +
                    "declare it in the method's own block (doc/translation.md R6.11a).");
            DropLocals(null, mark);
        }
        if (_objectLocals.Count > mark) _objectLocals.RemoveRange(mark, _objectLocals.Count - mark);
        foreach (var name in _slots.Keys.Where(n => !declared.Contains(n)).ToList())
            _slots.Remove(name);
    }

    private void DropLocals(string? returned, int from = 0, string? ownedBy = null,
        ImmutableArray<(string Field, string Projection)> owned = default)
    {
        foreach (var local in _objectLocals.Skip(from))
        {
            if (local.Binder == returned) continue;
            var m = FreshValue(local.Name);
            // R27.37. An object the returned borrowing struct owns is handed over under
            // the struct's field: the value is the same reference, so the rewrite is pure.
            if (ownedBy is not null && !owned.IsDefaultOrEmpty &&
                owned.FirstOrDefault(o => Pal.Compiler.Frontend.Borrowing.OwnedName(o.Field) == local.Name) is { Projection: { } proj })
            {
                Line($"with {m}. assert ({local.Resource(m)});");
                Line($"assert (pure ({ownedBy}.{proj} == {local.Binder}));");
                Line($"rewrite ({local.Resource(m)}) as ({(local with { Binder = $"({ownedBy}.{proj})" }).Resource(m)});");
                continue;
            }
            // R34.10. The cell itself is reclaimed with its scope; the array is dropped.
            if (local.Kind == SlotKind.ArrayCell)
            {
                Line($"Pulse.Lib.CSharp.ArrayCell.release {local.Binder};");
                continue;
            }
            Line($"with {m}. assert ({local.Resource(m)});");
            Line($"drop_ ({local.Resource(m)});");
        }
    }

    private void CloseObjects(IrMethod method, MethodPlan plan, string? returned = null, string? ownedBy = null)
    {
        DropLocals(returned, 0, ownedBy, plan.ResultOwned);

        // R33.27. A span the body borrowed from the opened receiver's arrays and left
        // borrowed when its scope ended is given back before the receiver is closed, the
        // latest borrow first.
        if (_objects.Length > 0)
            foreach (var span in _slots.Values.Where(s => s is { Kind: SlotKind.Span, Origin: not null }).Reverse().ToList())
            {
                // A window left as it was borrowed gives the array back unchanged.
                if (span.Origin is SpanOrigin.ArrayRange)
                {
                    var (a, i, j, v) = (FreshValue("a"), FreshValue("i"), FreshValue("j"), FreshValue("v"));
                    Line($"with {a} {i} {j} {v}. assert (Span.is_range_of {a} {span.Binder} {span.Fraction ?? "1.0R"} {i} {j} {v});");
                    Line($"Pulse.Lib.CSharp.Seq.splice_same {v} {i} {j};");
                }
                Line($"Span.{span.Origin switch
                {
                    SpanOrigin.Array => "restore_array",
                    SpanOrigin.ArrayRange => "restore_array_range",
                    _ => "restore_sub",
                }} {span.Binder};");
            }

        // R10.7. The innermost window closes first: it was opened last, and what it
        // re-establishes is a conjunct of what the one outside it re-establishes.
        for (var i = _windows.Count - 1; i >= 0; i--) Line(_windows[i]);

        foreach (var obj in _objects) CloseObject(method, obj);
        // R27.49. Another object held at its heaps is handed back as it was received.
        foreach (var peer in _heldPeers)
            Line($"{Names.ClassModule(((IrClassType)peer.Type).Name)}.{Names.ClassOfHeap(((IrClassType)peer.Type).Name)} {peer.Binder};");
    }

    /// <summary>R22.15. Reopens the receiver a call closed, at whatever model the callee left.</summary>
    private void Reopen(Slot self, ImmutableArray<IrClassType>? heaps)
    {
        var klass = (IrClassType)self.Type;
        if (heaps is { } regions)
        {
            var m = FreshValue(klass.Name);
            var hs = regions.Select(k => FreshValue(Frontend.Region.HeapBinder(k.Name))).ToList();
            var args2 = $"{self.Binder} {self.PermArg}{m} {string.Join(" ", hs)}";
            Line($"with {m} {string.Join(" ", hs)}. assert ({InvHeap(klass)} {args2});");
            Line($"unfold {InvHeap(klass)} {args2};");
        }
        else if (self.PostModel == self.PreModel)
            Line($"unfold {Inv(klass)} {self.Binder} {self.PermArg}{self.PreModel};");
        else
        {
            var m = FreshValue(klass.Name);
            Line($"with {m}. assert ({Inv(klass)} {self.Binder} {self.PermArg}{m});");
            Line($"unfold {Inv(klass)} {self.Binder} {self.PermArg}{m};");
        }
    }

    /// <summary>R27.59. The owned fields left open at a heap by a call that returned a region pointer.</summary>
    // R32.10. `Regions` names the field's region classes in the order of its heap
    // arguments; `Written` is set when the method has since written one of them.
    private readonly Dictionary<string, (IrClassType Class, string Args, string? Perm, IReadOnlyList<string> Regions,
        IReadOnlyList<string> Heaps, IReadOnlyList<IrClassType> Written)> _fieldOpen = [];

    /// <summary>R32.10. A write to (or an allocation in) a region of class <paramref name="k"/> may be a write to an open field's region.</summary>
    private void FieldRegionWritten(IrClassType k)
    {
        foreach (var (f, open) in _fieldOpen.ToList())
            if (open.Regions.Contains(k.Name) && !open.Written.Any(w => w.Name == k.Name))
                _fieldOpen[f] = open with { Written = [.. open.Written, k] };
    }

    /// <summary>R27.59. Closes an owned field <see cref="_fieldOpen"/> holds open, back to its invariant.</summary>
    private void CloseFieldRegion(string field, bool forget = true)
    {
        if (!_fieldOpen.TryGetValue(field, out var open)) return;
        var fexpr = open.Args.Split(' ')[0];
        if (open.Written.Count == 0)
            Line($"fold {InvHeap(open.Class)} {open.Args};");
        else
        {
            // R32.10. The method wrote the field's region since the call that opened it:
            // the invariant is folded again at the heap the region holds now, and at the
            // model that heap and the field's record determine. Folding it at that model
            // is the proof obligation that the write kept the invariant's refinements.
            var perm = open.Perm ?? "1.0R";
            var heaps = open.Heaps.ToList();
            foreach (var k in open.Written)
            {
                var hn = FreshValue(Frontend.Region.HeapBinder(k.Name));
                Line($"with {hn}. assert ({PulseEmitter.RegionAt(k, perm, hn)});");
                heaps[open.Regions.ToList().IndexOf(k.Name)] = hn;
            }
            var rn = FreshValue(open.Class.Name);
            Line($"with {rn}. assert (B.pts_to {fexpr} #{perm} {rn});");
            var model = $"({Names.ClassModule(open.Class.Name)}.{Names.ClassAbsModel(open.Class.Name)} {rn} {string.Join(" ", heaps)})";
            Line($"fold {InvHeap(open.Class)} {fexpr} {(open.Perm is null ? "" : $"#{open.Perm} ")}{model} {string.Join(" ", heaps)};");
        }
        Line($"{Names.ClassModule(open.Class.Name)}.{Names.ClassOfHeap(open.Class.Name)} {fexpr};");
        if (forget) _fieldOpen.Remove(field);
    }

    /// <summary>R4.11a. Re-establishes one open object's invariant.</summary>
    private void CloseObject(IrMethod method, Slot obj)
    {
        // R27.59. Every path that closes the receiver closes the fields it holds open; the
        // record is kept for the other branches, which close them too.
        if (obj.Name == Names.This)
            foreach (var field in _fieldOpen.Keys.ToList()) CloseFieldRegion(field, forget: false);
        {
            var klass = (IrClassType)obj.Type;
            // R4.11a. A read-only method re-folds at the binder it was handed; under a
            // view (R9.14) that binder names the class's *own* model, which the opening
            // `with` introduced, and the view closes at the base model it was given.
            if (obj.PostModel == obj.PreModel)
            {
                var own = obj.ViewBase is null ? obj.PreModel : obj.OwnModel;
                if (!obj.Heaps.IsEmpty)
                {
                    Line($"fold {InvHeap(klass)} {obj.Binder} {obj.PermArg}{own} " +
                         $"{string.Join(" ", obj.Heaps.Select(h => h.Pre))};");
                    return;
                }
                Line($"fold {Inv(klass)} {obj.Binder} {obj.PermArg}{own};");
                CloseView(obj, obj.PreModel!);
                return;
            }

            if (classes is null || !classes.TryGetValue(klass.Name, out var decl))
            {
                diagnostics.Unsupported(method.Loc,
                    $"Mutating an object of class `{klass.Name}` whose model is not in this translation unit");
                return;
            }

            var witness = ModelWitness(decl, obj);
            if (obj.ViewBase is null)
            {
                Line(obj.Heaps.IsEmpty
                    ? $"fold {Inv(klass)} {obj.Binder} {witness};"
                    : $"fold {InvHeap(klass)} {obj.Binder} {witness} {string.Join(" ", _witnessHeaps)};");
                return;
            }

            // A mutator under a view re-folds twice, and the outer index is the inner one
            // pushed through R9.6's forgetting function. That is what makes an override
            // satisfy the base's postcondition: the base's model of the post-state *is*
            // the forgetting of this class's model of it.
            var post = Fresh();
            Line($"let {post} = {witness};");
            Line($"fold {Inv(klass)} {obj.Binder} {obj.PermArg}{post};");
            CloseView(obj, $"({Names.ClassModule(klass.Name)}.{Names.ClassForget(klass.Name)} {post})");
        }
    }

    /// <summary>R9.14. Closes the base-model view an <c>override</c>'s receiver is held at.</summary>
    private void CloseView(Slot obj, string model)
    {
        if (obj.ViewBase is not { } b) return;
        var klass = (IrClassType)obj.Type;
        Line($"fold {Names.ClassModule(klass.Name)}." +
             $"{Names.ClassAsBase(klass.Name, b)} {obj.Binder} {obj.PermArg}{model};");
    }

    /// <summary>
    /// The abstraction function applied to the object's current representation: the
    /// <c>[Model]</c> member's body, with each field read through the box.
    /// </summary>
    private string ModelWitness(IrClass decl, Slot obj)
    {
        var raw = Fresh();
        Line($"let {raw} = B.op_Bang {obj.Binder};");

        var scope = new SpecScope();
        foreach (var field in decl.Fields)
        {
            var projection = $"{raw}.{Names.ClassProjection(decl.Name, field.Name)}";
            if (field.Type is IrArrayType)
            {
                // R3.10a. The abstraction reads an array field's *contents*, and the
                // contents are an existential the context is holding rather than anything
                // this method named — the array has been written since the `unfold`, so
                // even the binder the `unfold` produced is stale. `with c. assert p`
                // names what is actually there, which is the same device R4.14 needs.
                var contents = FreshValue(field.Name);
                Line($"with {contents}. assert ({PulseEmitter.ArrayPts(field)} {projection} {contents});");
                scope.Bind(field.Name, new Term(contents, TermKind.Seq, field.Type));
                scope.Bind(SpecEmitter.ArrayRefKey(field.Name), new Term(projection, TermKind.Other, field.Type));
                continue;
            }
            if (IsRegionType(field.Type))
            {
                scope.Bind(field.Name, new Term(projection, TermKind.Other, field.Type));
                continue;
            }
            if (field.Type is IrClassType)
            {
                // R3.10b, and the same device for the same reason. A sub-object's model
                // may have moved since the `unfold` — that is what calling a method on it
                // does — so the abstraction reads whatever model the context is now
                // holding for it, not the one the `unfold` produced.
                var subModel = FreshValue(Names.SubModel(field.Name));
                Line($"with {subModel}. assert " +
                     $"({PulseEmitter.SubInvAt(field.Type, projection, obj.PermArg, subModel)});");
                scope.Bind(field.Name, new Term(subModel, TermKind.Math, field.Type));
                continue;
            }
            scope.Bind(field.Name, new Term(
                projection, MethodPlan.KindOf(field.Type), field.Type));
        }

        // R27.4. The model reads the region as the context now holds it.
        var heaps = ImmutableArray.CreateBuilder<string>();
        foreach (var k in RegionsOf(decl))
        {
            var heap = FreshValue(Frontend.Region.HeapBinder(k.Name));
            heaps.Add(heap);
            Line($"with {heap}. assert ({PulseEmitter.RegionAt(k, obj.Fraction ?? "1.0R", heap)});");
            scope.Bind(Frontend.Region.HeapName(k.Name), new Term(heap, TermKind.Other));
        }
        _witnessHeaps = heaps.ToImmutable();

        // R9.2: only a class with a representation has an abstraction function, and only
        // such a class reaches here — an abstract class's model is supplied by its leaves.
        var body = decl.ModelBody ?? throw new InvalidOperationException(
            $"{decl.Name} has no abstraction function");
        return MethodPlan.KindOf(decl.ModelType) == TermKind.Math
            ? spec.Math(body, scope)
            : $"({spec.Emit(body, scope).Text})";
    }

    // =======================================================================
    // Statements
    // =======================================================================

    private void Statement(IrStmt stmt, MethodPlan plan)
    {
        // Every line emitted from here down belongs to this statement, unless a nested
        // statement claims it first. Saving and restoring rather than just assigning is
        // what keeps a block's closing lines attributed to the block and not to whatever
        // it happened to contain last.
        var outer = _loc;
        _loc = stmt.Loc;
        try
        {
            if (PeerWritten(stmt) is { } peer) PeerWrite(peer.Slot, peer.Class, () => StatementCore(stmt, plan));
            else StatementCore(stmt, plan);
        }
        finally { _loc = outer; }
        if (!_receiverDirty && DirtiesReceiver(stmt)) _receiverDirty = true;
    }

    private void StatementCore(IrStmt stmt, MethodPlan plan)
    {
        switch (stmt)
        {
            // R3.8. An object local binds a reference. C# can rebind it, but nothing in
            // the supported subset does, and binding it immutably is what lets it be
            // handed to a callee that consumes and returns its invariant.
            // R12.4. A local naming a `[Plain]` object. An immutable binder rather than
            // R5.2's `let mut` cell: the reference is a value, and the resource behind it
            // is matched by the binder's name, so putting it in a cell would leave every
            // later mention asking for a `pts_to` at a name Pulse cannot see through.
            // R17.5. A span local. Like R12.4's `[Plain]` reference and unlike R5.2's
            // ordinary local, it gets an immutable binder rather than a `let mut` cell:
            // Pulse matches `S.pts_to` by name, so putting the slice in a cell would leave
            // the context holding the resource at a name every later mention has to read
            // through. C# agrees — a `Span<T>` local the subset admits is never reassigned,
            // because a reassignment would abandon a live receipt.
            //
            // The slot records where the borrow came from. That is not flow analysis: it is
            // the shape of the initializer, read once, at the declaration that wrote it.
            case IrLocalDecl { Type: IrSpanType, Init: IrSpanCreate create } d:
            {
                // The borrow is emitted *at* the local's binder rather than at a fresh one
                // it is then copied from, for the reason R12.4 gives for an allocation:
                // Pulse matches resources by name, so a copy would leave the context
                // holding `S.pts_to t0 _` while every later mention asked for
                // `S.pts_to var_s _` (F77).
                var binder = Names.Local(d.Name);
                Borrow(create, binder);
                _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Span, binder)
                {
                    Origin = create.Origin,
                    BorrowedField = create.Source is IrField { Receiver: IrVar { Name: Names.This }, Field: var bf } ? bf : null,
                    // R33.27. A window of the receiver's array is held at the receiver's permission.
                    Fraction = create.Source is IrField { Receiver: IrVar { Name: Names.This } }
                        ? _objects.FirstOrDefault(o => o.Name == Names.This)?.Fraction : null,
                };
                return;
            }

            // R17.5. A span local with any other initializer — another span local, a span
            // parameter, a conditional. Each would alias a live borrow under a second name
            // (SliceFacts S4), and the receipt names only one of them.
            case IrLocalDecl { Type: IrSpanType } d:
                diagnostics.SpanWindow(d.Loc,
                    $"a `Span<T>` local initialised from anything but a borrow (`{d.Name}`)");
                return;

            case IrLocalDecl { Type: IrClassType pc, Init: not null } d
                when classes is not null && classes.TryGetValue(pc.Name, out var pdecl) && pdecl.IsPlain:
            {
                var pbinder = Names.Local(d.Name);
                if (d.Init is IrAlloc pal)
                {
                    // The allocation is emitted *at* the local's binder rather than at a
                    // fresh one it is then copied from. Pulse matches resources by name, so
                    // a copy would leave the context holding `pts_to t0 _` while every later
                    // mention asked for `pts_to var_node _` — the same reason R3.8's alias
                    // case shares a slot instead of rebinding one.
                    // R27.6. A region object is allocated into its owner's region.
                    if (pdecl.IsRegion)
                        Line($"let {pbinder} = {Frontend.Region.Module}.alloc {AllocRecord(pal)};");
                    else
                    {
                        Line($"let {pbinder} = B.alloc {AllocRecord(pal)};");
                        Line($"B.pts_to_not_null {pbinder};");
                    }
                }
                else if (d.Immutable)
                {
                    _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Value, Expr(d.Init));
                    return;
                }
                else
                {
                    // R12.3b. A `[Plain]` reference the body *assigns* is a local like any
                    // other, so R5.2 applies unchanged: it gets a `let mut`, and its slot is
                    // a cell whose resource is an ordinary `R.pts_to`. That is what a cursor
                    // is — a reference the loop moves — and it needs no rule of its own,
                    // only the ordinary one not being skipped because the local happens to
                    // hold a reference.
                    Line($"let mut {pbinder} = {Expr(d.Init)};");
                    _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Cell, pbinder);
                    return;
                }
                _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Value, pbinder);
                return;
            }

            case IrLocalDecl { Type: IrClassType, Init: IrVar alias } d
                when Lookup(alias.Name) is { Kind: SlotKind.Object } aliased:
            {
                // R3.8, the other half. `C x = y;` binds a second C# name to one object; it
                // allocates nothing and owns nothing, because the invariant is attached to
                // `y` and Pulse matches resources by name. So the translation is to *share
                // the slot*: `x` and `y` denote the same Pulse binder, and every rule that
                // consults a slot — R4.14's discard, R5.13's lemma, an argument position —
                // sees one object, which is what C# says there is.
                //
                // Emitting `let var_x = var_y;` instead would leave the context holding
                // `inv var_y _` while every later mention asked for `inv var_x _`, and no
                // pure equality closes that gap (Error 228).
                _slots[d.Name] = aliased with { Name = d.Name };
                return;
            }

            case IrLocalDecl { Type: IrClassType oc, Init: not null } d:
            {
                // F19. The discard would land at this block's close, where Pulse is still
                // solving for the block's postcondition and cannot open the object's
                // model existential. Refused rather than emitted (§0 rule 3).
                if (_closingBlocks > 0)
                {
                    diagnostics.Unsupported(d.Loc,
                        $"`new {oc.Name}()` in a nested block",
                        "An object allocated here would be discarded where the enclosing " +
                        "block closes (R4.14), and a block in statement position has no " +
                        "postcondition of its own for the discard to be checked against: " +
                        "Pulse reports `Cannot find witness` for the object's model (F19). " +
                        "Allocate it in the method's own block, or in a branch that " +
                        "returns.");
                    return;
                }

                var binder = Names.Local(d.Name);

                // R9.15/R9.16. A reference conversion, which C# writes silently when it
                // goes up and explicitly when it comes back down. The two directions are
                // told apart by the hierarchy, not by the syntax, because `Shape s = sq;`
                // and `Square q = (Square) s;` are the same IR node.
                if (d.Init is IrConvert { Target: IrClassType } conv)
                {
                    var from = (conv.Operand.Type as IrClassType)?.Name;
                    if (Ancestors(from, oc.Name) is not null)
                    {
                        if (Upcast(d.Loc, conv.Operand, oc, d.Name, binder) is { } up)
                        {
                            _slots[d.Name] = up;
                            _objectLocals.Add(up);
                        }
                        return;
                    }

                    if (conv.Operand is IrVar source && Ancestors(oc.Name, from) is not null)
                    {
                        Downcast(d, oc, source, binder);
                        return;
                    }

                    diagnostics.Unsupported(d.Loc,
                        $"Converting a `{from}` to a `{oc.Name}`",
                        "R9.15 converts a reference between a class and its bases; " +
                        "these two are not related that way.");
                    return;
                }

                // The initialiser is emitted *into* the local's binder rather than into a
                // temporary the local then aliases. Pulse matches resources syntactically:
                // after `let var_c = t0` the context still holds `inv t0 _`, and no amount
                // of pure equality will let the frame rule find `inv var_c _` (Error 228).
                if (d.Init is IrCall { Kind: CalleeKind.Method } call) Call(call, binder);
                else Line($"let {binder} = {Expr(d.Init)};");

                var local = new Slot(d.Name, oc, SlotKind.Object, binder);
                _slots[d.Name] = local;
                _objectLocals.Add(local);
                return;
            }

            case IrBlock b:
                Scoped(() => Sequence(b.Statements, plan), dropAtEnd: true);
                return;

            case IrLocalDecl { Type: IrArrayType, Init: IrNewArray or IrOrderBy } d:
                ArrayLocal(d);
                return;

            // R32.14. So is a view of another object of the class, which owns nothing.
            case IrLocalDecl { Owned.IsDefaultOrEmpty: false } or IrLocalDecl { HeldOwner: not null }:
                HeldStruct((IrLocalDecl)stmt);
                return;

            case IrLocalDecl d:
                LocalDeclaration(d);
                return;

            case IrAssign a:
                Assign(a);
                return;

            case IrIf i:
                If(i, plan);
                return;

            case IrWhile w:
                // R27.50. A loop that changes the receiver changes it before its own
                // body runs again, so nothing inside it sees the receiver unchanged.
                // R27.50. The receiver is at its model on every iteration when nothing before
                // the loop, in an enclosing loop, or in this loop's body has changed it.
                _pristineLoops.Push(RegionOwner && (_pristineLoops.Count == 0 || _pristineLoops.Peek()) &&
                                    !_receiverDirty && !DirtiesReceiver(w.Body));
                if (DirtiesReceiver(w)) _receiverDirty = true;
                var renamed = _receiverRenamed;
                try { While(w, plan); } finally { _pristineLoops.Pop(); _receiverRenamed = renamed; }
                return;

            case IrGhostStmt g:
                Ghost(g, plan);
                return;

            case IrExprStmt { Expr: IrCall { DoesNotReturn: true } dnr }:
                // R22.11. The call raises or diverges, so what this method holds goes back
                // first, exactly as at a `throw`; the callee's `ensures false` then makes
                // the rest of the block unreachable, whatever it expects to hold.
                DoesNotReturnCall(dnr, plan);
                Line("unreachable ();");
                return;

            case IrExprStmt { Expr: IrCall rc } when RaisesThroughOpenRegion(rc) is { } held:
                RaisingRegionCall(rc, held, plan);
                return;

            case IrArrayOp c:
            {
                var args = Operands(c.Args);
                var fn = c.Op switch
                {
                    ArrayOpKind.Copy => "copy",
                    ArrayOpKind.CopyAt => "copy_at",
                    ArrayOpKind.Move => "move",
                    ArrayOpKind.Clear => "clear",
                    ArrayOpKind.Sort => "sort",
                    ArrayOpKind.CopyFrom => "copy_to",
                    _ => "reverse",
                };
                var module = c.Op switch
                {
                    ArrayOpKind.Sort => "Pulse.Lib.CSharp.Sort",
                    ArrayOpKind.CopyFrom => "Pulse.Lib.CSharp.Enumerable",
                    _ => "Pulse.Lib.CSharp.Array",
                };
                WithArrays(c.Args.Zip(args, (e, t) => (e, t)).Where(p => p.e.Type is IrArrayType),
                    () => Line($"{module}.{fn} {string.Join(" ", args)};"));
                return;
            }
            case IrExprStmt e:
                // R27.31. A discarded result is bound to `_`: Pulse rejects a statement
                // whose value is not `unit`.
                Line(e.Expr.Type is null or IrPrim { Kind: PrimKind.Void }
                    ? Expr(e.Expr) + ";"
                    : $"let _ = {Expr(e.Expr)};");
                return;

            case IrReturn r:
                diagnostics.Unsupported(r.Loc, "A `return` in this position");
                return;

            case IrThrow th:
                Throw(th, plan, tail: false);
                return;

            case IrTry tr:
                Try(tr, plan);
                return;

            case IrBreak b2:
                if (_escape?.Break is { } brkCell) Line($"{brkCell} := true;");
                else diagnostics.Unsupported(b2.Loc, "`break` outside a loop");
                if (_escape?.Continue is { } brkEsc) Line($"{brkEsc} := true;");
                return;

            case IrContinue c2:
                if (_escape?.Continue is { } contCell) Line($"{contCell} := true;");
                else diagnostics.Unsupported(c2.Loc, "`continue` outside a loop");
                return;

            default:
                diagnostics.Unsupported(stmt.Loc, $"`{stmt.GetType().Name}`");
                return;
        }
    }

    /// <summary>
    /// R5.10. A statement sequence, with the escape guard threaded through it.
    ///
    /// <para>Pulse has no <c>break</c> and no <c>continue</c>, so the *remainder* of a
    /// sequence after a statement that may escape is emitted under a test of the escape
    /// flags. The rewrite is compositional — it looks only at the statement in hand and
    /// the statements after it — and it is inserted only where <see cref="MayEscape"/>
    /// holds, so a loop without <c>break</c> or <c>continue</c> is emitted exactly as
    /// before.</para>
    /// </summary>
    private void Sequence(ImmutableArray<IrStmt> statements, MethodPlan plan)
    {
        for (var k = 0; k < statements.Length; k++)
        {
            Statement(statements[k], plan);

            var rest = statements.RemoveRange(0, k + 1);
            if (rest.IsEmpty || _escape is null || !MayEscape(statements[k])) continue;

            Line($"if ({EscapeTest()}) {{");
            _indent++;
            Sequence(rest, plan);
            Line("()");
            _indent--;
            Line("} else { () };");
            return;
        }
    }

    /// <summary>
    /// Emits the reads of the escape flags and returns the pure test meaning
    /// "this iteration has not escaped". The flags are read into `let`-bound names because
    /// a Pulse <c>if</c> condition must be pure.
    /// </summary>
    private string EscapeTest()
    {
        var parts = new List<string>();
        foreach (var cell in new[] { _escape!.Break, _escape.Continue })
        {
            if (cell is null) continue;
            var t = Fresh();
            Line($"let {t} = !{cell};");
            parts.Add($"not {t}");
        }
        return string.Join(" && ", parts);
    }

    /// <summary>
    /// Whether <paramref name="stmt"/> can transfer control out of the sequence it is in.
    /// The walk deliberately stops at a nested loop, whose own <c>break</c> and
    /// <c>continue</c> bind to that loop.
    /// </summary>
    private static bool MayEscape(IrStmt stmt) => stmt switch
    {
        IrBreak or IrContinue => true,
        IrBlock b => b.Statements.Any(MayEscape),
        IrIf i => MayEscape(i.Then) || (i.Else is not null && MayEscape(i.Else)),
        _ => false,
    };

    /// <summary>
    /// R6.11a. A local initialised with a fresh array — <c>new T[n]</c>, or R20.6's sort —
    /// owns that array. It is bound immutably to the array itself, so the resource is
    /// named by the local, and is discarded where the local goes out of scope, exactly as
    /// R4.14 discards an object local. Reassigning it is refused (PALCS0623): the array
    /// it owned would be lost with nothing to discard it.
    /// </summary>
    private void ArrayLocal(IrLocalDecl d)
    {
        var binder = Names.Local(d.Name);
        if (d.Init is IrNewArray first && Reassigned(d))
        {
            // R34.10. A cell holding the array, owned with it.
            var t = Fresh();
            Line($"let {t} = {NewArray(first)};");
            Line($"let mut {binder} = {t};");
            Line($"Pulse.Lib.CSharp.ArrayCell.intro {binder};");
            var cell = new Slot(d.Name, d.Type, SlotKind.ArrayCell, binder);
            _slots[d.Name] = cell;
            _objectLocals.Add(cell);
            if (_closingBlocks > 0) _nestedArrays[cell] = d.Loc;
            return;
        }
        switch (d.Init)
        {
            case IrNewArray na:
                Line($"let {binder} = {NewArray(na)};");
                break;
            case IrOrderBy ob:
                Line($"let {binder} = Linq.order_by_to_list {Expr(ob.Source)} {ob.Key} {OrderOf(ob.KeyType)};");
                break;
        }
        var local = new Slot(d.Name, d.Type, SlotKind.Array, binder);
        _slots[d.Name] = local;
        _objectLocals.Add(local);
        // R22.17. In a nested block the array must have been moved into a field (R22.12)
        // by the time the block closes; Scoped checks that it was.
        if (_closingBlocks > 0) _nestedArrays[local] = d.Loc;
    }

    /// <summary>R34.10. The slot of a reassigned array local, when <paramref name="v"/> is one.</summary>
    private Slot? ArrayCellOf(IrVar v) =>
        _slots.TryGetValue(v.Name, out var s) && s.Kind == SlotKind.ArrayCell ? s : null;

    /// <summary>R34.10. Whether the method assigns the local <paramref name="name"/> after declaring it.</summary>
    private bool Reassigned(IrLocalDecl d)
    {
        if (_method?.Body is not { } body) return false;
        // What follows the declaration in its block is its scope; another local of the
        // same name in a sibling block is another local.
        var scope = Passes.Check.Statements(body).OfType<IrBlock>()
            .FirstOrDefault(b => b.Statements.Any(st => ReferenceEquals(st, d))) is { } home
            ? home.Statements.SkipWhile(st => !ReferenceEquals(st, d)).Skip(1)
                .SelectMany(Passes.Check.Statements)
            : Passes.Check.Statements(body);
        return scope.Any(st => st is IrAssign { Target: IrVar v } && v.Name == d.Name);
    }

    /// <summary>R5.2. Every C# local is a Pulse <c>ref</c> cell.</summary>
    private void LocalDeclaration(IrLocalDecl d)
    {
        var cell = Names.Local(d.Name);
        var init = d.Init is null ? Default(d.Type) : Expr(d.Init);
        var nullableArray = d.Type is IrArrayType && d.Init is not null && IsNullableArray(d.Init);
        if (d.Immutable)
        {
            // A value that is already a read's binder is named by it: a second `let` would
            // be a binder Pulse's prover cannot see through, and a branch that mentions it
            // could not be joined (R26.4).
            if (System.Text.RegularExpressions.Regex.IsMatch(init, @"^t[0-9]+$"))
            {
                _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Value, init)
                {
                    NullableArray = nullableArray,
                };
                return;
            }
            _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Value, cell)
            {
                NullableArray = nullableArray,
            };
            Line($"let {cell} = {init};");
            return;
        }
        _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Cell, cell)
        {
            NullableArray = nullableArray,
        };
        // R27.20. A region pointer declared without a value starts as `null`: C#'s definite
        // assignment makes every read see a value assigned since, which F* then proves non-null.
        if (d.Init is null && d.Type is IrClassType { Nullable: false } unset && IsRegionType(unset))
        {
            Line($"let mut {cell} : {Types.Render(unset with { Nullable = true })} = B.null;");
            return;
        }
        // A type parameter's default leaves its dictionary to be resolved, and a cell's type
        // is inferred from its initialiser; the annotation resolves it first (R26.2's cell).
        // A tuple's universe is likewise inferred, and `let mut` needs it to be zero.
        Line(init.StartsWith("(Pulse.Lib.CSharp.Inhabited.default_of", StringComparison.Ordinal) ||
             d.Type is IrUserSpecType { FStar: Frontend.WellKnown.TupleType } ||
             // R27.42. An iterator's trace starts as `Seq.empty`, whose element type is implicit.
             d.Type is IrSeqType ||
             // R27.37. The struct a borrowing constructor builds is passed by reference to
             // its writer members, which take a reference to the (refined) struct type.
             d.Name == Frontend.BorrowContext.SelfCell ||
             // R32.12. So is the copy of a wrapped struct a writer member is passed.
             d.Name.StartsWith("__pal_inner", StringComparison.Ordinal)
            ? $"let mut {cell} : {Types.Render(d.Type)} = {init};"
            : $"let mut {cell} = {init};");
    }

    /// <summary>
    /// R27.41. A borrowing struct held in a local. The constructor hands each owned object
    /// over under the struct's field (R27.37); the object is held from here on in a local
    /// of its own, which the struct's members are passed, and dropped with the method's
    /// other object locals. The rewrite is pure: the local is the field's value.
    /// </summary>
    private void HeldStruct(IrLocalDecl d)
    {
        if (_closingBlocks > 0 || d.Init is null || d.Type is not IrNamedType structType)
        {
            diagnostics.Unsupported(d.Loc, $"The borrowing struct local `{d.Name}` here",
                "R27.41 holds a borrowing struct in a local of the method's own block.");
            return;
        }
        if (d.HeldOwner is { } peer) HoldPeerAtHeaps(peer, d.Loc);
        var t = Fresh();
        if (d.Init is IrCall { Kind: CalleeKind.Method } call) Call(call, t);
        else Line($"let {t} = {Expr(d.Init)};");
        foreach (var (field, local, type) in d.Owned)
        {
            var binder = Names.Local(local);
            var proj = $"({t}.{Names.Projection(structType.Name, field)})";
            var slot = new Slot(local, type, SlotKind.Object, binder);
            var m = FreshValue(local);
            Line($"let {binder} = {proj};");
            Line($"with {m}. assert ({(slot with { Binder = proj }).Resource(m)});");
            Line($"rewrite ({(slot with { Binder = proj }).Resource(m)}) as ({slot.Resource(m)});");
            _slots[local] = slot;
            _objectLocals.Add(slot);
        }
        var cell = Names.Local(d.Name);
        _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Cell, cell);
        Line($"let mut {cell} : {Types.Render(d.Type)} = {t};");
    }

    /// <summary>
    /// R27.49. Another object of the receiver's class, of which the method holds a borrowing
    /// struct, is held from here on at its heaps (<c>class_C__to_heap</c>), named as they are
    /// now, so the struct's facts about them survive the calls of its members. The epilogue
    /// gives the plain invariant back (<see cref="CloseObjects"/>).
    /// </summary>
    private void HoldPeerAtHeaps(string peer, IrLoc loc)
    {
        if (!_slots.TryGetValue(peer, out var slot) ||
            slot is not { Kind: SlotKind.Object, Type: IrClassType { Nullable: false } oc, Index: null, ViewBase: null } ||
            _objects.Any(o => o.Name == peer) || !classes!.TryGetValue(oc.Name, out var decl))
        {
            diagnostics.Unsupported(loc, $"A borrowing struct of `{peer}` here",
                "R27.49 holds a struct of a parameter the method holds closed, at the parameter's class type.");
            return;
        }
        if (!slot.Heaps.IsEmpty) return;
        var regions = RegionsOf(decl).ToList();
        if (regions.Count == 0) return;
        var hs = regions.Select(k => FreshValue(Frontend.Region.HeapBinder(k.Name))).ToList();
        Line($"{Names.ClassModule(oc.Name)}.{Names.ClassToHeap(oc.Name)} {slot.Binder};");
        Line($"with {string.Join(" ", hs)}. assert ({InvHeap(oc)} {slot.Binder} {slot.PermArg}{slot.PreModel} {string.Join(" ", hs)});");
        var held = slot with { Heaps = [.. regions.Select((k, i) => (k, hs[i], hs[i]))] };
        _slots[peer] = held;
        _heldPeers.Add(held);
        for (var i = 0; i < regions.Count; i++)
            _plan!.PreScope.Bind(Frontend.Region.HeapNameOf(regions[i].Name, peer), new Term(hs[i], TermKind.Other));
    }

    private readonly List<Slot> _heldPeers = [];

    /// <summary>
    /// R22.10. <c>new T[n]</c>. A literal zero length needs no element to fill with, so it
    /// is <c>alloc_empty</c>: a generic class's empty array is then no reason to ask the
    /// caller for a <c>default(T)</c>.
    /// </summary>
    private string NewArray(IrNewArray na) => na switch
    {
        // R23.4. `Array.Resize(ref a, n)`: a fresh array holding `a`'s first cells.
        { Source: { } src } => $"Pulse.Lib.CSharp.QueueStack.resize {Expr(src)} {Expr(na.Length)}",
        { Length: IrLiteral { Value: 0 or 0L } } => $"alloc_empty #({Types.Render(na.Element)}) ()",
        _ => $"alloc {Expr(na.Length)} {Default(na.Element)}",
    };

    private static string Default(IrType type) => type switch
    {
        IrPrim { Kind: PrimKind.Bool } => "false",
        IrPrim p when p.IsMachineInt => Types.Literal(0, p),
        _ => $"(Pulse.Lib.CSharp.Inhabited.default_of ({Types.Render(type)}))",
    };

    /// <summary>R5.3.</summary>
    private void Assign(IrAssign a)
    {
        Adopt(a);
        switch (a.Target)
        {
            // R34.10. `Array.Resize(ref arr, n)` on a reassigned array local.
            case IrVar v when ArrayCellOf(v) is { } resized:
                if (a.Value is IrNewArray { Source: IrVar src } grown && src.Name == v.Name)
                    Line($"Pulse.Lib.CSharp.ArrayCell.resize {resized.Binder} {Expr(grown.Length)};");
                else if (a.Value is IrNewArray fresh && fresh.Source is null)
                {
                    var t = Fresh();
                    Line($"let {t} = {NewArray(fresh)};");
                    Line($"Pulse.Lib.CSharp.ArrayCell.release {resized.Binder};");
                    Line($"{resized.Binder} := {t};");
                    Line($"Pulse.Lib.CSharp.ArrayCell.intro {resized.Binder};");
                }
                else
                    diagnostics.Error("PALCS0863", a.Loc,
                        $"`{v.Name}` is an array local that is reassigned (doc/translation.md R34.10). " +
                        "It may be assigned only a fresh array, `new T[n]` or `Array.Resize(ref " + v.Name + ", n)`.");
                return;

            case IrElement { Array: IrVar wv } wel when ArrayCellOf(wv) is { } wcell:
            {
                var index = Expr(wel.Index);
                var value = Expr(a.Value);
                Line($"Pulse.Lib.CSharp.ArrayCell.write {wcell.Binder} {index} {value};");
                return;
            }

            case IrVar v when _objectLocals.Any(l => l.Name == v.Name && l.Kind == SlotKind.Array):
                diagnostics.Error("PALCS0623", a.Loc,
                    $"`{v.Name}` owns the array it was initialised with, and assigning it " +
                    "would lose that array (doc/translation.md R6.11a). Declare another local.");
                return;

            case IrVar v when _slots.TryGetValue(v.Name, out var slot) && slot.Kind is SlotKind.Cell or SlotKind.RefParam:
                if (ReadOnly(slot, a.Loc)) return;
                Line($"{slot.Binder} := {Expr(a.Value)};");
                return;

            case IrElement { Array: IrVar av } when
                _slots.TryGetValue(av.Name, out var arr) && ReadOnly(arr, a.Loc):
                return;

            case IrElement el:
            {
                // C# evaluates the target's index before the right-hand side, so the
                // lifted bindings must appear in that order.
                var array = Expr(el.Array);
                var index = Expr(el.Index);
                var value = Expr(a.Value);
                WithArrays([(el.Array, array)], () =>
                    Line($"{(IsSpan(el.Array) ? "Span." : "")}write {array} {index} {value};"));
                return;
            }

            // R12.3. Writing a field of a `[Plain]` reference: the same write as R3.8,
            // reached by a different slot kind. This is the operation §10 could not offer
            // at all, because a derived predicate *owns* the field it folds over; here the
            // user's predicate only constrained `prev`, so overwriting it is a plain write
            // and re-closing the segment reports what the field now holds.
            case IrField { Receiver: IrVar wv } wfield when
                _slots.TryGetValue(wv.Name, out var wobj)
                && wobj is { Kind: SlotKind.Value, Type: IrClassType wc }
                && classes is not null && classes.TryGetValue(wc.Name, out var wdecl)
                && wdecl.IsPlain:
            {
                if (!Reachable(wobj, wfield.Loc, wfield.Field)) return;
                var wvalue = Inject(FieldType(wc, wfield.Field), a.Value, Expr(a.Value));
                var wcur = Fresh();
                // R27.5. A write replaces the record in the region, as R3.6 replaces it in a box.
                if (wdecl.IsRegion)
                {
                    var wrecv = wobj.NonNull;
                    Line($"let {wcur} = {Names.ClassModule(wc.Name)}.{Frontend.Region.ReadOf(wc.Name)} {wrecv};");
                    Line($"{Frontend.Region.Module}.write {wrecv} " +
                         $"({{ {wcur} with {Names.ClassProjection(wc.Name, wfield.Field)} = {wvalue} }});");
                    FieldRegionWritten(wc);
                    return;
                }
                Line($"let {wcur} = B.op_Bang {wobj.NonNull};");
                Line($"B.op_Colon_Equals {wobj.NonNull} " +
                     $"({{ {wcur} with {Names.ClassProjection(wc.Name, wfield.Field)} = {wvalue} }});");
                return;
            }

            // R27.16. Writing a field of a region object held in a mutable local: the same
            // write as R27.5, through the pointer the local holds now.
            case IrField { Receiver: IrVar cv } cfield when
                _slots.TryGetValue(cv.Name, out var cslot)
                && cslot is { Kind: SlotKind.Cell, Type: IrClassType cc }
                && classes is not null && classes.TryGetValue(cc.Name, out var cdecl)
                && cdecl.IsRegion:
            {
                var cvalue = Inject(FieldType(cc, cfield.Field), a.Value, Expr(a.Value));
                var cptr = Fresh();
                var ccur = Fresh();
                Line($"let {cptr} = !{cslot.Binder};");
                Line($"let {ccur} = {Names.ClassModule(cc.Name)}.{Frontend.Region.ReadOf(cc.Name)} {cptr};");
                Line($"{Frontend.Region.Module}.write {cptr} " +
                     $"({{ {ccur} with {Names.ClassProjection(cc.Name, cfield.Field)} = {cvalue} }});");
                FieldRegionWritten(cc);
                return;
            }

            // R27.33. Writing a field of a region object some other expression reaches
            // (`x.Left.Left = v`): the receiver is a pointer value like any other, so it is
            // evaluated first, as C# evaluates it, and written through as R27.5.
            case IrField { Receiver: not IrVar } xfield when
                xfield.Receiver.Type is IrClassType xc
                && classes is not null && classes.TryGetValue(xc.Name, out var xdecl)
                && xdecl.IsRegion:
            {
                var xptr = Fresh();
                Line($"let {xptr} = {Expr(xfield.Receiver)};");
                var xvalue = Inject(FieldType(xc, xfield.Field), a.Value, Expr(a.Value));
                var xcur = Fresh();
                Line($"let {xcur} = {Names.ClassModule(xc.Name)}.{Frontend.Region.ReadOf(xc.Name)} {xptr};");
                Line($"{Frontend.Region.Module}.write {xptr} " +
                     $"({{ {xcur} with {Names.ClassProjection(xc.Name, xfield.Field)} = {xvalue} }});");
                FieldRegionWritten(xc);
                return;
            }

            // R3.8. Writing a field of an object is a write through the box: read the
            // representation, replace one field, write it back. The record update needs a
            // pure source (F11), which is why the dereference is let-bound first.
            case IrField { Receiver: IrVar ov } field when
                _slots.TryGetValue(ov.Name, out var obj) && obj is { Kind: SlotKind.Object, Type: IrClassType oc }:
            {
                if (!Reachable(obj, field.Loc, field.Field)) return;
                string value;
                if (a.Value is IrNull && FieldType(oc, field.Field) is IrArrayType nullType &&
                    FieldDecl(oc, field.Field) is { IsNullableArray: true })
                {
                    value = Fresh();
                    Line($"let {value} = NA.alloc_null ({Types.Render(nullType.Element)}) ();");
                }
                else
                    value = Inject(FieldType(oc, field.Field), a.Value, Expr(a.Value));
                var current = Fresh();
                Line($"let {current} = B.op_Bang {obj.NonNull};");
                if (FieldType(oc, field.Field) is IrArrayType fat)
                {
                    // R22.12. The object owns the array a field holds, so replacing the
                    // array discards the old one's contents -- it is garbage to the CLR --
                    // and the new one's ownership moves from the local into the object.
                    var fdecl = FieldDecl(oc, field.Field)!;
                    var pts = PulseEmitter.ArrayPts(fdecl);
                    var projection = $"{current}.{Names.ClassProjection(oc.Name, field.Field)}";
                    var old = FreshValue(field.Field);
                    Line($"with {old}. assert ({pts} {projection} {old});");
                    Line($"drop_ ({pts} {projection} {old});");
                    if (a.Value is IrVar moved)
                    {
                        _objectLocals.RemoveAll(l => l.Name == moved.Name && l.Kind == SlotKind.Array);
                        // R33.16. Nor does a ghost statement's naming bracket still find it.
                        if (_slots.TryGetValue(moved.Name, out var ms) && ms.Kind == SlotKind.Array)
                            _slots[moved.Name] = ms with { Kind = SlotKind.Value, Index = null };
                    }
                    // R24.7. A nullable field owns what it holds through `NA.pts_to`: a
                    // non-null array moves in by `intro`, and `null` owns nothing.
                    // (`null` arrives owned, by `NA.alloc_null`.)
                    if (fdecl.IsNullableArray && a.Value is not IrNull && !IsNullableArray(a.Value))
                        Line($"NA.intro {value};");
                }
                Line($"B.op_Colon_Equals {obj.NonNull} " +
                     $"({{ {current} with {Names.ClassProjection(oc.Name, field.Field)} = {value} }});");
                return;
            }

            // R24.21. `a[i].f = v` on an array of structs: read the element, replace the
            // field, write the element back.
            case IrField efield when Normalize.ElementTarget(efield) is IrElement el:
            {
                if (el.Array is IrVar eav && _slots.TryGetValue(eav.Name, out var earr) && ReadOnly(earr, a.Loc)) return;
                var array = Expr(el.Array);
                var index = Expr(el.Index);
                var value = Expr(a.Value);
                var current = Fresh();
                WithArrays([(el.Array, array)], () =>
                {
                    Line($"let {current} = {(IsSpan(el.Array) ? "Span." : "")}read {array} {index};");
                    Line($"{(IsSpan(el.Array) ? "Span." : "")}write {array} {index} {Update(current, efield, value, a.Loc)};");
                });
                return;
            }

            // R3.6. A C# field assignment on a value type replaces the whole value, so
            // it becomes an update of the cell the value lives in.
            case IrField field when Root(field) is { } root &&
                                    _slots.TryGetValue(root.Name, out var cell) &&
                                    cell.Kind is SlotKind.Cell or SlotKind.RefParam:
            {
                if (ReadOnly(cell, a.Loc)) return;
                var value = Expr(a.Value);
                var current = Fresh();
                Line($"let {current} = !{cell.Binder};");
                Line($"{cell.Binder} := {Update(current, field, value, a.Loc)};");
                return;
            }

            default:
                diagnostics.Unsupported(a.Loc, "This assignment target");
                return;
        }
    }

    /// <summary>The local or parameter a field path is rooted at, if it is rooted at one.</summary>
    private static IrVar? Root(IrExpr expr) => expr switch
    {
        IrVar v => v,
        IrField f => Root(f.Receiver),
        _ => null,
    };

    /// <summary>
    /// R3.6. Rebuilds a value with one field path replaced. Nested paths compose: `x.f.g`
    /// updates `f` with an update of `g`. The source of a record update must be a pure
    /// term (F11), which is why the caller let-binds the dereference first.
    /// </summary>
    private string Update(string root, IrExpr target, string value, IrLoc loc)
    {
        if (target is not IrField field) return value;

        if (field.Receiver.Type is not IrNamedType named)
        {
            diagnostics.Unsupported(loc, $"The assignment target `.{field.Field}`");
            return value;
        }

        var updated =
            $"({{ {Path(root, field.Receiver, loc)} with {Names.Projection(named.Name, field.Field)} = {value} }})";
        return Update(root, field.Receiver, updated, loc);
    }

    /// <summary>The pure projection path from a root binder down to a field access.</summary>
    private string Path(string root, IrExpr expr, IrLoc loc)
    {
        if (expr is IrVar or IrElement) return root;
        if (expr is IrField f && f.Receiver.Type is IrNamedType named)
            return $"{Path(root, f.Receiver, loc)}.{Names.Projection(named.Name, f.Field)}";
        diagnostics.Unsupported(loc, "This assignment target");
        return root;
    }

    /// <summary>
    /// R4.9. A slot held at a fractional permission may be observed but not written; the
    /// permission is precisely the right to read.
    /// </summary>
    private bool ReadOnly(Slot slot, IrLoc loc)
    {
        if (slot.Fraction is null) return false;
        diagnostics.Error("PALCS0305", loc,
            $"`{slot.Name}` is held at the fractional permission `{slot.Fraction}` " +
            "and so cannot be written. Remove its `[Frac]` to take full ownership.");
        return true;
    }

    /// <summary>R5.4. Both branches are always emitted.</summary>
    private void If(IrIf i, MethodPlan plan)
    {
        if (NullTest(i.Cond) is { } window)
        {
            NullWindow(window, i, branch => { if (branch is not null) Statement(branch, plan); }, tail: false);
            Line(";");
            return;
        }

        if (i.Else is not null && i.Cond is IrBinary pnb && PlainNullTest(pnb) is { } ptest)
        {
            PlainNullWindow(ptest, i, branch => { if (branch is not null) Statement(branch, plan); }, tail: false);
            Line(";");
            return;
        }

        var cond = Expr(i.Cond);
        Line($"if ({cond}) {{");
        _indent++;
        Statement(i.Then, plan);
        Line("()");
        _indent--;
        Line("} else {");
        _indent++;
        if (i.Else is not null) Statement(i.Else, plan);
        Line("()");
        _indent--;
        Line("};");
    }

    /// <summary>
    /// R10.2b. A non-null reference where a nullable one is expected. C# calls this the
    /// identity because nullability is an annotation there, and under R10.2 the encoding
    /// agrees: `C` is `C?` under a refinement. So the *term* is unchanged. What is left is
    /// the invariant, which R10.3a states through an abbreviation Pulse's matcher does not
    /// see through (F77), so `as_opt` survives as a one-line rewrite.
    /// </summary>
    private string Inject(IrType? expected, IrExpr value, string text)
    {
        if (expected is not IrClassType { Nullable: true } k) return text;
        if (value.Type is not IrClassType { Nullable: false } nn || nn.Name != k.Name) return text;
        // R10.2 (F76). The *term* is unchanged: `class_C` is `class_C__opt` under a
        // refinement, so a non-nullable reference already is a nullable one, and C#'s
        // identity coercion is F*'s. What remains is not about the reference but about its
        // invariant, which is stated through R10.3a's abbreviation and must be unfolded.
        // R12.2. A plain reference carries no invariant, so for it there is nothing at all.
        if (classes is not null && classes.TryGetValue(k.Name, out var kd))
        {
            if (kd.IsPlain) return text;
            // R31.2. Nor has any class that is not recursive (a ring's owner): R10.3a's
            // abbreviation is only a recursive class's.
            if (kd.Recursion is null) return text;
        }
        Line($"{Names.ClassModule(k.Name)}.{Names.ClassAsOpt(k.Name)} {text};");
        return text;
    }

    /// <summary>R12.4. The record an allocation boxes.</summary>
    private string AllocRecord(IrAlloc al)
    {
        var flds = al.Record.Fields.Select((f, i) =>
            (i == 0 ? Names.ClassProjection(al.Class, f.Field) : Names.Field(f.Field))
            + " = " + Inject(f.FieldType, f.Value, Expr(f.Value)));
        return "({ " + string.Join("; ", flds) + " })";
    }

    private IrFieldDecl? FieldDecl(IrClassType owner, string field) =>
        classes is not null && classes.TryGetValue(owner.Name, out var decl)
            ? decl.Fields.FirstOrDefault(f => f.Name == field)
            : null;

    /// <summary>
    /// R24.7. Whether an array expression denotes an array owned through
    /// <c>NA.pts_to</c>: a nullable field, or a local that was initialised from one.
    /// </summary>
    private bool IsNullableArray(IrExpr e) => e switch
    {
        IrField { Receiver: IrVar rv } f =>
            _slots.TryGetValue(rv.Name, out var o) && o.Type is IrClassType k &&
            FieldDecl(k, f.Field) is { IsNullableArray: true },
        IrVar v => _slots.TryGetValue(v.Name, out var slot) && slot.NullableArray,
        _ => false,
    };

    /// <summary>
    /// R24.7. Brackets an operation on an array owned through <c>NA.pts_to</c>: the
    /// ordinary operation needs <c>A.pts_to</c>, which <c>elim</c> gives back for a
    /// non-null array -- the obligation the C# null test discharges.
    /// </summary>
    /// <summary>
    /// R29.5. The operands of an array primitive, evaluated left to right. An operand that
    /// reads an array field of an object (<c>_dict.keys</c>) and is followed by a call
    /// (<c>_dict.Count</c>) names the array through a record read before that call, while
    /// the call refolds the object's invariant and the next unfold names a fresh one; the
    /// array's permission is then stated about a record Pulse cannot relate to the first.
    /// The field is therefore read again after the last operand. That is the value C# read
    /// exactly when nothing in between can have written the object's box, and the rereading
    /// is done only then: every call among the later operands is a read-only instance call
    /// (R4.11b: held at an arbitrary fraction, so it cannot write) whose other arguments
    /// hold no reference, and none of them runs statements of its own.
    /// </summary>
    private List<string> Operands(IReadOnlyList<IrExpr> operands)
    {
        var texts = operands.Select(a => Atom(Expr(a))).ToList();
        for (var i = 0; i < operands.Count; i++)
        {
            if (operands[i] is not IrField { Receiver: IrVar ov, Type: IrArrayType } f
                || !_slots.TryGetValue(ov.Name, out var obj)
                || obj is not { Kind: SlotKind.Object, Type: IrClassType oc }) continue;
            var later = operands.Skip(i + 1).SelectMany(Check.Subexpressions).ToList();
            var calls = later.OfType<IrCall>().ToList();
            if (calls.Count == 0) continue;
            var readOnly = calls.All(k => k.HasReceiver && !k.MutatesReceiver
                    && k.Args.Skip(1).All(a => a.Type is not (IrClassType or IrArrayType)))
                && !later.Any(e => e is IrStmtExpr or IrRaise);
            if (!readOnly) continue;
            var t = Fresh();
            Line($"let {t} = B.op_Bang {obj.NonNull};");
            texts[i] = $"{t}.{Names.ClassProjection(oc.Name, f.Field)}";
        }
        return texts;
    }

    private void WithArrays(IEnumerable<(IrExpr Expr, string Text)> arrays, Action op)
    {
        var nullable = arrays.Where(a => IsNullableArray(a.Expr)).Select(a => a.Text).Distinct().ToList();
        foreach (var a in nullable) Line($"NA.elim {a};");
        op();
        foreach (var a in nullable) Line($"NA.intro {a};");
    }

    private IrType? FieldType(IrClassType owner, string field) =>
        classes is not null && classes.TryGetValue(owner.Name, out var decl)
            ? decl.Fields.FirstOrDefault(f => f.Name == field)?.Type
            : null;

    /// <summary>
    /// R10.8. Whether the representation behind a reference is reachable here. For a
    /// non-null reference it always is; for a nullable one it is exactly inside the window
    /// R10.7 opens, because that is where the head cell has been given up. Refusing the
    /// rest is not the emitter inventing a refusal: outside a window the reference is still
    /// an `option` and there is no record to project.
    /// </summary>
    private bool Reachable(Slot obj, IrLoc loc, string field)
    {
        if (obj.Type is not IrClassType { Nullable: true } k || obj.Window) return true;
        // R12.3c. For a `[Plain]` class there is no derived invariant and so no window: §12
        // gave the ownership of the record to the user's predicate, and whether it is held
        // here is that predicate's business, not the emitter's. So the projection is
        // emitted and Pulse checks the non-null refinement against whatever the user's
        // annotations establish — a loop guard, a lemma, an `if`. Refusing it here would be
        // the emitter inventing a refusal (§0 rule 3): it would rule out every cursor, and
        // a cursor's null test is a *loop condition*, which no window can be the extent of.
        if (classes is not null && classes.TryGetValue(k.Name, out var d) && d.IsPlain) return true;
        diagnostics.Error("PALCS0567", loc,
            $"`{obj.Name}.{field}` reads through a reference that may be null. A field behind a " +
            "nullable class reference is reachable only inside a null test — write `if (" + obj.Name +
            " == null) { … } else { … }` and reach the field in the `else` branch " +
            "(doc/translation.md R10.7).");
        return false;
    }

    /// <summary>
    /// R12.3. The operand of an <c>== null</c> / <c>!= null</c> test whose static type is a
    /// nullable <c>[Plain]</c> class, or <c>null</c> when this is not such a test.
    /// </summary>
    private (IrExpr Tested, Slot? Slot, bool ThenIsNull)? PlainNullTest(IrBinary b)
    {
        if (b.Op is not (BinOp.Eq or BinOp.Ne)) return null;
        var tested = b.Left is IrNull ? b.Right : b.Right is IrNull ? b.Left : null;
        if (tested?.Type is not IrClassType k) return null;
        if (classes is null || !classes.TryGetValue(k.Name, out var decl) || !decl.IsPlain) return null;
        // R27.8. A region pointer typed non-null is still tested: the test is a pointer test.
        if (!k.Nullable && !decl.IsRegion) return null;
        Slot? slot = null;
        if (tested is IrVar v && _slots.TryGetValue(v.Name, out var s) && s.Kind is SlotKind.Value)
            slot = s;
        return (tested, slot, b.Op is BinOp.Eq);
    }

    /// <summary>
    /// R12.3. The bracket R10.7 puts around a null test, with every proof step taken out.
    /// §12 derived no predicate for a <c>[Plain]</c> class, so there is nothing to case
    /// split and no lemma the emitter would be entitled to place; what remains is the
    /// branch itself and the one fact the branch establishes — that in the <c>else</c>
    /// arm the reference is non-null, so the record behind it can be projected. Whether
    /// that projection is <em>owned</em> is the user's predicate's business, and a missing
    /// <c>pts_to</c> is a failure in their annotations rather than in the translation.
    /// </summary>
    private void PlainNullWindow(
        (IrExpr Tested, Slot? Slot, bool ThenIsNull) test, IrIf i,
        Action<IrStmt?> branch, bool tail)
    {
        var opt = Expr(test.Tested);
        var nullBranch = test.ThenIsNull ? i.Then : i.Else;
        var otherBranch = test.ThenIsNull ? i.Else : i.Then;

        Line($"if (B.is_null {opt}) {{");
        _indent++;
        branch(nullBranch);
        if (!tail) Line("()");
        _indent--;
        Line("} else {");
        _indent++;
        var saved = test.Slot is null ? null : _slots[test.Slot.Name];
        if (saved is not null) _slots[saved.Name] = saved with { Window = true };
        try
        {
            branch(otherBranch);
            if (!tail) Line("()");
        }
        finally
        {
            if (saved is not null) _slots[saved.Name] = saved;
        }
        _indent--;
        Line("}");
    }

    /// <summary>
    /// R10.7. A null test on a recursive object, which is where §10 puts the case lemmas.
    /// Returns the slot tested, its class, and whether the <c>then</c> branch is the null
    /// one — nothing else in the emitter needs to know what a recursive class is.
    /// </summary>
    private (Slot Slot, IrClassType Type, bool ThenIsNull)? NullTest(IrExpr cond)
    {
        if (cond is not IrBinary { Op: BinOp.Eq or BinOp.Ne } b) return null;
        var tested = b.Left is IrNull ? b.Right : b.Right is IrNull ? b.Left : null;
        if (tested is not IrVar v || !_slots.TryGetValue(v.Name, out var slot)) return null;
        if (slot.Kind is not SlotKind.Object || slot.Type is not IrClassType { Nullable: true } k) return null;
        if (classes is null || !classes.TryGetValue(k.Name, out var decl) || decl.Recursion is null)
            return null;
        return (slot, k, b.Op is BinOp.Eq);
    }

    /// <summary>
    /// R10.7. The whole of §10's proof placement, and the reason the user writes no ghost
    /// code: the <c>if (n == null)</c> they had to write anyway <em>is</em> the case split
    /// on the model. <c>cases</c> connects the two before the test; the null branch learns
    /// the model is empty; the other branch opens the head cell, runs, and closes it again.
    ///
    /// <para>It is the same bracket R4.10 puts around a receiver, at a different place —
    /// around the branch a null test already delimits rather than around a whole body — and
    /// the field access inside it is the same rule, because the slot is rebound to the
    /// non-null reference for exactly the extent of the branch.</para>
    /// </summary>
    private void NullWindow(
        (Slot Slot, IrClassType Type, bool ThenIsNull) window, IrIf i,
        Action<IrStmt?> branch, bool tail)
    {
        var (slot, klass, thenIsNull) = window;
        var mod = Names.ClassModule(klass.Name);
        var opt = slot.Binder;
        var nullBranch = thenIsNull ? i.Then : i.Else;
        var consBranch = thenIsNull ? i.Else : i.Then;

        Line($"{mod}.{Names.ClassCases(klass.Name)} {opt};");
        Line($"if (B.is_null {opt}) {{");
        _indent++;
        // R10.4b. Preserving or consuming, read off the contract: a method that gave the
        // object away (R4.9c) owes nothing back, and leaving the empty invariant behind
        // would be a leftover resource.
        var nil = slot.Consumed ? Names.ClassElimNil(klass.Name) : Names.ClassNilCase(klass.Name);
        Line($"{mod}.{nil} {opt};");
        branch(nullBranch);
        if (!tail) Line("()");
        _indent--;
        Line("} else {");
        _indent++;
        Line($"{mod}.{Names.ClassElimCons(klass.Name)} {opt};");

        // Inside the window the reference is known non-null, so every rule that reaches a
        // field through a box applies unchanged — the slot names the box rather than the
        // option, and R3.8's read and R3.12's write need no case for recursion.
        var saved = _slots[slot.Name];
        _slots[slot.Name] = saved with { Window = true };
        _windows.Add($"{mod}.{Names.ClassIntroCons(klass.Name)} {opt};");
        try
        {
            branch(consBranch);
            if (!tail)
            {
                Line(_windows[^1]);
                Line("()");
            }
        }
        finally
        {
            _windows.RemoveAt(_windows.Count - 1);
            _slots[slot.Name] = saved;
        }
        _indent--;
        Line(tail ? "}" : "}");
    }

    /// <summary>R26.10. Whether the loop assigns the local <paramref name="name"/> itself.</summary>
    private static bool Rebinds(IrWhile w, string name)
    {
        var stmts = Passes.Check.Statements(w.Body).Concat(w.Step.SelectMany(Passes.Check.Statements)).ToList();
        if (stmts.Any(st => st is IrAssign { Target: IrVar v } && v.Name == name)) return true;
        var exprs = stmts.SelectMany(Passes.Check.Expressions).Append(w.Cond)
            .SelectMany(Passes.Check.Subexpressions);
        return exprs.Any(e => e is IrRefArg { Operand: IrVar v } && v.Name == name);
    }

    /// <summary>R5.6, R5.8, R5.8b, R5.9.</summary>
    private void While(IrWhile w, MethodPlan plan)
    {
        // R5.12. The unfolded receiver is not among the ordinary live slots: inside R4.10's
        // window it is a representation, not an object, and its folded invariant is exactly
        // the thing that does not hold here.
        var live = w.Live.Where(n => _slots.TryGetValue(n, out var s) && s.Owns)
            .Select(n => _slots[n])
            .Where(s => !_objects.Any(o => o.Name == s.Name))
            .ToImmutableArray();
        var unassigned = w.Unassigned.ToImmutableHashSet();
        // R26.10. A local holding an array -- `var nodes = _nodes;` -- is a cell holding a
        // reference. Writing an element changes the array, which is owned elsewhere, and
        // not the cell, so the reference stays known to be the one the loop started with.
        foreach (var slot in live)
            if (slot.Kind == SlotKind.Cell && slot.Type is IrArrayType &&
                !unassigned.Contains(slot.Name) && !Rebinds(w, slot.Name))
                unassigned = unassigned.Add(slot.Name);
        // R33.28. An object whose fields the loop writes changes its model.
        foreach (var slot in live)
            if (slot.Kind == SlotKind.Object && unassigned.Contains(slot.Name) &&
                Check.Statements(w.Body).Any(st => PeerTarget(st) is { Receiver: IrVar pv } && pv.Name == slot.Name))
                unassigned = unassigned.Remove(slot.Name);

        // Name the values the loop will *not* change, so the invariant can say they are
        // unchanged rather than merely existentially quantified (R5.8b). Values the loop
        // does change are named too, because a ghost statement in the body may need them.
        var fixedNames = new Dictionary<string, string>();
        var existentials = ImmutableArray.CreateBuilder<string>();
        var resources = ImmutableArray.CreateBuilder<string>();
        var scope = new SpecScope(plan.PreScope) { Pre = plan.PreScope };

        var measureScope = DerefScope();
        var stillHeaps = new List<string>();
        // R27.41. A receiver held at its heaps that the method has not opened (it only
        // passes itself to calls, as to a borrowing struct's members) is carried at them.
        for (var i = 0; i < live.Length; i++)
        {
            if (live[i] is not { Kind: SlotKind.Object, Heaps.IsDefaultOrEmpty: false, Open: false } held) continue;
            var still = unassigned.Contains(held.Name);
            var heaps = new List<string>();
            foreach (var h in held.Heaps)
            {
                var hv = FreshValue(Frontend.Region.HeapBinder(h.Region.Name));
                heaps.Add(hv);
                if (!still) existentials.Add(hv);
                else stillHeaps.Add(hv);
                scope.Bind(Frontend.Region.HeapNameOf(h.Region.Name, held.Name), new Term(hv, TermKind.Other));
                measureScope.Bind(Frontend.Region.HeapNameOf(h.Region.Name, held.Name), still
                    ? new Term(hv, TermKind.Other)
                    : new Term($"({Frontend.Region.Module}.current #({PulseEmitter.RegionRaw(h.Region)}) ())", TermKind.Other));
            }
            live = live.SetItem(i, held with { LoopHeaps = [.. heaps] });
        }
        foreach (var slot in live)
        {
            var value = FreshValue(slot.Name);
            fixedNames[slot.Name] = value;
            if (!unassigned.Contains(slot.Name)) existentials.Add(value);
            resources.Add(slot.Resource(value));
            scope.Bind(slot.Name, new Term(value, MethodPlan.KindOf(slot.Type), slot.Type));
            // R27.41. An object the loop leaves alone is at its fixed model in the measure too.
            if (slot is { Kind: SlotKind.Object, LoopHeaps.IsDefaultOrEmpty: false } && unassigned.Contains(slot.Name))
                measureScope.Bind(slot.Name, new Term(value, MethodPlan.KindOf(slot.Type), slot.Type));
            // R27.43. An object the loop changes is at the model its invariant holds now.
            else if (slot is { Kind: SlotKind.Object, Open: false, Index: null, LoopHeaps.IsDefaultOrEmpty: true, Type: IrClassType oc })
                measureScope.Bind(slot.Name, new Term(
                    $"(Pulse.Lib.CSharp.Callback.model_now ({Names.ClassModule(oc.Name)}.{Names.ClassInv(oc.Name)} {slot.Binder} #{slot.Fraction ?? "1.0R"}) ())",
                    MethodPlan.KindOf(slot.Type), slot.Type));
        }

        // R24.22. A name that owns nothing -- an immutable local, a ghost local -- holds
        // one value for the whole loop, and the invariant may mention it as such.
        foreach (var (name, slot) in _slots)
            if (!slot.Owns && !_objects.Any(o => o.Name == name) && !scope.TryGet(name, out _))
                scope.Bind(name, new Term(slot.Binder, MethodPlan.KindOf(slot.Type), slot.Type));

        // R5.12. Everything R4.10 opened has to be carried across the loop.
        var pure = ImmutableArray.CreateBuilder<string>();
        var repFixed = new List<(string Name, string Resource)>();
        foreach (var receiver in _objects)
            Representation(receiver, w.Body, scope, measureScope, resources, existentials, pure, repFixed);

        // R27.31. A region the method holds itself (R27.16) and an `[Open]` receiver's
        // heaps (R27.23) are carried across the loop as an owner's region is (R27.4), and
        // an `[Open]` receiver's fields are read from its record as the loop holds it.
        var carried = plan.Held
            .Select(u => (Region: u.Region,
                          Perm: u.Mutates ? "1.0R" : "p_" + Frontend.Region.HeapBinder(u.Region.Name)))
            .Concat(live.Where(s => s.Open).SelectMany(s => s.OpenHeaps.Select(k => (Region: k, Perm: "1.0R"))));
        foreach (var (k, perm) in carried)
        {
            var heap = FreshValue(Frontend.Region.HeapBinder(k.Name));
            var regionResource = PulseEmitter.RegionAt(k, perm, heap);
            resources.Add(regionResource);
            var still = !WritesRegion(w.Body, k.Name);
            if (still) repFixed.Add((heap, regionResource));
            else existentials.Add(heap);
            scope.Bind(Frontend.Region.HeapName(k.Name), new Term(heap, TermKind.Other));
            measureScope.Bind(Frontend.Region.HeapName(k.Name), still
                ? new Term(heap, TermKind.Other)
                : new Term($"({Frontend.Region.Module}.current #({PulseEmitter.RegionRaw(k)}) ())", TermKind.Other));
        }
        foreach (var slot in live.Where(s => s is { Open: true, Type: IrClassType }))
        {
            var oc = (IrClassType)slot.Type;
            var (_, written) = ReceiverWrites(w.Body);
            foreach (var f in slot.OpenFields)
            {
                var at = $"{fixedNames[slot.Name]}.{Names.ClassProjection(oc.Name, f.Name)}";
                // R33.15. An array field is carried by its own `pts_to`, at contents the
                // loop holds fixed unless it writes the array.
                if (f.Type is IrArrayType)
                {
                    var c = FreshValue(Names.Contents(f.Name));
                    var res = $"{PulseEmitter.ArrayPts(f)} {at} {c}";
                    resources.Add(res);
                    // A fixed contents names the record it is reached from, so it can be
                    // fixed only while the record is.
                    if (written.Contains(f.Name) || written.Contains(AnyArray) || !unassigned.Contains(slot.Name))
                        existentials.Add(c);
                    else repFixed.Add((c, res));
                    scope.Bind($"{Names.This}.{f.Name}", new Term(c, TermKind.Seq, f.Type));
                    scope.Bind(SpecEmitter.ArrayRefKey($"{Names.This}.{f.Name}"), new Term(at, TermKind.Other, f.Type));
                    continue;
                }
                scope.Bind($"{Names.This}.{f.Name}", new Term(at, MethodPlan.KindOf(f.Type), f.Type));
            }
        }

        // R5.8b, and R5.12 with it: a binder the loop cannot change is *named* before the
        // loop rather than existentially quantified inside it, so that what comes out is
        // known to be what went in. For the receiver that is not an optimisation — a
        // read-only method re-folds its invariant at the model it was handed (R4.11a), and
        // an existentially quantified representation could not possibly satisfy it.
        var fixedAll = repFixed
            .Concat(live.Where(s => unassigned.Contains(s.Name))
                        .Select(s => (Name: fixedNames[s.Name], Resource: s.Resource(fixedNames[s.Name]))))
            .ToList();
        // R33.20. An `[Open]` receiver the loop changes keeps, across it, the fields that
        // neither the loop nor an `[Open]` callee of it assigns.
        foreach (var slot in live.Where(s => s is { Open: true, Type: IrClassType } && !unassigned.Contains(s.Name)))
        {
            if (MethodPlan.OpenAssigned(w.Body, methods, []) is not { } loopAssigned) continue;
            var kept = slot.OpenFields.Where(f => !loopAssigned.Contains(f.Name)).ToList();
            if (kept.Count == 0) continue;
            var before = FreshValue(slot.Name);
            Line($"with {before}. assert ({slot.Resource(before)});");
            var oc = (IrClassType)slot.Type;
            foreach (var f in kept)
            {
                var proj = Names.ClassProjection(oc.Name, f.Name);
                pure.Add($"{fixedNames[slot.Name]}.{proj} == {before}.{proj}");
            }
        }

        if (fixedAll.Count > 0)
        {
            Line($"with {string.Join(" ", fixedAll.Select(f => f.Name).Concat(stillHeaps))}. " +
                 $"assert ({string.Join(" ** ", fixedAll.Select(f => f.Resource))});");
        }

        // R5.10. Flags are allocated only for the forms the body actually uses, so a
        // loop with neither `break` nor `continue` is emitted unchanged.
        // R26.2. A loop left only by `return`s breaks on the flag the `return` raises, so
        // that after the loop the flag alone says why it ended.
        var returnOnly = MayEscape(w.Body) && ContainsBreak(w.Body) && !ContainsUserBreak(w.Body);
        var brkCell = returnOnly ? Names.Local(Frontend.StmtLowerer.ReturnedFlag)
            : MayEscape(w.Body) && ContainsBreak(w.Body) ? $"var_brk_{_loop}" : null;
        var contCell = ContainsContinue(w.Body) ? $"var_cont_{_loop}" : null;
        _loop++;
        var outerEscape = _escape;
        _escape = brkCell is null && contCell is null ? null : new Escape(brkCell, contCell);

        if (brkCell is not null && !returnOnly)
        {
            Line($"let mut {brkCell} = false;");
            var value = FreshValue("brk");
            existentials.Add(value);
            resources.Add($"R.pts_to {brkCell} {value}");
            // R26.10. `Pal.Broke()` in this loop's invariant is the flag's value.
            scope = new SpecScope(scope);
            scope.Bind(Frontend.StmtLowerer.BrokeFlag, new Term(value, TermKind.Bool, IrPrim.Bool));
        }

        var guard = Capture(() => Expr(w.Cond));
        Line("while (");
        _indent++;
        _lines.AddRange(guard.Lines);
        if (brkCell is null)
        {
            Line(guard.Term);
        }
        else
        {
            // The user's guard comes first so that its dereferences stay visible to the
            // body; the break flag is a pure conjunct appended to it.
            var t = Fresh();
            Line($"let {t} = !{brkCell};");
            Line($"({guard.Term}) && not {t}");
        }
        _indent--;
        Line(")");

        // R5.8c. A loop invariant is assembled by exactly the test R12.2 applies to a
        // contract: an `SlProp` clause is a resource and goes next to the `pts_to`s,
        // anything else is a proposition and goes inside the one `pure`. Without this a
        // loop could only ever state facts about values, so a loop that *walks* a data
        // structure — a cursor — has nowhere to say which part of it the invariant owns,
        // and every iterative traversal stays out of reach.
        foreach (var i in w.Invariants)
        {
            if (i.Type is IrPrim { Kind: PrimKind.SlProp })
                resources.Add(spec.Emit(i, scope).Text);
            else
                pure.Add(spec.AsProp(spec.Emit(i, scope)));
        }
        Line("invariant " + MethodPlan.Clause(
            resources.ToImmutable(), pure.ToImmutable(), existentials.ToImmutable()));

        if (w.Decreases is not null)
        {
            var measure = spec.Math(w.Decreases, measureScope);
            // The iteration that breaks need not decrease the user's measure — it exits
            // instead. `until_set` makes the measure 0 once the flag is set, so the breaking
            // iteration decreases it whatever the measure's state then is (R27.10: Pulse's
            // join of the skipped rest keeps no fact about the cells it would have written).
            // F9 forbids a dereference inside a branch of an `if` in a measure, so the flag
            // and the measure are arguments rather than an `if`'s condition and arm.
            if (brkCell is not null) measure = $"CA.until_set !{brkCell} ({measure})";
            Line($"decreases ({measure})");
        }

        Line("{");
        _indent++;
        if (contCell is not null) Line($"let mut {contCell} = false;");

        // R5.8d. The last statement of a loop body is in *tail position*, exactly as the
        // last statement of a method body is (R4.2). It matters for the same reason: a
        // Pulse `let mut` needs a postcondition at the end of its scope, and it has one
        // only where the scope ends at a construct that carries an annotation. A field read
        // inside the non-null branch of a test — which is what §12 asks every cursor loop to
        // write — is therefore typable in tail position and untypable one statement short of
        // it. Emitting the branch as a tail rather than terminating it with `()` is what
        // closes that gap, and it is the same rule the method case already applies.
        //
        // R27.15. A body that may escape by `return` or `break` is a tail as well when there
        // is no step to run after it: the escape guard of R5.8d keeps what follows an
        // escaping statement under the flag, so each arm still meets the invariant. As a
        // non-tail its arms would be joined first, and Pulse cannot join arms that write
        // different locals once one of them has bound an `if`-expression's refined result.
        if (brkCell is null && contCell is null &&
            (w.Step.IsEmpty || w.Body is IrBlock sb && SplitAt([.. sb.Statements, .. w.Step]) is not null) ||
            w.Step.IsEmpty && SplitsRecordWrite(w.Body) ||
            w.Step.IsEmpty && contCell is null && brkCell is not null ||
            // R27.52. A receiver held at an existential model is reopened by a call in one
            // arm at a record of its own, and Pulse's join keeps nothing relating that record
            // to the one the other arm left: each arm meets the invariant instead.
            w.Step.IsEmpty && _receiverRenamed)
        {
            UnitTail(w.Step.IsEmpty ? w.Body
                : new IrBlock(w.Body.Loc, [.. ((IrBlock)w.Body).Statements, .. w.Step]), plan);
            _indent--;
            Line("};");
            _escape = outerEscape;
            return;
        }

        Statement(w.Body, plan);
        if (!w.Step.IsEmpty)
        {
            // R5.7 + R5.10. The `for` step runs after a `continue` but not after a
            // `break`, so it sits outside the body's escape guard and under the break
            // flag alone.
            if (brkCell is not null)
            {
                var t = Fresh();
                Line($"let {t} = !{brkCell};");
                Line($"if (not {t}) {{");
                _indent++;
                Sequence(w.Step, plan);
                Line("()");
                _indent--;
                Line("} else { () };");
            }
            else
            {
                Sequence(w.Step, plan);
            }
        }
        Line("()");
        _indent--;
        Line("};");
        _escape = outerEscape;
    }

    // =======================================================================
    // Exceptions (§19)
    // =======================================================================

    /// <summary>
    /// R19.2. <c>throw e</c> is <c>raise</c>. The exception is let-bound first so that
    /// building it is a step of its own, and a method's objects are closed before it
    /// exactly as before a <c>return</c>: the <c>raises</c> clause owns them folded, as the
    /// postcondition does. Inside a <c>try</c> only what the <c>try</c> declared is
    /// dropped, because the <c>try</c>'s own <c>raises</c> owns the rest.
    /// </summary>
    private void Throw(IrThrow th, MethodPlan plan, bool tail)
    {
        string exn;
        if (th.Value is { } value)
        {
            exn = Fresh();
            Line($"let {exn} = {Expr(value)};");
        }
        else if (_caught.Count > 0)
        {
            exn = _caught[^1];
        }
        else
        {
            diagnostics.Unsupported(th.Loc, "`throw;` outside a catch clause");
            return;
        }

        ReleaseForThrow(plan);
        Line(tail ? $"raise {exn}" : $"raise {exn};");
    }

    /// <summary>
    /// What a throw point gives back. Outside a <c>try</c>, the method's <c>raises</c>
    /// clause owns what its postcondition does, so objects are closed as at a return —
    /// except the object a constructor is building (R22.11), which the <c>raises</c> does
    /// not mention because the caller never receives it, and which may be thrown out of
    /// before its invariant holds: its representation is discarded as it stands.
    /// </summary>
    private bool ReleaseForThrow(MethodPlan plan)
    {
        if (_tryMarks.Count > 0)
        {
            DropLocals(null, _tryMarks[^1]);
            return false;
        }
        if (!NeedsEpilogue) return false;
        if (_method is { IsConstructor: true } &&
            _objects.FirstOrDefault(o => o.Binder == Names.Result) is { } built)
        {
            var saved = _objects;
            _objects = [.. _objects.Where(o => o != built)];
            CloseObjects(_method, plan);
            _objects = saved;
            DropRepresentation(built);
            return false;
        }
        CloseObjects(_method!, plan);
        return true;
    }

    /// <summary>
    /// R22.11 with R23.7. A call to a <c>[DoesNotReturn]</c> method: what this method holds goes
    /// back first, as at a <c>throw</c>. When that closed the receiver, a call on it is
    /// made on the closed receiver as it stands: R22.15's bracket would close it twice.
    /// </summary>
    private void DoesNotReturnCall(IrCall dnr, MethodPlan plan)
    {
        _receiverClosedForThrow = ReleaseForThrow(plan);
        try { Line(Expr(dnr) + ";"); }
        finally { _receiverClosedForThrow = false; }
    }

    private bool _receiverClosedForThrow;
    private bool _catching;

    /// <summary>
    /// R31.14. A static call that may raise, made while the receiver is open and holds its
    /// regions: the callee takes a region the receiver's invariant owns, so the receiver
    /// cannot be closed around the call (R27.38), and an exception it raises would leave
    /// the invariant unfolded. The call is caught in a local function, which returns the
    /// exception; the receiver is then closed as at a <c>throw</c> and the exception raised
    /// again. Only a receiver whose representation is its box and its regions, with
    /// nothing else live, is so handled; it may be held at a fraction.
    /// </summary>
    private Slot? RaisesThroughOpenRegion(IrCall call)
    {
        if (raising?.Contains(call.Callee) != true || call.HasReceiver || call.DoesNotReturn) return null;
        if (_tryMarks.Count > 0 || _windows.Count > 0 || _objectLocals.Count > 0 || _heldPeers.Count > 0 ||
            _receiverClosedForThrow || _objects is not [{ Name: Names.This, ViewBase: null } self])
            return null;
        if (self.Type is not IrClassType k || classes is null || !classes.TryGetValue(k.Name, out var decl))
            return null;
        if (!RegionsOf(decl).Any() ||
            decl.Fields.Any(f => f.Type is IrArrayType || f.Type is IrClassType && !IsRegionType(f.Type)))
            return null;
        if (_slots.Values.Any(s => s.Owns && s.Name != Names.This)) return null;
        // The callee's postcondition is restated at the arguments, which must be names.
        if ((Methods ?? methods)?.TryGetValue(call.Callee, out var callee) != true || callee!.Parameters.Length != call.Args.Length ||
            call.Args.Any(a => a is not IrVar v || !_slots.TryGetValue(v.Name, out var vs) || vs.Kind is not SlotKind.Value))
            return null;
        return self;
    }

    private void RaisingRegionCall(IrCall call, Slot self, MethodPlan plan)
    {
        var decl = classes![((IrClassType)self.Type).Name];
        var rep = FreshValue("rep");
        var heaps = RegionsOf(decl).Select(k => (k, FreshValue(Frontend.Region.HeapBinder(k.Name)))).ToList();
        var held = string.Join(" ** ",
            new[] { $"B.pts_to {self.Binder} {self.PermArg}{rep}" }
                .Concat(heaps.Select(h => PulseEmitter.RegionAt(h.k, self.Fraction ?? "1.0R", h.Item2))));
        Line($"with {rep} {string.Join(" ", heaps.Select(h => h.Item2))}. assert ({held});");
        // What the callee ensures is what the code after the call knows: a `try` is not
        // framed, so its contract restates it, read at the arguments and at the heaps held.
        var callee = (Methods ?? methods)![call.Callee];
        var scope = new SpecScope();
        for (var i = 0; i < callee.Parameters.Length; i++)
        {
            var prm = callee.Parameters[i];
            scope.Bind(prm.Name, new Term(_slots[((IrVar)call.Args[i]).Name].Binder, MethodPlan.KindOf(prm.Type), prm.Type));
        }
        foreach (var (k, h) in heaps)
            scope.Bind(Frontend.Region.HeapName(k.Name), new Term(h, TermKind.Other));
        scope = new SpecScope(scope) { Pre = scope };
        var post = callee.Ensures.Select(e => spec.AsProp(spec.Emit(e, scope))).ToList();
        var ex = $"ex_{_try++}";
        // And what it raises is what its `[Throws]` clauses say it may (R19.2).
        var cases = callee.Throws.Select(t =>
        {
            scope.Bind(Frontend.FrontendPass.ThrownParameter, new Term(ex, TermKind.Other, t.Type));
            var parts = new List<string>();
            if (t.Type.Name is { } n) parts.Add($"{Names.Qualified(Names.ExnIs(n))} {ex}");
            if (t.When is { } w) parts.Add(spec.AsProp(spec.Emit(w, scope)));
            return parts.Count == 0 ? "True" : "(" + string.Join(" /\\ ", parts) + ")";
        }).ToList();
        var raised = cases.Count == 0 ? held : $"{held} ** pure ({string.Join(" \\/ ", cases)})";
        // A `try` whose handler closed the receiver cannot be used here: Pulse appends a
        // forwarding branch to every handler, which must hand what the `try` raises to the
        // method's own `raises` as it stands, unclosed. So the call is caught inside a local
        // function, where no exception destination is in scope and that branch is
        // unreachable, and the outcome comes back as an `option exn` to raise from.
        var helper = $"catch_{_try++}";
        var res = FreshValue("caught");
        var normal = post.Count == 0 ? "True" : string.Join(" /\\ ", post);
        var thrown = cases.Count == 0 ? "True" : string.Join(" \\/ ", cases);
        var settled = $"{held} ** pure (None? {res} ==> ({normal})) ** " +
            $"pure (Some? {res} ==> (let {ex} = Some?.v {res} in {thrown}))";
        Line($"fn {helper} ()");
        _indent++;
        Line($"requires {held}");
        Line($"returns {res}: option exn");
        Line($"ensures {settled}");
        _indent--;
        Line("{");
        _indent++;
        Line("try");
        _indent++;
        Line($"returns {res}: option exn");
        Line($"ensures {settled}");
        Line($"raises (fun ({ex}: exn) -> {raised})");
        _indent--;
        Line("{");
        _indent++;
        // The receiver is not closed around this call as R27.38 closes one held read-only:
        // the callee takes its regions.
        _catching = true;
        try { Line(Expr(call) + ";"); }
        finally { _catching = false; }
        Line("None #exn");
        _indent--;
        Line("} catch {");
        _indent++;
        Line($"{ex} -> {{ Some {ex} }}");
        _indent--;
        Line("}");
        _indent--;
        Line("};");
        var outcome = Fresh();
        Line($"let {outcome} = {helper} ();");
        Line($"if (Some? {outcome}) {{");
        _indent++;
        ReleaseForThrow(plan);
        Line($"raise (Some?.v {outcome});");
        Line("()");
        _indent--;
        Line("} else {");
        _indent++;
        Line("()");
        _indent--;
        Line("};");
    }

    /// <summary>R22.11. Discards an open object's box and the arrays its fields own.</summary>
    private void DropRepresentation(Slot obj)
    {
        var klass = (IrClassType)obj.Type;
        if (classes is null || !classes.TryGetValue(klass.Name, out var decl)) return;
        var raw = Fresh();
        Line($"let {raw} = B.op_Bang {obj.Binder};");
        foreach (var field in decl.Fields.Where(f => f.Type is IrArrayType))
        {
            var projection = $"{raw}.{Names.ClassProjection(decl.Name, field.Name)}";
            var contents = FreshValue(field.Name);
            Line($"with {contents}. assert ({PulseEmitter.ArrayPts(field)} {projection} {contents});");
            Line($"drop_ ({PulseEmitter.ArrayPts(field)} {projection} {contents});");
        }
        Line($"drop_ (B.pts_to {obj.Binder} {raw});");
    }

    /// <summary>
    /// R19.3. <c>try</c>/<c>catch</c> is Pulse's <c>try</c>, whose one handler tests the
    /// exception against each catch clause in order and re-raises what none of them takes.
    ///
    /// <para>A Pulse <c>try</c> is not framed (F86): its <c>ensures</c> and <c>raises</c>
    /// must own everything that is live across it, exactly as a loop invariant must, and
    /// they are assembled the same way (R5.8b) — a slot the <c>try</c> does not assign is
    /// held at the value it had, one it does is existentially quantified. The
    /// <c>raises</c> adds what may reach the handler: an exception some unfiltered clause
    /// handles, or one the enclosing construct may itself raise. That is precisely what
    /// lets the handler's final <c>raise</c> be proved.</para>
    /// </summary>
    private void Try(IrTry tr, MethodPlan plan)
    {
        if (_objects.Length > 0 || _windows.Count > 0)
        {
            diagnostics.Error("PALCS0614", tr.Loc,
                "A `try` where an object's representation is open (an instance method that " +
                "reads a field, or inside a null test of a recursive object) is not " +
                "supported (doc/translation.md R19.3): the `try` would have to carry the " +
                "representation across both of its exits. Move the `try` to a method that " +
                "works through calls.");
            return;
        }

        var live = tr.Live.Where(n => _slots.TryGetValue(n, out var s) && s.Owns)
            .Select(n => _slots[n])
            .ToImmutableArray();
        var unassigned = tr.Unassigned.ToImmutableHashSet();

        var existentials = ImmutableArray.CreateBuilder<string>();
        var resources = ImmutableArray.CreateBuilder<string>();
        var fixedAll = new List<(string Name, string Resource)>();
        var scope = new SpecScope(plan.PreScope) { Pre = plan.PreScope };
        foreach (var slot in live)
        {
            var value = FreshValue(slot.Name);
            if (unassigned.Contains(slot.Name)) fixedAll.Add((value, slot.Resource(value)));
            else existentials.Add(value);
            resources.Add(slot.Resource(value));
            scope.Bind(slot.Name, new Term(value, MethodPlan.KindOf(slot.Type), slot.Type));
        }
        // R19.5. The invariant is stated over the same names, so that what is assigned is
        // spoken of at whatever value it has when control leaves.
        var invariant = tr.Invariants.Select(i => spec.AsProp(spec.Emit(i, scope))).ToImmutableArray();
        // R5.10's flags of an enclosing loop are live too, though no C# names them.
        foreach (var cell in new[] { _escape?.Break, _escape?.Continue })
        {
            if (cell is null) continue;
            var value = FreshValue("esc");
            existentials.Add(value);
            resources.Add($"R.pts_to {cell} {value}");
        }
        if (fixedAll.Count > 0)
        {
            Line($"with {string.Join(" ", fixedAll.Select(f => f.Name))}. " +
                 $"assert ({string.Join(" ** ", fixedAll.Select(f => f.Resource))});");
        }

        var ex = $"ex_{_try++}";
        var enclosing = _raises[^1];
        string Raised(string e)
        {
            var disjuncts = tr.Catches.Where(c => c.When is null)
                .Select(c => c.Type.Name is { } n ? $"{Names.Qualified(Names.ExnIs(n))} {e}" : "True")
                .Append(enclosing(e));
            return "(" + string.Join(" \\/ ", disjuncts.Select(d => $"({d})")) + ")";
        }

        var owned = resources.ToImmutable();
        var bound = existentials.ToImmutable();
        Line("try");
        _indent++;
        Line("ensures " + MethodPlan.Clause(owned, invariant, bound));
        Line($"raises (fun ({ex}: exn) -> " + MethodPlan.Clause(owned, [.. invariant, Raised(ex)], bound) + ")");
        _indent--;
        Line("{");
        _indent++;
        _raises.Add(Raised);
        _tryMarks.Add(_objectLocals.Count);
        Statement(tr.Body, plan);
        _tryMarks.RemoveAt(_tryMarks.Count - 1);
        _raises.RemoveAt(_raises.Count - 1);
        Line("()");
        _indent--;
        Line("} catch {");
        _indent++;
        Line($"{ex} -> {{");
        _indent++;
        _caught.Add(ex);
        Catches(tr, 0, ex, plan);
        _caught.RemoveAt(_caught.Count - 1);
        _indent--;
        Line("}");
        _indent--;
        Line("};");
    }

    /// <summary>
    /// R19.4. The catch clauses from the <paramref name="k"/>-th on, as a chain of tests.
    /// A clause binds its variable to the exception at its class's type, which its test
    /// has just established, and a filter is evaluated under that binding.
    /// </summary>
    private void Catches(IrTry tr, int k, string ex, MethodPlan plan)
    {
        if (k == tr.Catches.Length)
        {
            Line($"raise {ex}");
            return;
        }
        var c = tr.Catches[k];
        var test = c.Type.Name is { } n ? $"{Names.Qualified(Names.ExnIs(n))} {ex}" : "true";
        var mark = new HashSet<string>(_slots.Keys);
        string? binder = null;
        if (c.Var is { } v)
        {
            binder = $"{Names.Local(v)}_{ex}_{k}";
            Line($"let {binder} = {ex};");
            _slots[v] = new Slot(v, c.Type, SlotKind.Value, binder);
        }
        if (c.When is { } when)
        {
            var filter = Capture(() => Expr(when));
            if (!filter.Lines.IsEmpty)
            {
                diagnostics.Error("PALCS0614", when.Loc,
                    "This exception filter reads state. A `when` clause has to be a pure " +
                    "test of the exception and of values, because it is decided before any " +
                    "handler runs (doc/translation.md R19.4).");
            }
            test = $"{test} && ({filter.Term})";
        }
        Line($"if ({test}) {{");
        _indent++;
        Statement(c.Body, plan);
        Line("()");
        _indent--;
        Line("} else {");
        _indent++;
        if (binder is not null) _slots.Remove(c.Var!);
        foreach (var name in _slots.Keys.Where(x => !mark.Contains(x)).ToList()) _slots.Remove(name);
        Catches(tr, k + 1, ex, plan);
        _indent--;
        Line("}");
    }

    /// <summary>
    /// R5.8d. A statement in tail position whose value is unit — the last statement of a
    /// loop body. It is <see cref="Tail"/> without the return value or the object epilogue,
    /// and it recurses through blocks and two-armed <c>if</c>s so that a nest of them is a
    /// nest of tails; anything else is an ordinary statement and keeps its <c>()</c>.
    ///
    /// <para>A null test that opens a §10 window is deliberately *not* treated as a tail:
    /// the window's closing lemma is emitted by the non-tail path, and moving it would be a
    /// change to R10.7 rather than to where a block ends.</para>
    /// </summary>
    /// <summary>
    /// R5.8d, R24.24. A loop body's statements in tail position. Where one may escape, what
    /// follows it is guarded and is itself in tail position; an <c>if</c> one of whose arms
    /// writes a field of the receiver takes what follows into both arms, so that each arm is
    /// checked against the invariant rather than joined first: Pulse joins the record as a
    /// <c>match</c>, through whose projection no array field can then be found.
    /// </summary>
    private void UnitTailSequence(ImmutableArray<IrStmt> statements, MethodPlan plan)
    {
        for (var k = 0; k < statements.Length; k++)
        {
            var rest = statements.RemoveRange(0, k + 1);
            if (rest.IsEmpty) { UnitTail(statements[k], plan); return; }
            // R27.31. So does one whose arm moves a region (R22.12): the heap each arm leaves
            // is a fresh existential at the join, and what the arm proved about it is lost.
            // R27.40. And so, in a loop that may escape, does one that calls a method on a local
            // object without escaping (R26.5's split, which only a non-escaping loop gets).
            if (statements[k] is IrIf i &&
                (WritesRecordInArm(i) || _escape is null && MovesRegion(i) ||
                 _escape is not null && !MayEscape(i) && CallsLocalObject(i)) &&
                NullTest(i.Cond) is null)
            {
                IrBlock Arm(IrStmt? arm, IrLoc loc) =>
                    new(loc, [.. arm is IrBlock ab ? ab.Statements : arm is null ? [] : [arm], .. rest]);
                UnitTail(i with { Then = Arm(i.Then, i.Then.Loc), Else = Arm(i.Else, i.Else?.Loc ?? i.Loc) }, plan);
                return;
            }
            // R27.53. A local initialized by a conditional one of whose arms calls a method
            // that moves its receiver: Pulse joins the two arms' calls at a fresh model and
            // keeps the facts of one arm only, so the declaration becomes an `if` whose arms
            // each bind the local and run the rest.
            // R32.14. So does one an arm of which calls a view's member that takes the
            // view's record by reference: Pulse rebinds the record at a fresh value there too.
            if (statements[k] is IrLocalDecl { Init: IrConditional ce } d &&
                (MovesReceiver(ce.Then) || MovesReceiver(ce.Else) || PassesRefSelf(ce.Then) || PassesRefSelf(ce.Else)))
            {
                UnitTail(new IrIf(d.Loc, ce.Cond,
                    new IrBlock(ce.Then.Loc, [d with { Init = ce.Then }, .. rest]),
                    new IrBlock(ce.Else.Loc, [d with { Init = ce.Else }, .. rest])), plan);
                return;
            }
            // R27.27. An escaping `if` whose join would lose a moved region (R22.12): the rest
            // goes into the arm that falls through; the escaping arm keeps none of it.
            if (statements[k] is IrIf ei && _escape is not null && MayEscape(ei) && MovesRegion(ei))
            {
                IrBlock Arm(IrStmt? arm, IrLoc loc)
                {
                    ImmutableArray<IrStmt> own = arm is IrBlock ab ? ab.Statements : arm is null ? [] : [arm];
                    return new(loc, own is [.., var last] && Jumps(last) ? own : [.. own, .. rest]);
                }
                static bool Jumps(IrStmt t) =>
                    t is IrBreak or IrContinue or IrThrow or IrReturn || t is IrBlock { Statements: [.., var l] } && Jumps(l);
                UnitTail(ei with { Then = Arm(ei.Then, ei.Then.Loc), Else = Arm(ei.Else, ei.Else?.Loc ?? ei.Loc) }, plan);
                return;
            }
            Statement(statements[k], plan);
            if (_escape is not null && MayEscape(statements[k]))
            {
                Line($"if ({EscapeTest()}) {{");
                _indent++;
                UnitTailSequence(rest, plan);
                _indent--;
                Line("} else { () }");
                return;
            }
        }
        Line("()");
    }

    /// <summary>R32.14. Whether an expression passes a view member's by-reference record on to a call.</summary>
    private bool PassesRefSelf(IrExpr e) =>
        _method is { } m && m.Parameters.Any(p => p.Name == Frontend.BorrowContext.Self && p.Mode == ParamMode.Ref) &&
        Passes.Check.Subexpressions(e).OfType<IrCall>().Any(c => c.Args.Any(a => a is IrVar { Name: Frontend.BorrowContext.Self } or IrRefArg { Operand: IrVar { Name: Frontend.BorrowContext.Self } }));

    /// <summary>R27.53. Whether an expression calls a method that may move its receiver.</summary>
    private static bool MovesReceiver(IrExpr e) =>
        Passes.Check.Subexpressions(e).OfType<IrCall>().Any(c => c.MutatesReceiver);

    /// <summary>R24.24. Whether some arm of an <c>if</c> assigns a field of the receiver.</summary>
    private bool WritesRecordInArm(IrIf i) =>
        ReceiverWrites(i.Then).Record || i.Else is { } e && ReceiverWrites(e).Record;

    /// <summary>R24.24. Whether a loop body has an <c>if</c>, not last, that R24.24 splits.</summary>
    private bool SplitsRecordWrite(IrStmt body) =>
        body is IrBlock b && b.Statements.Length > 1 &&
        b.Statements.RemoveAt(b.Statements.Length - 1).Any(s => s is IrIf i && WritesRecordInArm(i));

    private void UnitTail(IrStmt stmt, MethodPlan plan)
    {
        switch (stmt)
        {
            case IrBlock { Statements.IsEmpty: true }:
                Line("()");
                return;

            case IrBlock b when SplitAt(b.Statements) is { } k:
            {
                // R26.5. An arm that calls a method on a local object leaves that object's
                // invariant under a fresh existential, and Pulse's join keeps the other
                // arm's facts about the old one only under the arm's condition, unrelated
                // to the new witness. The rest of the block moves into both arms (as
                // R22.12 does in a method's tail), so the loop invariant is proved per arm.
                var split = (IrIf)b.Statements[k];
                var rest = b.Statements.RemoveRange(0, k + 1);
                ImmutableArray<IrStmt> Arm(IrStmt? arm)
                {
                    ImmutableArray<IrStmt> own = arm is IrBlock ab ? ab.Statements : arm is null ? [] : [arm];
                    return own is [.., IrThrow or IrReturn or IrExprStmt { Expr: IrCall { DoesNotReturn: true } } or IrGhostStmt { Kind: GhostKind.Unreachable }]
                        ? own : [.. own, .. rest];
                }
                Scoped(() =>
                {
                    Sequence(b.Statements.RemoveRange(k, b.Statements.Length - k), plan);
                    UnitTail(split with
                    {
                        Then = new IrBlock(split.Then.Loc, Arm(split.Then)),
                        Else = new IrBlock(split.Else?.Loc ?? split.Loc, Arm(split.Else)),
                    }, plan);
                }, dropAtEnd: false);
                return;
            }

            case IrBlock b:
                Scoped(() => UnitTailSequence(b.Statements, plan), dropAtEnd: false);
                return;

            // R27.54. `if (c) S` last in a loop body, where `S` calls a method that changes its
            // receiver: Pulse's join of `S` with the empty arm keeps neither arm's facts about
            // the receiver, so the arms are tails, each proving the invariant.
            case IrIf { Else: null } bare when NullTest(bare.Cond) is null &&
                                              Check.Statements(bare.Then).SelectMany(Check.Expressions).Any(MovesReceiver):
                UnitTail(bare with { Else = new IrBlock(bare.Loc, []) }, plan);
                return;

            case IrIf { Else: not null } i when NullTest(i.Cond) is null:
            {
                if (i.Cond is IrBinary pnb && PlainNullTest(pnb) is { } ptest)
                {
                    PlainNullWindow(ptest, i, branch => UnitTail(branch!, plan), tail: true);
                    return;
                }
                var cond = Expr(i.Cond);
                Line($"if ({cond}) {{");
                _indent++;
                UnitTail(i.Then, plan);
                _indent--;
                Line("} else {");
                _indent++;
                UnitTail(i.Else, plan);
                _indent--;
                Line("}");
                return;
            }

            default:
                Statement(stmt, plan);
                Line("()");
                return;
        }
    }

    /// <summary>
    /// R26.5. The first non-final statement of a loop body that is an <c>if</c> one of
    /// whose arms calls a method on a local object, if any.
    /// </summary>
    private int? SplitAt(ImmutableArray<IrStmt> statements)
    {
        if (_escape is not null) return null;
        for (var k = 0; k < statements.Length - 1; k++)
            if (statements[k] is IrIf i && NullTest(i.Cond) is null && !MayEscape(i) &&
                (CallsLocalObject(i) ||
                 (DeclaresCell(i) || AssignsConditional(i)) && Straight(statements.Skip(k + 1))))
                return k;
        return null;
    }

    /// <summary>
    /// R34.11. Whether an arm of <paramref name="i"/> declares a local, which is a Pulse
    /// <c>let mut</c>: Pulse allocates one only where its scope ends at an annotated
    /// postcondition, which an arm joined with its sibling does not have, and an arm that
    /// is a tail does.
    /// </summary>
    private static bool DeclaresCell(IrIf i) =>
        Passes.Check.Statements(i).Skip(1).Any(st => st is IrLocalDecl { Immutable: false });

    /// <summary>
    /// R34.11. Whether an arm of <paramref name="i"/> assigns a local a conditional value
    /// (<c>n = c ? a : b</c>): the value's own join sits inside the arm, and Pulse's join of
    /// the arms then keeps the local's value of the assigning arm only.
    /// </summary>
    private static bool AssignsConditional(IrIf i) =>
        Passes.Check.Statements(i).Skip(1).Any(st => st is IrAssign { Target: IrVar, Value: IrConditional });

    /// <summary>
    /// R34.11. Whether <paramref name="rest"/>, which a split copies into both arms, has no
    /// branch or loop of its own, so the copy stays linear.
    /// </summary>
    private static bool Straight(IEnumerable<IrStmt> rest)
    {
        foreach (var st in rest)
            if (Passes.Check.Statements(st).Any(x => x is IrIf or IrWhile or IrFor)) return false;
        return true;
    }

    private bool CallsLocalObject(IrStmt s) =>
        Passes.Check.Statements(s).SelectMany(Passes.Check.Expressions)
            .SelectMany(Passes.Check.Subexpressions).OfType<IrCall>()
            .Any(c => c.HasReceiver && c.Args is [IrVar { Type: IrClassType k } r, ..] &&
                      r.Name != Names.This && _objects.All(o => o.Name != r.Name) &&
                      !(classes is not null && classes.TryGetValue(k.Name, out var d) && d.IsPlain));

    private static bool ContainsBreak(IrStmt stmt) => stmt switch
    {
        IrBreak => true,
        IrBlock b => b.Statements.Any(ContainsBreak),
        IrIf i => ContainsBreak(i.Then) || (i.Else is not null && ContainsBreak(i.Else)),
        _ => false,
    };

    private static bool ContainsUserBreak(IrStmt stmt) => stmt switch
    {
        IrBreak { FromReturn: false } => true,
        IrBlock b => b.Statements.Any(ContainsUserBreak),
        IrIf i => ContainsUserBreak(i.Then) || (i.Else is not null && ContainsUserBreak(i.Else)),
        _ => false,
    };

    private static bool ContainsContinue(IrStmt stmt) => stmt switch
    {
        IrContinue => true,
        IrBlock b => b.Statements.Any(ContainsContinue),
        IrIf i => ContainsContinue(i.Then) || (i.Else is not null && ContainsContinue(i.Else)),
        _ => false,
    };

    /// <summary>
    /// The scope a <c>decreases</c> measure is read in: by F3 a measure may dereference
    /// mutable locals but may not mention the invariant's existentials, so every cell
    /// denotes <c>!var_x</c> here rather than a value binder.
    /// </summary>
    /// <summary>R34.6. The cell holding an enumerator's cursor, which its members are passed.</summary>
    private string CursorCell(IrExpr cursor)
    {
        if (cursor is IrVar v && _slots.TryGetValue(v.Name, out var slot) && slot.Kind == SlotKind.Cell)
            return slot.Binder;
        diagnostics.Error("PALCS0862", cursor.Loc,
            "An enumerator is used where its cursor is not a local of this method (doc/translation.md R34.6).");
        return "()";
    }

    private SpecScope DerefScope()
    {
        var scope = new SpecScope();
        foreach (var (name, slot) in _slots)
        {
            var text = slot.Kind is SlotKind.Cell or SlotKind.RefParam ? $"!{slot.Binder}"
                // R27.39. A trace is read from its protocol, as a heap is from its region.
                : slot.Kind is SlotKind.Trace ? $"(Pulse.Lib.CSharp.Callback.trace_now {slot.Binder} ())"
                // R34.1. An enumerable is the items it yields, which never change.
                : slot.Kind is SlotKind.Enumerable && slot.Items is { } items ? items
                : slot.Binder;
            // Here an array denotes the live array, not its contents: a measure may
            // dereference a mutable local (F3) but may not mention the invariant's
            // existentials, which is where the contents live.
            // A cell holding an array (R26.10) dereferences to the live array too.
            var kind = slot.Kind is SlotKind.Array || (slot.Kind is SlotKind.Cell && slot.Type is IrArrayType)
                ? TermKind.Array : MethodPlan.KindOf(slot.Type);
            scope.Bind(name, new Term(text, kind, slot.Type));
        }
        return scope;
    }

    /// <summary>
    /// R5.11. A ghost statement needs to name the values held right now, so each one is
    /// preceded by a <c>with … assert …</c> that binds them. Regenerating the names at
    /// every ghost point is what keeps them from going stale after an assignment.
    /// </summary>
    private void Ghost(IrGhostStmt g, MethodPlan plan)
    {
        // R5.13 is handled before the naming bracket below, and deliberately. That bracket
        // names every owned resource at the permission the slot was declared with; a
        // `Share` is the statement that stops that being true, so a lemma about the
        // permission must not be preceded by an assertion that presumes it.
        if (g.Kind is GhostKind.Share or GhostKind.Gather) { Permission(g); return; }

        // R17.6. The end of a borrow, before the naming bracket for the same reason a
        // `Share` is: the bracket names every owned resource at the slot it was declared
        // with, and `Pal.Restore` is the statement that stops the span being one.
        if (g.Kind is GhostKind.Restore) { Restore(g); return; }

        // R5.12, again: inside R4.10's window the receiver is a representation, so its
        // folded invariant is not what the context holds and asserting it would fail. The
        // representation is named instead, which is also what lets a ghost statement in an
        // instance method mention a field.
        var owned = _slots.Values
            .Where(s => s.Owns && !_objects.Any(o => o.Name == s.Name))
            .ToImmutableArray();
        var scope = new SpecScope(plan.PreScope) { Pre = plan.PreScope };

        var named = new List<(string Name, string Resource)>();
        var here = new IrBlock(g.Loc, ImmutableArray<IrStmt>.Empty);
        foreach (var receiver in _objects)
        {
            Representation(
                receiver, here, scope, new SpecScope(),
                ImmutableArray.CreateBuilder<string>(), ImmutableArray.CreateBuilder<string>(),
                ImmutableArray.CreateBuilder<string>(), named);
        }

        foreach (var slot in owned)
        {
            var value = FreshValue(slot.Name);
            // R27.49. An object held at its heaps (outside a loop) is named at them as they are now.
            if (slot is { Kind: SlotKind.Object, Type: IrClassType hc, Open: false, Index: null, Heaps.IsEmpty: false } &&
                slot.LoopHeaps.IsDefaultOrEmpty)
            {
                var hs = slot.Heaps.Select(h => FreshValue(Frontend.Region.HeapBinder(h.Region.Name))).ToList();
                named.Add((string.Join(" ", [value, .. hs]),
                    $"{InvHeap(hc)} {slot.Binder} {slot.PermArg}{value} {string.Join(" ", hs)}"));
                scope.Bind(slot.Name, new Term(value, MethodPlan.KindOf(slot.Type), slot.Type));
                for (var i = 0; i < hs.Count; i++)
                    scope.Bind(Frontend.Region.HeapNameOf(slot.Heaps[i].Region.Name, slot.Name), new Term(hs[i], TermKind.Other));
                continue;
            }
            named.Add((value, slot.Resource(value)));
            scope.Bind(slot.Name, new Term(value, MethodPlan.KindOf(slot.Type), slot.Type));
            // R27.23. An `[Open]` receiver's fields and heaps, as held right now.
            if (slot is { Open: true, Type: IrClassType oc })
            {
                foreach (var f in slot.OpenFields)
                {
                    var at = $"{value}.{Names.ClassProjection(oc.Name, f.Name)}";
                    if (f.Type is IrArrayType)
                    {
                        var c = FreshValue(Names.Contents(f.Name));
                        named.Add((c, $"{PulseEmitter.ArrayPts(f)} {at} {c}"));
                        scope.Bind($"{Names.This}.{f.Name}", new Term(c, TermKind.Seq, f.Type));
                        scope.Bind(SpecEmitter.ArrayRefKey($"{Names.This}.{f.Name}"), new Term(at, TermKind.Other, f.Type));
                        continue;
                    }
                    scope.Bind($"{Names.This}.{f.Name}", new Term(at, MethodPlan.KindOf(f.Type), f.Type));
                }
                foreach (var k in slot.OpenHeaps)
                {
                    var heap = FreshValue(Frontend.Region.HeapBinder(k.Name));
                    named.Add((heap, PulseEmitter.RegionAt(k, "1.0R", heap)));
                    scope.Bind(Frontend.Region.HeapName(k.Name), new Term(heap, TermKind.Other));
                }
            }
        }

        // R27.16. A region the method holds and writes is named as it is now, so that
        // `Pal.Heap<K>()` in a ghost statement is the current heap, not the one at entry.
        foreach (var use in plan.Held.Where(u => u.Mutates))
        {
            var heap = FreshValue(Frontend.Region.HeapBinder(use.Region.Name));
            named.Add((heap, PulseEmitter.RegionAt(use.Region, "1.0R", heap)));
            scope.Bind(Frontend.Region.HeapName(use.Region.Name), new Term(heap, TermKind.Other));
        }

        if (named.Count > 0)
        {
            Line($"with {string.Join(" ", named.Select(n => n.Name))}. " +
                 $"assert ({string.Join(" ** ", named.Select(n => n.Resource))});");
        }

        foreach (var slot in _slots.Values.Where(s => !s.Owns))
            scope.Bind(slot.Name, new Term(slot.Binder, MethodPlan.KindOf(slot.Type), slot.Type));

        switch (g.Kind)
        {
            case GhostKind.Assert:
                Line($"assert (pure ({spec.AsProp(spec.Emit(g.Prop!, scope))}));");
                return;
            case GhostKind.Assume:
                Line($"assume (pure ({spec.AsProp(spec.Emit(g.Prop!, scope))}));");
                return;
            // R27.48. Behind it nothing is held; LowerBlock dropped the rest of the block.
            case GhostKind.Unreachable:
                Line("unreachable ();");
                return;
            case GhostKind.Raw:
                Line(Antiquotation.Expand(g.Text!, scope, Binder) + ";");
                return;
            case GhostKind.Let:
            {
                var inner = g.Type is IrGhostType gt ? gt.Inner : g.Type!;
                // R24.12. A snapshot is a specification value, and a machine integer in a
                // specification is its mathematical value.
                if (inner is IrPrim { IsMachineInt: true }) inner = new IrPrim(PrimKind.SpecInt);
                Line($"let {g.Text} : erased ({Types.Render(inner)}) = " +
                     $"hide ({SpecArgument(g.Prop!, inner, scope)});");
                _slots[g.Text!] = new Slot(g.Text!, inner, SlotKind.Value, g.Text!);
                return;
            }
            case GhostKind.LemmaCall when g.Prop is IrSpecOp lemma:
                Line($"{spec.Emit(lemma, scope).Text};");
                return;
            case GhostKind.LemmaCall when g.Prop is IrCall call:
                // R14.5. A generic [Lemma] is applied to its type arguments first.
                Line($"{Names.SpecModule(call.Callee)}.{Names.Lemma(call.Callee)} " +
                     string.Join(" ", call.TypeArguments.Select(Types.Atom)
                         .Concat(call.Args.Select((a, i) =>
                             SpecArgument(a, SpecEmitter.ParamType(call, i), scope)))) + ";");
                return;
            default:
                return;
        }
    }

    /// <summary>
    /// R17.6. <c>Pal.Restore(w)</c>: the ghost statement that gives a borrowed span back.
    /// </summary>
    /// <remarks>
    /// Which of the three library operations this is depends on where the span came from,
    /// which the slot recorded at the declaration that borrowed it. Nothing is inferred
    /// here, and nothing needs to be: the receipt is a resource, so the array, the
    /// permission, the bounds and both contents are recovered by unifying it against what
    /// the context holds (SliceFacts S8). That is what lets `Pal.Restore` take one argument.
    ///
    /// After this the span's slot is dropped. A later use of the name is then out of scope,
    /// which is the right message: what makes it unusable is that its ownership has gone.
    /// </remarks>
    private void Restore(IrGhostStmt g)
    {
        if (g.Prop is not IrVar v || Lookup(v.Name) is not { Kind: SlotKind.Span } slot)
        {
            diagnostics.SpanWindow(g.Loc, "`Pal.Restore` of anything but a borrowed span local");
            return;
        }

        if (slot.Origin is not { } origin)
        {
            diagnostics.SpanWindow(g.Loc,
                $"`Pal.Restore` of the span parameter `{v.Name}`, which this method did not borrow");
            return;
        }

        Line($"Span.{origin switch
        {
            SpanOrigin.Array => "restore_array",
            SpanOrigin.ArrayRange => "restore_array_range",
            _ => "restore_sub",
        }} {slot.Binder};");

        _slots.Remove(v.Name);
    }

    /// <summary>
    /// R17.5. Emits a borrow, binding the window to <paramref name="target"/>. One
    /// operation per origin, each consuming the source's ownership and producing a receipt.
    /// </summary>
    private string Borrow(IrSpanCreate create, string target)
    {
        var source = Expr(create.Source);
        if (create.Origin is SpanOrigin.Array)
        {
            Line($"let {target} = Span.of_array {source};");
            return target;
        }
        var start = Expr(create.Start!);
        var count = Expr(create.Length!);
        var op = create.Origin is SpanOrigin.ArrayRange ? "of_array_range" : "sub";
        Line($"let {target} = Span.{op} {source} {start} {count};");
        return target;
    }

    /// <summary>R17.1. Whether an expression denotes a span rather than an array.</summary>
    private bool IsSpan(IrExpr e) =>
        e.Type is IrSpanType ||
        (e is IrVar v && Lookup(v.Name) is { Type: IrSpanType });

    /// <summary>
    /// R5.13. <c>Pal.Share</c>/<c>Pal.Gather</c> translate by what their argument is: an
    /// object goes through the lemmas R3.10d emitted for its class, an array through
    /// <c>Pulse.Lib.Array</c>'s. Nothing else has a permission to split, so nothing else
    /// has a translation — and that is a translatability refusal, not a provability one:
    /// whether the permission was there to split is Pulse's question.
    /// </summary>
    private void Permission(IrGhostStmt g)
    {
        var share = g.Kind is GhostKind.Share;

        if (g.Prop is IrVar v && Lookup(v.Name) is { } slot)
        {
            switch (slot.Type)
            {
                case IrClassType c:
                    var lemma = share ? Names.ClassInvShare(c.Name) : Names.ClassInvGather(c.Name);
                    Line($"{Names.ClassModule(c.Name)}.{lemma} {slot.Binder};");
                    return;
                case IrArrayType:
                    Line($"A.{(share ? "share" : "gather")} {slot.Binder};");
                    return;
            }
        }

        diagnostics.Unsupported(g.Loc,
            $"`Pal.{(share ? "Share" : "Gather")}` of anything but an array or an object variable");
    }

    private Slot? Lookup(string name) =>
        _slots.TryGetValue(name, out var slot) ? slot
        : _objectLocals.FirstOrDefault(l => l.Name == name);

    /// <summary>
    /// The object a Pulse binder stands for, if any. A conversion (R9.15) produces a
    /// reference with no C# name at all, so the binder — not the source name — is what
    /// identifies it once it has been emitted.
    /// </summary>
    private Slot? SlotByBinder(string binder) =>
        _objectLocals.FirstOrDefault(l => l.Binder == binder)
        ?? _slots.Values.FirstOrDefault(l => l.Kind == SlotKind.Object && l.Binder == binder);

    /// <summary>
    /// R4.7: a lemma is applied to the values the program holds, so its arguments are
    /// passed with their program types and receive no <c>Int32.v</c> coercion.
    /// </summary>
    /// <summary>
    /// R4.13. A lemma called from code takes its arguments under exactly the rule a lemma
    /// mentioned in a specification does: a machine value entering a mathematical
    /// parameter is C#'s implicit conversion, and is the `.v` of §6.
    /// </summary>
    private string SpecArgument(IrExpr arg, IrType? paramType, SpecScope scope) =>
        spec.Argument(arg, paramType, scope);

    // =======================================================================
    // Expressions (R6)
    // =======================================================================

    /// <summary>
    /// Emits an expression, let-binding every stateful subexpression, and returns the
    /// Pulse term denoting its value.
    /// </summary>
    private string Expr(IrExpr expr)
    {
        switch (expr)
        {
            case IrLiteral l:
                return Types.Literal(l.Value, l.Type);

            // R4.9c, R4.12b. The call took this reference's invariant with it.
            case IrVar v when _slots.TryGetValue(v.Name, out var given) && given.Given is { } to:
                diagnostics.Error("PALCS0550", v.Loc,
                    $"`{v.Name}` cannot be used after it is passed to `{to}`, which takes " +
                    "ownership of it (R4.9c). What `" + v.Name + "` owned is now part of " +
                    "what that call produced: use the result instead.");
                return "()";

            // R9.16. The cast moved this reference's invariant onto the derived name.
            case IrVar v when _slots.TryGetValue(v.Name, out var cast) && cast.Cast is { } to:
                diagnostics.Error("PALCS0548", v.Loc,
                    $"`{v.Name}` cannot be used after it is cast to `{to}`. The cast moved " +
                    $"what `{v.Name}` owned onto the `{to}` reference (R9.16), which is the " +
                    "same object: use that name instead.");
                return "()";

            // R34.10. A reassigned array local is read, written, measured, resized and
            // returned through its cell; it is not a value to pass elsewhere.
            case IrVar v when _slots.TryGetValue(v.Name, out var cellArray) && cellArray.Kind == SlotKind.ArrayCell:
                diagnostics.Error("PALCS0863", v.Loc,
                    $"`{v.Name}` is an array local that is reassigned, so it is held in a cell " +
                    "(doc/translation.md R34.10). Such a local may be indexed, written, measured " +
                    "with `.Length`, resized with `Array.Resize` and returned, but not otherwise used.");
                return "()";

            case IrVar v when _slots.TryGetValue(v.Name, out var slot):
                if (slot.Kind is SlotKind.Cell or SlotKind.RefParam)
                {
                    var t = Fresh();
                    Line($"let {t} = !{slot.Binder};");
                    return t;
                }
                return slot.Binder;

            case IrVar v:
                diagnostics.Error("PALCS0400", v.Loc, $"`{v.Name}` is not in scope here.");
                return "()";

            // R6.10: a by-reference argument passes the cell, not its contents.
            case IrRefArg { Operand: IrVar v } when _slots.TryGetValue(v.Name, out var slot)
                                                   && slot.Kind is SlotKind.Cell or SlotKind.RefParam:
                return slot.Binder;

            case IrRefArg r:
                diagnostics.Error("PALCS0402", r.Loc,
                    "Only a local variable or a `ref`/`out` parameter can be passed by reference.");
                return "()";

            // R3.3/R17.3. `a.Length` and `s.Length`. One node, two libraries: a span's
            // length is `Slice.len`, which is pure and non-ghost exactly as an array's
            // header field is, so nothing but the qualifier differs.
            case IrLength { Array: IrVar lv } when ArrayCellOf(lv) is { } lcell:
            {
                var t = Fresh();
                Line($"let {t} = Pulse.Lib.CSharp.ArrayCell.length {lcell.Binder};");
                return t;
            }

            case IrElement { Array: IrVar rv } rel when ArrayCellOf(rv) is { } rcell:
            {
                var index = Expr(rel.Index);
                var t = Fresh();
                Line($"let {t} = Pulse.Lib.CSharp.ArrayCell.read {rcell.Binder} {index};");
                return t;
            }

            case IrLength len:
            {
                var array = Expr(len.Array);
                var t = Fresh();
                WithArrays([(len.Array, array)], () =>
                    Line($"let {t} = {(IsSpan(len.Array) ? "Span." : "")}length_i32 {array};"));
                return t;
            }

            // R6.4/R17.4. `a[i]` and `s[i]`, with the same bounds obligations.
            case IrElement el:
            {
                var array = Expr(el.Array);
                var index = Expr(el.Index);
                var t = Fresh();
                WithArrays([(el.Array, array)], () =>
                    Line($"let {t} = {(IsSpan(el.Array) ? "Span." : "")}read {array} {index};"));
                return t;
            }

            // R17.5. Borrowing. Each of the three forms consumes the source's ownership and
            // produces the window's, plus a receipt that only `Pal.Restore` can redeem.
            case IrSpanCreate create:
                return Borrow(create, Fresh());

            // R6.9. `new T[n]`. `Pulse.Lib.CSharp.Array.alloc` is where the garbage
            // collector is assumed: it carries no deallocation obligation, unlike
            // `Pulse.Lib.Array.alloc`, which is a stack allocation.
            // R10.2. `null` is the empty structure, and owning it is free — which is what
            // `intro_nil` says. Emitting the step here rather than at each position a null
            // may appear keeps `new Node(v, null)` and `x.next = null` the same rule.
            // R12.2. `null` on a `[Plain]` class is the null pointer and nothing else:
            // §12 derived no `intro_nil`, because it derived no predicate for the lemma to
            // be about. Whether a null pointer may stand where a segment is wanted is the
            // user's predicate's business.
            // R20.3. `null` at a `T?` is `None`; the operations of `T?` are `option`'s.
            case IrNull { Type: IrOptionType on }:
                return $"(None #{Types.Atom(on.Inner)})";
            case IrOptionOp oo:
            {
                var operand = Expr(oo.Operand);
                return oo.Op switch
                {
                    OptionOpKind.HasValue => $"(Some? {operand})",
                    OptionOpKind.Value => $"(Some?.v {operand})",
                    // R33.11. A value of another type the same F* type stands for (two
                    // bindings of one type) is given the option's type explicitly.
                    _ when oo.Type is IrOptionType on && oo.Operand.Type is { } ot && !ot.Equals(on.Inner) =>
                        $"(Some #{Types.Atom(on.Inner)} {operand})",
                    _ => $"(Some {operand})",
                };
            }

            // R20.3. A delegate is created and nothing more; its identity is opaque.
            case IrMethodGroup mg:
                return $"(Opaque.method_group {Types.StringLiteral(mg.Method)})";

            // R20.7. A specification operation applied to values is a pure F* function:
            // reading `band.Min` off a `[SpecType]` value is its `[SpecOp]`.
            case IrSpecOp so:
            {
                var operands = so.TypeArgs.Select(Types.Atom)
                    .Concat(so.Args.Select(a => Atom(Expr(a)))).ToList();
                return operands.Count == 0
                    ? so.Function
                    : $"({so.Function} {string.Join(" ", operands)})";
            }

            // R34.3, R34.6. An enumerable's count; an enumerator's start, step and item.
            case IrEnumOp eo:
            {
                if (eo.Op == EnumOpKind.Start) return "0l";
                var source = Expr(eo.Source);
                var t = Fresh();
                var call = eo.Op switch
                {
                    EnumOpKind.Count => $"count {source}",
                    EnumOpKind.MoveNext => $"move_next {source} {CursorCell(eo.Args[0])}",
                    _ => $"current {source} {CursorCell(eo.Args[0])}",
                };
                Line($"let {t} = Pulse.Lib.CSharp.Enumerable.{call};");
                return t;
            }

            // R20.6. A stable sort into a fresh array, at the order the key's type has.
            // R22.25. A search reads the array and yields a position.
            case IrArraySearch se:
            {
                var ops = Operands([se.Array, se.Item, se.Start, se.Count]);
                var (array, item, start, count) = (ops[0], ops[1], ops[2], ops[3]);
                var t = Fresh();
                var fn = se.Last ? "last_index_of" : "index_of";
                Line($"let {t} = Pulse.Lib.CSharp.Array.{fn} {array} {item} {start} {count};");
                return t;
            }

            case IrArrayBinarySearch bs:
            {
                var ops = Operands([bs.Array, bs.Start, bs.Count, bs.Item, bs.Comparer]);
                var (array, start, count, item, comparer) = (ops[0], ops[1], ops[2], ops[3], ops[4]);
                var t = Fresh();
                Line($"let {t} = Pulse.Lib.CSharp.Sorted.range_search_array {array} {start} {count} {item} {comparer};");
                return t;
            }

            case IrOrderBy ob:
            {
                var source = Expr(ob.Source);
                var t = Fresh();
                Line($"let {t} = Linq.order_by_to_list {source} {ob.Key} {OrderOf(ob.KeyType)};");
                return t;
            }

            case IrNull pn when pn.Type is IrClassType pk
                && classes is not null && classes.TryGetValue(pk.Name, out var pnd) && pnd.IsPlain:
                // R27.6. Typed, so that a cell initialised with it has a type to allocate.
                return pnd.IsRegion ? $"(B.null #{PulseEmitter.RegionRaw(pk)})" : "B.null";

            // R31.9. A non-recursive class has no `intro_nil` (§10 derives it only for a
            // recursive one): its null, stored in a node's back pointer, is the typed null box.
            case IrNull nn when nn.Type is IrClassType nk
                && classes is not null && classes.TryGetValue(nk.Name, out var nnd) && nnd.Recursion is null:
            {
                var t = Fresh();
                Line($"let {t} : {Types.Render(nk with { Nullable = true })} = B.null;");
                return t;
            }

            // R15.8. `B.null` at a generic class says nothing about what it is empty *of*,
            // so the type argument `intro_nil` takes implicitly (R15.2) has nothing to
            // resolve against. Naming the empty structure first, at its type, is the
            // smallest thing that gives the implicit a source; the monomorphic case has
            // no ambiguity and so keeps the shorter form.
            case IrNull n when n.Type is IrClassType { TypeArguments.IsEmpty: false } gk:
            {
                var t = Fresh();
                Line($"let {t} : {Types.Render(gk with { Nullable = true })} = B.null;");
                Line($"{Names.ClassModule(gk.Name)}.{Names.ClassIntroNil(gk.Name)} {t} 1.0R;");
                return t;
            }

            case IrNull n when n.Type is IrClassType k:
                Line($"{Names.ClassModule(k.Name)}.{Names.ClassIntroNil(k.Name)} B.null 1.0R;");
                return "B.null";

            case IrNewArray na:
            {
                var alloc = NewArray(na);
                var t = Fresh();
                Line($"let {t} = {alloc};");
                return t;
            }

            // R12.3. A field of a `[Plain]` reference. The same memory operation as R3.8 —
            // dereference the box, project the record — reached by a different slot kind,
            // because a plain reference carries no model and so is an ordinary value.
            // R19.1. An exception's field is its class's accessor applied to it; an
            // exception is a value, so nothing is owned and nothing is opened.
            case IrField { Receiver.Type: IrExnType { Name: { } en } } ef:
                return $"({Names.Qualified(Names.ExnField(en, ef.Field))} {Expr(ef.Receiver)})";

            // R19.2. Building an exception is a pure function of its arguments.
            case IrNewException ne:
                return ne.Args.IsEmpty
                    ? $"({Names.Qualified(Names.ExnNew(ne.Class))} ())"
                    : $"({Names.Qualified(Names.ExnNew(ne.Class))} {string.Join(" ", ne.Args.Select(a => $"({Expr(a)})"))})";

            // R31.11. `list!.head` in a ring node's member: the node is read for its back
            // pointer, and the owner is read through it, as the box the member was given.
            case IrField { Receiver: IrField { Receiver: IrVar { Name: Names.This }, Field: var obf } } obr when
                _method is not null && OwnerBorrows is not null &&
                OwnerBorrows.TryGetValue(_method.Name, out var obm) && obm.Field == obf:
            {
                var nodeRead = Fresh();
                var thisBinder = _slots.TryGetValue(Names.This, out var obs) ? obs.Binder : Names.Local(Names.This);
                Line($"let {nodeRead} = {Names.ClassModule(obm.Node.Name)}.{Frontend.Region.ReadOf(obm.Node.Name)} {thisBinder};");
                var ownerRead = Fresh();
                Line($"let {ownerRead} = {Frontend.Region.Module}.read_owner {OwnerBorrow.Binder} " +
                     $"{nodeRead}.{Names.ClassProjection(obm.Node.Name, obf)};");
                return $"{ownerRead}.{Names.ClassProjection(obm.Owner.Name, obr.Field)}";
            }

            case IrField { Receiver: IrVar pv } pf when
                _slots.TryGetValue(pv.Name, out var pobj)
                && pobj is { Kind: SlotKind.Value or SlotKind.Cell, Type: IrClassType pc }
                && classes is not null && classes.TryGetValue(pc.Name, out var pdecl)
                && pdecl.IsPlain:
            {
                if (!Reachable(pobj, pf.Loc, pf.Field)) return "()";
                // A cell slot holds the *reference*, so it is read first and the box is
                // projected out of what was read; a value slot already is the reference.
                var precv = pobj.Kind is SlotKind.Cell ? Expr(pv) : pobj.Binder;
                var pt = Fresh();
                // R27.5. A region object is read through the region its owner holds.
                if (pdecl.IsRegion)
                    Line($"let {pt} = {Names.ClassModule(pc.Name)}.{Frontend.Region.ReadOf(pc.Name)} {precv};");
                else
                Line($"let {pt} = B.op_Bang {precv};");
                return $"{pt}.{Names.ClassProjection(pc.Name, pf.Field)}";
            }

            // R3.8. A field of an object lives behind a box, so reading it is a memory
            // operation, not a projection: the object is dereferenced and the resulting
            // representation projected. Legal only between the opening `unfold` and the
            // closing `fold`, which is exactly where a method body lives.
            case IrField { Receiver: IrVar ov } f when
                _slots.TryGetValue(ov.Name, out var obj) && obj is { Kind: SlotKind.Object, Type: IrClassType oc }:
            {
                if (!Reachable(obj, f.Loc, f.Field)) return "()";
                var t = Fresh();
                if (f.Peer && ov.Name != Names.This && !obj.Open && !_objects.Any(o => o.Name == ov.Name) && !_peerOpen.Contains(ov.Name))
                {
                    PeerOpen(obj, oc, () => Line($"let {t} = B.op_Bang {obj.NonNull};"));
                    return $"{t}.{Names.ClassProjection(oc.Name, f.Field)}";
                }
                Line($"let {t} = B.op_Bang {obj.NonNull};");
                return $"{t}.{Names.ClassProjection(oc.Name, f.Field)}";
            }

            // R27.5. A field of a region object reached by any expression (`Left!.Left`) is
            // read through the region, as from a local.
            case IrField { Receiver.Type: IrClassType rc } rf when IsRegionType(rc):
            {
                var rrecv = Expr(rf.Receiver);
                var rt = Fresh();
                Line($"let {rt} = {Names.ClassModule(rc.Name)}.{Frontend.Region.ReadOf(rc.Name)} {Atom(rrecv)};");
                return $"{rt}.{Names.ClassProjection(rc.Name, rf.Field)}";
            }

            case IrField f:
            {
                // R3.5. A field read of a value type is a pure projection: no memory is
                // touched beyond whatever reading the receiver already required.
                var receiver = Expr(f.Receiver);
                if (f.Receiver.Type is not IrNamedType named)
                {
                    diagnostics.Unsupported(f.Loc, $"The field access `.{f.Field}`");
                    return "()";
                }
                return $"{receiver}.{Names.Projection(named.Name, f.Field)}";
            }

            // R12.4. Allocating a `[Plain]` object: build the record, box it. `B.alloc`
            // carries no deallocation obligation, which is the same assumption R6.9 makes
            // about `new T[n]` and for the same reason — C# has a collector.
            case IrAlloc al:
            {
                var box = Fresh();
                // R27.6. A region object is allocated into its owner's region.
                if (classes is not null && classes.TryGetValue(al.Class, out var ad) && ad.IsRegion)
                {
                    Line($"let {box} = {Frontend.Region.Module}.alloc {AllocRecord(al)};");
                    return box;
                }
                Line($"let {box} = B.alloc {AllocRecord(al)};");
                // R10.6b, again: `new` is non-null, and the proof of it is a library call.
                Line($"B.pts_to_not_null {box};");
                return box;
            }

            case IrNew n:
            {
                var fields = n.Fields.Select((f, i) =>
                    (i == 0 ? Names.Projection(n.Struct, f.Field) : Names.Field(f.Field))
                    + " = " + Expr(f.Value)).ToImmutableArray();
                // Parenthesised: in statement position Pulse reads a bare `{ … }` as a block.
                return "({ " + string.Join("; ", fields) + " })";
            }

            case IrUnary u:
                return Unary(u);
            // R12.3. A null test on a `[Plain]` reference in value position is the
            // representation's own question and nothing more: is the pointer null?
            // R31.13. A region node's back pointer to its owner (`node.list != null`) is a
            // box stored in the node's record: the test asks only whether it is null.
            case IrBinary { Op: BinOp.Eq or BinOp.Ne } ob when
                (ob.Left is IrNull ? ob.Right : ob.Right is IrNull ? ob.Left : null) is
                    IrField { Type: IrClassType { Nullable: true }, Receiver.Type: var backOf } back &&
                IsRegionType(backOf) && !IsRegionType(back.Type):
            {
                // Bound on its own, so the solver sees `is_null`'s refinement (`b <==> x == null`).
                var t = Expr(back);
                var name = Fresh();
                Line($"let {name} = B.is_null {t};");
                return ob.Op is BinOp.Eq ? name : $"(not {name})";
            }

            case IrBinary { Op: BinOp.Eq or BinOp.Ne } pb when PlainNullTest(pb) is { } pt:
            {
                var t = Expr(pt.Tested);
                var name = Fresh();
                Line(pb.Op is BinOp.Eq
                    ? $"let {name} = B.is_null {t};"
                    : $"let {name} = not (B.is_null {t});");
                return name;
            }

            case IrBinary b:
                return Binary(b);

            case IrConditional c:
            {
                var cond = Expr(c.Cond);
                var whenTrue = Capture(() => Expr(c.Then));
                var whenFalse = Capture(() => Expr(c.Else));
                return Branch(cond, whenTrue, whenFalse);
            }

            case IrCall { Kind: CalleeKind.Method } call:
                return Call(call, Fresh());

            // R27.39. A `[Callback]` parameter is called with the node alone: the trace and
            // the region it is held at are the callback type's ghost arguments.
            case IrCall { Kind: CalleeKind.Callback } cb when _slots.TryGetValue(cb.Callee, out var cbSlot):
            {
                var node = Expr(cb.Args[1]);
                var t = Fresh();
                Line($"let {t} = {cbSlot.Binder} {node};");
                return t;
            }

            // R27.39. A lifted lambda is passed as its protocol and its callback, both
            // applied to what it captures; the protocol is folded at the empty trace here,
            // and unfolded at whatever trace the callee left it, after the call.
            case IrLambdaRef lr:
            {
                var caps = lr.Captures.Select(Expr).ToList();
                var applied = string.Join(" ", lr.TypeArguments.Select(Types.Atom).Concat(caps));
                var protocol = $"({Names.LambdaProtocol(lr.Method)} {applied})".Replace(" )", ")");
                var e = Types.Atom(new IrUserSpecType("ValueTuple", Frontend.WellKnown.TupleType,
                    [lr.Callback.View, lr.Callback.Result]));
                Line($"fold ({protocol} (Seq.empty #{e}));");
                _lambdaProtocols.Add(protocol);
                // R32.11. A bounded parameter takes the lambda's bound, or none, before it.
                var callback = $"({Names.LambdaCallback(lr.Method)} {applied})".Replace(" )", ")");
                if (!lr.Callback.Bounded) return $"{protocol} {callback}";
                var bound = lr.Bounded
                    ? $"({Names.LambdaBound(lr.Method)} {applied})".Replace(" )", ")")
                    : "Pulse.Lib.CSharp.Callback.max_bound";
                return $"{protocol} {bound} {callback}";
            }

            case IrConvert cv:
                return Convert(cv);

            // R13.3. Run the effect where it stands, then yield the value. Emitting the
            // prelude through the ordinary statement path is what makes the effect land
            // in the right place: inside a loop guard it is re-run every iteration, and
            // inside a captured short-circuit branch it is run only when that branch is.
            case IrStmtExpr se:
                foreach (var s in se.Prelude) Statement(s, _plan!);
                return Expr(se.Value);

            // R21.7. A raise in expression position is a computation of any type, so it is
            // always a line of its own: a branch holding one is a Pulse `if`, never F*'s.
            // Pulse gives a `raise` with no expected type the type `unit` and leaves
            // `pure False` behind it; the value of the expression's own type is then
            // `false_elim`, so the branch has the type the other arm has.
            case IrRaise ra:
            {
                var exn = Fresh();
                Line($"let {exn} = {Expr(ra.Exception)};");
                if (_tryMarks.Count == 0)
                {
                    if (NeedsEpilogue) CloseObjects(_method!, _plan!);
                }
                else
                {
                    DropLocals(null, _tryMarks[^1]);
                }
                if (ra.Type is not { } raType) return $"raise {exn}";
                Line($"raise {exn};");
                Line("let _ = elim_pure_explicit False;");
                return $"(FStar.Pervasives.false_elim #({Types.Render(raType)}) ())";
            }

            default:
                diagnostics.Unsupported(expr.Loc, $"`{expr.GetType().Name}` in executable code");
                return "()";
        }
    }

    /// <summary>Emits a call, binding its result to <paramref name="binder"/>.</summary>
    /// <summary>R27.39. The protocols of the lambdas passed to the call being emitted.</summary>
    private readonly List<string> _lambdaProtocols = [];

    private string Call(IrCall call, string binder)
    {
        if (PeerRegionCall(call) is { } peer) return PeerCall(call, binder, peer.Slot, peer.Region);
        var declared = PulseEmitter.DispatchOwner(classes, slots, call.Callee);
        var owner = PulseEmitter.DispatchClass(classes, slots, call);

        // R9.16. An indexed reference is owned through `class_C__inv_at`, and that is what
        // a dispatching wrapper's `_at` form asks for; anything else — a base-typed
        // parameter of an ordinary method, an argument passed as data — asks for the plain
        // invariant, so the index is dropped here, where it is in the way.
        // The arguments are computed first, because one of them may *be* a conversion
        // (R9.15) and the reference it produces is what the index has to be read off.
        var raw = call.Args.Select(Expr).ToImmutableArray();

        // R10.2b, at an argument. Under R10.2 the reference itself needs no coercion, but
        // its *invariant* is still stated through R10.3a's abbreviation, so `Inject` is
        // called here for the same reason it is at a return (R4.13) and at a field write
        // (R10.4). It returns the text unchanged; what it may emit is the rewrite.
        var args = raw
            .Select((text, i) => Inject(
                i < call.ParamTypes.Length ? call.ParamTypes[i] : null, call.Args[i], text))
            .ToImmutableArray();

        // R31.11. A ring node's member that reads its owner is called from a method of the
        // owner's class, on a node of the receiver's region: the receiver's box is passed as
        // the owner, and the callee's precondition says the node points back to it.
        if (OwnerBorrows is not null && OwnerBorrows.TryGetValue(call.Callee, out var cob) && call.HasReceiver && args.Length > 0)
        {
            if (_method?.DeclaringClass == cob.Owner.Name && _slots.TryGetValue(Names.This, out var ownerSlot) &&
                _objects.Any(o => o.Name == Names.This))
                args = args.Insert(1, $"(hide {ownerSlot.Binder})");
            else
                diagnostics.Error("PALCS0781", call.Loc,
                    $"`{call.Callee}` reads the `{cob.Owner.Name}` its node points back to through `{cob.Field}`, " +
                    $"so it is called only from an instance method of `{cob.Owner.Name}` on a node of the receiver's " +
                    "ring, with the receiver open (doc/translation.md R31.11).");
        }

        var indexed = false;
        for (var i = 0; i < raw.Length; i++)
        {
            if (SlotByBinder(raw[i]) is not { Index: not null } ix) continue;
            if (i == 0 && call.HasReceiver && owner is not null) { indexed = true; continue; }
            Forget(ix);
        }

        // R4.9c, R4.12b, on the calling side. A parameter the callee consumes takes the
        // argument's invariant with it, so the caller stops owning it here — it must not be
        // folded back at the end of the block (R4.14) and must not be handed to anything
        // else. C# would leave the name usable, so PALCS0550 says so at the next use rather
        // than leaving Pulse to fail on a resource that moved several statements earlier.
        Moved(call, raw);
        // R9.12. A call resolved to an `abstract` declaration is a virtual call: it goes
        // to the dispatching wrapper, which recovers the object and runs its vtable slot.
        // Nothing else about the call changes — the arguments, the implicit model binder
        // and the permission are found by the same rules as for a direct call, because
        // R9.9 gives the wrapper the same contract shape a direct method has.
        // R9.18. The wrapper's class is the receiver's static one; the member's name is
        // the one the class that declared it gave it, all the way down.
        var member = declared is null ? "" : Names.Member(call.Callee, declared);
        var callee = owner is not null
            ? indexed
                ? Names.DispatchAt(owner, member)
                : Names.Dispatch(owner, member)
            : Names.Function(call.Callee);

        // R9.7, on the calling side. An `override`'s contract is written at the model of
        // the class that declared the method, so its receiver is owned through
        // `class_C__as_B` — C's own invariant read at B's model — and not through
        // `class_C__inv`. A caller naming the override directly, which is what a call at
        // the leaf's own static type is, therefore has to hand the receiver over the same
        // way. The bracket is R9.14's view, opened and closed around one call; it is the
        // same two ghost steps R9.15's conversion emits, for the same reason, and it is
        // not a proof step but the rendering of "this reference is being used as a B".
        var view = Bracket(owner is null ? call : null, raw);

        // R14.5. Type arguments apply first, positionally, in declaration order. A generic
        // method with no value parameters still applies them, so the `()` below is reached
        // only by a call that is nullary in both senses.
        var tyArgs = call.TypeArguments.Select(Types.Atom).ToImmutableArray();
        var applied = args.Length == 0 && tyArgs.Length == 0
            ? "()"
            : string.Join(" ", tyArgs.Concat(args));

        // R22.15. A call on the receiver from inside one of its own methods, with the
        // receiver open: the callee's contract asks for the invariant, so the bracket is
        // closed around the call and reopened after it. The fold is checked like any
        // other -- an invariant that does not hold at the call is Pulse's error, not an
        // assumption -- and the reopening names whatever model the callee left.
        var self = call.HasReceiver && raw.Length > 0 && _windows.Count == 0 && !_receiverClosedForThrow
            ? _objects.FirstOrDefault(o => o.Binder == raw[0] && o.ViewBase is null)
            : null;
        // R27.13. The callee's contract may hold the receiver at its heaps, and the caller
        // may hold it the other way: the two forms are converted around the call.
        var wantsHeap = call.HasReceiver && raw.Length > 0 && heapIndexed is not null &&
                        heapIndexed.ContainsKey(call.Callee);
        // R27.23. An `[Open]` callee takes the receiver open, as the caller holds it.
        var openCallee = openMethods?.Contains(call.Callee) == true;
        if (openCallee) self = null;
        var closedRecv = !openCallee && self is null && call.HasReceiver && raw.Length > 0 &&
                         SlotByBinder(raw[0]) is { Kind: SlotKind.Object, ViewBase: null, Type: IrClassType { Nullable: false } } cr &&
                         !_objects.Any(o => o.Binder == cr.Binder) && owner is null
            ? cr : null;
        var haveHeap = (self ?? closedRecv)?.Heaps.IsEmpty == false;
        var convert = (self ?? closedRecv) is { } recvSlot && haveHeap != wantsHeap
            ? $"{Names.ClassModule(((IrClassType)recvSlot.Type).Name)}."
            : null;
        var recvClass = (self ?? closedRecv)?.Type is IrClassType rcls ? rcls.Name : null;
        // R27.58. A receiver that is an object the receiver of this method owns (a field
        // read off it, held by its invariant without heaps) is converted the same way.
        if (convert is null && wantsHeap && !openCallee && self is null && closedRecv is null &&
            SlotByBinder(raw[0]) is null && call.Args[0] is IrField &&
            call.Args[0].Type is IrClassType { Nullable: false } frc)
        {
            convert = $"{Names.ClassModule(frc.Name)}.";
            recvClass = frc.Name;
        }
        var fieldRecv = convert is not null && self is null && closedRecv is null;
        // R27.59. A field still open from an earlier call is closed before another call on it.
        if (call.HasReceiver && call.Args.Length > 0 && call.Args[0] is IrField { Field: var calledField })
            CloseFieldRegion(calledField);
        var atModel = self is not null && Pristine && self.PreModel is not null && self.ViewBase is null;
        if (atModel) CloseAtModel(self!, null);
        else if (self is not null) CloseObject(_method!, self);
        // R27.38. A callee that may raise hands its exception, with whatever the caller
        // holds, to the caller's `raises`, which owns the objects closed. An object only
        // read (a borrowing struct's owner) is closed around the call, and reopened at the
        // same model after it: the call cannot have changed it.
        var bracketed = raising?.Contains(call.Callee) == true && _windows.Count == 0 && !_receiverClosedForThrow && !_catching
            ? _objects.Where(o => o != self && o.Fraction is not null && o.ViewBase is null &&
                                  o.PostModel == o.PreModel && !raw.Contains(o.Binder) &&
                                  // R32.9. Not the holder whose owned field is the receiver
                                  // (R27.58): the field's invariant is unfolded from it.
                                  !(fieldRecv && o.Name == Names.This)).ToList()
            : [];
        foreach (var o in bracketed) CloseObject(_method!, o);
        // R33.22. A receiver held whole and opened (R4.10), around a callee on something
        // else that may raise: the exception leaves with it closed, so it is closed before
        // the call -- its invariant must hold there -- and reopened after it. Not around a
        // call on an object the receiver owns (`_set.Add(…)`), whose permission the open
        // receiver holds: that call's own raising path closes the receiver (R27.38).
        var closedAround = raising?.Contains(call.Callee) == true && !call.DoesNotReturn && _windows.Count == 0 &&
                           !_receiverClosedForThrow && self is null &&
                           !call.Args.Any(a => a is IrField { Type: IrClassType })
            ? _objects.Where(o => o.Name == Names.This && o.Fraction is null && o.ViewBase is null &&
                                  !o.Open && o.Heaps.IsEmpty && !raw.Contains(o.Binder) && !bracketed.Contains(o)).ToList()
            : [];
        foreach (var o in closedAround) CloseObject(_method!, o);
        if (convert is not null)
            Line($"{convert}{(wantsHeap ? Names.ClassToHeap(recvClass!) : Names.ClassOfHeap(recvClass!))} {raw[0]};");
        Line($"let {binder} = {callee} {applied};");
        foreach (var protocol in _lambdaProtocols)
        {
            var tr = FreshValue("trace");
            Line($"with {tr}. assert ({protocol} {tr});");
            Line($"unfold ({protocol} {tr});");
        }
        _lambdaProtocols.Clear();
        foreach (var o in bracketed) Line(Unfold(o) + ";");
        foreach (var o in closedAround) Reopen(o, null);
        // R27.59. A region pointer handed back by a call on an owned field points into the
        // field's region, at the heap the call left it at: the field is kept open there, so
        // that the pointer can be read, until the receiver is closed.
        if (fieldRecv && wantsHeap && call.ResultType is IrClassType { } rpt && IsRegionType(rpt) &&
            classes is not null && classes.TryGetValue(recvClass!, out var fdecl) &&
            _objects.FirstOrDefault(o => o.Name == Names.This) is { } holder)
        {
            var fk = new IrClassType(recvClass!);
            var fm = FreshValue(recvClass!);
            var fhs = RegionsOf(fdecl).Select(k => FreshValue(Frontend.Region.HeapBinder(k.Name))).ToList();
            var fargs = $"{raw[0]} {holder.PermArg}{fm} {string.Join(" ", fhs)}";
            Line($"with {fm} {string.Join(" ", fhs)}. assert ({InvHeap(fk)} {fargs});");
            Line($"unfold {InvHeap(fk)} {fargs};");
            _fieldOpen[((IrField)call.Args[0]).Field] = (fk, fargs, holder.Fraction,
                [.. RegionsOf(fdecl).Select(k => k.Name)], fhs, []);
        }
        else if (convert is not null && (closedRecv is not null || fieldRecv))
            Line($"{convert}{(wantsHeap ? Names.ClassOfHeap(recvClass!) : Names.ClassToHeap(recvClass!))} {raw[0]};");
        if (self is not null)
        {
            // R27.50. A receiver at its model that the callee took without its heaps is
            // given them back before it is reopened, so that its heaps are named by the
            // reopening rather than hidden in it, where a join cannot abstract them.
            var heapsBack = atModel && convert is not null && !wantsHeap;
            if (heapsBack) Line($"{convert}{Names.ClassToHeap(recvClass!)} {raw[0]};");
            _lastReopen = (self, wantsHeap ? [.. heapIndexed![call.Callee]]
                : heapsBack ? [.. self.Heaps.Select(h => h.Region)] : null);
            var reopenStart = _lines.Count;
            Reopen(self, _lastReopen.Value.Heaps);
            _keptReopen = atModel && readOnlyMethods?.Contains(call.Callee) == true &&
                          (wantsHeap || heapsBack || self.Heaps.IsEmpty)
                ? (reopenStart, _lines.Count) : null;
        }
        Close(view);
        // R10.6c. The binder a call produced an object under is the name the context holds
        // that object's invariant under, exactly as for a `new` (R10.2b) or a parameter
        // (R10.6b). Recording it here is what stops R4.13 from re-binding it on the way
        // out of a method that hands back what it called: `let t' = t;` is not a rule of
        // the translation, and the frame rule cannot see through it.
        if (call.ResultType is IrClassType rk && !(classes?.TryGetValue(rk.Name, out var rc) == true && rc.IsPlain))
            _objectResults.Add(binder);
        return binder;
    }

    /// <summary>
    /// R4.9c, R4.12b. Records that a call took ownership of its consumed arguments.
    /// </summary>
    private void Moved(IrCall call, ImmutableArray<string> args)
    {
        if (consumed is null || !consumed.TryGetValue(call.Callee, out var positions)) return;
        for (var i = 0; i < args.Length; i++)
        {
            if (!positions.Contains(i)) continue;
            if (SlotByBinder(args[i]) is not { Kind: SlotKind.Object } obj) continue;
            _slots[obj.Name] = obj with { Kind = SlotKind.Value, Index = null, Given = call.Callee };
            _objectLocals.RemoveAll(l => l.Binder == obj.Binder);
        }
    }

    /// <summary>
    /// R9.7. Presents a direct call's receiver at the base model its <c>override</c>'s
    /// contract is written at, and reports what has to be closed afterwards.
    /// </summary>
    private (Slot Slot, string Class, string Base)? Bracket(IrCall? call, ImmutableArray<string> args)
    {
        if (call is null || !call.HasReceiver || args.Length == 0) return null;
        if (overrides is null || !overrides.TryGetValue(call.Callee, out var b)) return null;
        if (SlotByBinder(args[0]) is not { } recv) return null;
        // The method's own receiver is already open (R4.10) and already viewed at its base
        // by the signature, so a call on `this` needs neither half of the bracket.
        if (_objects.Any(o => o.Binder == recv.Binder)) return null;
        if (recv.Type is not IrClassType k) return null;

        var mod = Names.ClassModule(k.Name);
        var own = FreshValue(k.Name);
        Line($"with {own}. assert ({mod}.{Names.ClassInv(k.Name)} {recv.Binder} {recv.PermArg}{own});");

        // R9.15e, on a receiver that is never cast. The contract this call is checked
        // against is the base's (R9.7), so the same naming the cast needs is needed here:
        // a model left as an application of `forget` is only known at the derived class's
        // refinement (R9.5), and the base's own observations cannot be unfolded on it.
        var basis = FreshValue(b);
        Line($"let {basis} : erased ({Names.ClassModule(b)}.{Names.ClassModel(b)}) = " +
             $"hide ({mod}.{Names.ClassForget(k.Name)} {own});");
        Line($"fold ({mod}.{Names.ClassAsBase(k.Name, b)} {recv.Binder} " +
             $"{recv.PermArg}(reveal {basis}));");
        return (recv, k.Name, b);
    }

    /// <summary>Closes <see cref="Bracket"/>, at whatever model the call left behind.</summary>
    private void Close((Slot Slot, string Class, string Base)? view)
    {
        if (view is not { } v) return;
        var mod = Names.ClassModule(v.Class);
        var model = FreshValue(v.Class);
        Line($"with {model}. assert ({mod}.{Names.ClassAsBase(v.Class, v.Base)} " +
             $"{v.Slot.Binder} {v.Slot.PermArg}{model});");
        Line($"unfold ({mod}.{Names.ClassAsBase(v.Class, v.Base)} " +
             $"{v.Slot.Binder} {v.Slot.PermArg}{model});");
    }

    private string Unary(IrUnary u)
    {
        var operand = Expr(u.Operand);
        var module = Types.Module((u.Operand.Type as IrPrim)?.Kind ?? PrimKind.Int);
        return u.Op switch
        {
            UnOp.Not => $"(not {operand})",
            UnOp.Neg => $"({module}.sub {Types.Literal(0, u.Operand.Type)} {operand})",
            UnOp.BitNot => $"({module}.lognot {operand})",
            _ => operand,
        };
    }

    private string Binary(IrBinary b)
    {
        // R6.3. `&&` and `||` short-circuit, so the right operand is evaluated inside a
        // branch. This is the ordinary compositional expansion, used identically in a
        // loop guard, an `if` condition and an assignment's right-hand side.
        if (b.Op is BinOp.And or BinOp.Or)
        {
            var left = Expr(b.Left);
            var right = Capture(() => Expr(b.Right));
            var shortCircuit = new Captured([], b.Op == BinOp.And ? "false" : "true");
            return b.Op == BinOp.And
                ? Branch(left, right, shortCircuit)
                : Branch(left, shortCircuit, right);
        }

        // R24.7. An array compared with `null` asks whether the reference is null.
        if (b.Op is BinOp.Eq or BinOp.Ne &&
            (b.Left is IrNull ? b.Right : b.Right is IrNull ? b.Left : null) is { Type: IrArrayType } tested)
        {
            var reference = Expr(tested);
            return b.Op is BinOp.Eq ? $"(A.is_null {reference})" : $"(not (A.is_null {reference}))";
        }

        var l = Expr(b.Left);
        var r = Expr(b.Right);

        // R20.9. `x == y` on a `T?`, or on a `[SpecType]` value, is F*'s decidable
        // equality; C# lifts `int`'s `==` to `int?` exactly as `option`'s `=` does.
        // A test against `null` is `None?`, which needs no equality on the element type --
        // and so also serves an `option` of a `noeq` model.
        if (b.Op is BinOp.Eq or BinOp.Ne && (b.Left is IrNull || b.Right is IrNull) &&
            (b.Left.Type is IrOptionType || b.Right.Type is IrOptionType))
            return $"({(b.Op is BinOp.Eq ? "None?" : "Some?")} {Atom(b.Left is IrNull ? r : l)})";
        if (b.Op is BinOp.Eq or BinOp.Ne && b.Left.Type is IrOptionType or IrUserSpecType)
        {
            // R33.25. `c != EqualityComparer<T>.Default` for a nullable `c`: the other side
            // is a value that is there.
            if (b.Left.Type is IrOptionType && b.Right.Type is IrUserSpecType) r = $"(Some {Atom(r)})";
            else if (b.Left.Type is IrUserSpecType && b.Right.Type is IrOptionType) l = $"(Some {Atom(l)})";
            return b.Op is BinOp.Eq ? $"({l} = {r})" : $"(not ({l} = {r}))";
        }

        // R27.8. Two references to objects of a `[Region]` class are compared as pointers.
        if (b.Op is BinOp.Eq or BinOp.Ne && IsRegionType(b.Left.Type) && IsRegionType(b.Right.Type))
            return b.Op is BinOp.Eq
                ? $"(Pulse.Lib.CSharp.RefEq.ref_eq {Atom(l)} {Atom(r)})"
                : $"(not (Pulse.Lib.CSharp.RefEq.ref_eq {Atom(l)} {Atom(r)}))";

        // R27.50. So is `x == this` of an owner class: each is a box. R31.8: `x` may be
        // nullable (a node's `list`), a null box being unequal to `this`. Other comparisons
        // of two objects stay refused (R18.1).
        if (b.Op is BinOp.Eq or BinOp.Ne &&
            (b.Left is IrVar { Name: Names.This } || b.Right is IrVar { Name: Names.This }) &&
            b.Left.Type is IrClassType lc && b.Right.Type is IrClassType rc &&
            lc.Name == rc.Name && classes is not null && classes.ContainsKey(lc.Name))
            return b.Op is BinOp.Eq
                ? $"(Pulse.Lib.CSharp.RefEq.ref_eq {Atom(l)} {Atom(r)})"
                : $"(not (Pulse.Lib.CSharp.RefEq.ref_eq {Atom(l)} {Atom(r)}))";

        // R18.1. R6.4 reads an operator's implementation off its operand type, and this
        // defaulted to `Int32` for an operand that was not primitive at all. `a == b` on
        // two objects then emitted `I32.eq` applied to two boxes: not a translation, and
        // not caught until F* refused to typecheck a file the user never asked to read.
        if (b.Left.Type is not IrPrim && b.Left.Type is not null)
        {
            diagnostics.Error("PALCS0593", b.Loc,
                $"`{b.Op}` is applied to operands of type `{b.Left.Type}`, and R6.4 gives an " +
                "operator a meaning only at a primitive type (doc/translation.md R18.1). " +
                (b.Left.Type is IrClassType
                    ? "Comparing two references is object identity, which the scheme has no story " +
                      "for: `Box` has a decidable equality, but nothing relates it to the ownership " +
                      "discipline, and two equal references are not interchangeable in a context " +
                      "that owns one of them. Compare the objects' models instead."
                    : "Compare values the rules give an operator for."));
            return "()";
        }

        // R20.3. `decimal` and `string` are values with decidable equality; a decimal is
        // ordered by `Pulse.Lib.CSharp.Decimal`'s comparisons. Nothing else is modelled.
        if (b.Left.Type is IrPrim { Kind: PrimKind.Decimal or PrimKind.String } valueType)
        {
            var dec = valueType.Kind == PrimKind.Decimal;
            switch (b.Op)
            {
                case BinOp.Eq: return $"({l} = {r})";
                case BinOp.Ne: return $"(not ({l} = {r}))";
                case BinOp.Lt when dec: return $"(D.lt {l} {r})";
                case BinOp.Le when dec: return $"(D.le {l} {r})";
                case BinOp.Gt when dec: return $"(D.gt {l} {r})";
                case BinOp.Ge when dec: return $"(D.ge {l} {r})";
            }
            diagnostics.Error("PALCS0624", b.Loc,
                $"`{b.Op}` on `{valueType}`. A `decimal` translates with its comparisons and " +
                "equality only, and a `string` with equality only (doc/translation.md R20.3).");
            return "()";
        }

        var module = Types.Module((b.Left.Type as IrPrim)?.Kind ?? PrimKind.Int);

        // R13.5. C# takes a shift distance as an `int` whatever the operand's width, but
        // every one of F*'s `shift_left`/`shift_right` takes a `UInt32.t` — including
        // `Int64`'s and `UInt8`'s. The distance is therefore converted rather than
        // rendered at the operand's type, which is what it would otherwise inherit.
        if (b.Op is BinOp.Shl or BinOp.Shr &&
            (b.Right.Type as IrPrim)?.Kind is { } shiftKind && shiftKind != PrimKind.UInt)
        {
            r = Types.CastFunction(shiftKind, PrimKind.UInt) is { } toU32
                ? $"({toU32} {r})"
                : r;
        }

        var op = b.Op switch
        {
            BinOp.Add => "add", BinOp.Sub => "sub", BinOp.Mul => "mul",
            BinOp.Div => "div", BinOp.Rem => "rem",
            BinOp.BitAnd => "logand", BinOp.BitOr => "logor", BinOp.BitXor => "logxor",
            BinOp.Shl => "shift_left", BinOp.Shr => "shift_right",
            BinOp.Lt => "lt", BinOp.Le => "lte", BinOp.Gt => "gt", BinOp.Ge => "gte",
            BinOp.Eq => "eq", BinOp.Ne => "eq",
            _ => null,
        };

        if (op is null)
        {
            diagnostics.Unsupported(b.Loc, $"The operator `{b.Op}` in executable code");
            return "()";
        }

        // R34.12. A wrapping `<<` on `int`: C# masks the distance to five bits and keeps
        // the low 32 bits of the product. An unsigned `shift_left` already wraps.
        if (b.Wraps && b.Op is BinOp.Shl && b.Left.Type is IrPrim { Kind: PrimKind.Int })
            return $"(Pulse.Lib.CSharp.Int32.shift_left_wrap {l} {r})";

        // R22.14. A wrapping add/sub/mul: `_mod` for an unsigned width, which F* provides,
        // and the library's `_wrap` for `int`, which F* does not.
        if (b.Wraps && b.Op is BinOp.Add or BinOp.Sub or BinOp.Mul &&
            b.Left.Type is IrPrim { IsMachineInt: true } wp)
        {
            if (wp.Kind is PrimKind.Int) return $"(Pulse.Lib.CSharp.Int32.{op}_wrap {l} {r})";
            if (wp.Kind is PrimKind.UInt or PrimKind.ULong or PrimKind.UShort or PrimKind.Byte)
                return $"({module}.{op}_mod {l} {r})";
            diagnostics.Unsupported(b.Loc, $"`[Wrapping]` arithmetic at `{wp.Kind}`");
            return "()";
        }

        // Booleans have no machine-integer module; they use F*'s own operators.
        if (b.Left.Type is IrPrim { Kind: PrimKind.Bool })
        {
            var boolean = b.Op switch
            {
                BinOp.Eq => $"({l} = {r})",
                BinOp.Ne => $"(not ({l} = {r}))",
                BinOp.BitAnd => $"({l} && {r})",
                BinOp.BitOr => $"({l} || {r})",
                BinOp.BitXor => $"(not ({l} = {r}))",
                _ => null,
            };
            if (boolean is not null) return boolean;
            diagnostics.Unsupported(b.Loc, $"The Boolean operator `{b.Op}`");
            return "()";
        }

        var call = $"({module}.{op} {l} {r})";
        return b.Op == BinOp.Ne ? $"(not {call})" : call;
    }

    /// <summary>R20.6. The total preorder <c>OrderBy</c> sorts by, for a key of this type.</summary>
    private static string OrderOf(IrType key) => key switch
    {
        IrPrim { Kind: PrimKind.Decimal } => "D.le",
        IrPrim p when p.IsMachineInt => $"(fun (x y: {Types.Machine(p.Kind)}) -> {Types.Module(p.Kind)}.lte x y)",
        _ => "(fun _ _ -> true)",
    };

    private static string Atom(string term) =>
        term.Contains(' ') && !term.StartsWith('(') ? $"({term})" : term;

    private string Convert(IrConvert cv)
    {
        // R9.16. A cast between reference types is a statement, not an expression: it
        // moves a resource, and the name it moves it to is the one every later mention
        // has to use. Anywhere else it would silently be the identity.
        if (cv.Target is IrClassType target)
        {
            // R9.15's conversion has a value, so it is an expression like any other. R9.16's
            // does too, but it also binds the *model equation* the caller reasons with, and
            // that equation needs a name — so the downcast stays a local declaration.
            if (Ancestors((cv.Operand.Type as IrClassType)?.Name, target.Name) is not null)
                return UpcastExpr(cv, target);

            diagnostics.Error("PALCS0547", cv.Loc,
                $"A cast down to `{target.Name}` is emitted only as the initialiser of a " +
                $"local declaration (R9.16): write `{target.Name} x = …;` and use `x`.");
            return "()";
        }

        var operand = Expr(cv.Operand);
        var from = (cv.Operand.Type as IrPrim)?.Kind;
        var to = (cv.Target as IrPrim)?.Kind;
        if (from == to) return operand;

        // R13.1. A numeric width conversion is `FStar.Int.Cast`'s corresponding function.
        //
        // Note what is *not* here: a proof obligation. Everywhere else pal-csharp insists
        // arithmetic does not overflow, because C#'s wrapping `+` is almost always an
        // accident. A cast is the opposite — writing `(byte)v` is the programmer asking
        // for truncation, and C#'s unchecked context, which is the default, defines it to
        // truncate. `FStar.Int.Cast`'s narrowing functions are modular, so they mean the
        // same thing (F48). Demanding `0 <= v < 256` here would be the emitter inventing a
        // refusal for an operation the source language defines (§0 rule 3); a user who
        // wants exactness proves the range themselves and F49 hands it back.
        if (from is { } f && to is { } t)
        {
            // `ushort` and `char` are both `U16.t`, so the conversion between them is the
            // identity and there is no cast function to name.
            var fn = Types.CastFunction(f, t);
            if (fn is null && Types.Machine(f) == Types.Machine(t)) return operand;
            if (fn is not null) return $"({fn} {operand})";
        }

        diagnostics.Unsupported(cv.Loc, $"The conversion from `{from}` to `{to}`",
            "Only conversions between C#'s integer types are translated.");
        return operand;
    }

    // =======================================================================
    // Capturing sub-blocks
    // =======================================================================

    private readonly record struct Captured(ImmutableArray<EmittedLine> Lines, string Term,
        (Slot Self, ImmutableArray<IrClassType>? Heaps)? Reopened = null, int KeptTail = 0);

    /// <summary>
    /// Emits into a scratch buffer, so that a sub-block's let-bindings can be placed
    /// inside the branch or guard they belong to rather than hoisted out of it —
    /// hoisting would change evaluation order.
    /// </summary>
    private static readonly System.Text.RegularExpressions.Regex TotalReadLine =
        new(@"^\s*let t\d+ = (B\.op_Bang var_this|!var_\w+);\s*$");

    private static bool TotalRead(EmittedLine line) => TotalReadLine.IsMatch(line.Text);

    private Captured Capture(Func<string> emit)
    {
        var saved = _lines.Count;
        var savedReopen = _lastReopen;
        var savedKept = _keptReopen;
        _lastReopen = null;
        _keptReopen = null;
        var term = emit();
        var reopened = _lastReopen;
        var keptTail = _keptReopen is { } k && k.Start >= saved && k.End == _lines.Count ? k.End - k.Start : 0;
        _lastReopen = reopened ?? savedReopen;
        _keptReopen = savedKept;
        var captured = _lines.GetRange(saved, _lines.Count - saved);
        _lines.RemoveRange(saved, _lines.Count - saved);
        return new Captured([.. captured], term, reopened, keptTail);
    }

    /// <summary>
    /// A two-armed branch used as a value. Pulse permits this in any position, so
    /// short-circuiting needs no flag encoding (fact F8).
    /// </summary>
    private Captured Bound(string term) => Capture(() =>
    {
        var t = Fresh();
        Line($"let {t} = {term};");
        return t;
    });

    /// <summary>
    /// R27.50. An arm that closes the receiver around a call reopens it at a fresh record,
    /// and Pulse's join of a value-returning <c>if</c> keeps what one arm knows of a record
    /// only under that arm's condition. Where the receiver is still at its model, each arm
    /// instead ends with it closed at that model, which is one term on both sides, and the
    /// receiver is reopened once after the join.
    /// </summary>
    private Captured Reclosed(Captured arm, (Slot Self, ImmutableArray<IrClassType>? Heaps) r)
    {
        // An arm that ends by reopening the receiver after a callee that kept it at its
        // model already holds it closed at that model just before: it stops there, so
        // that nothing it learnt by reopening outlives the arm (Pulse cannot abstract a
        // heap that only pure facts still mention).
        if (arm.KeptTail > 0)
            return arm with { Lines = arm.Lines.RemoveRange(arm.Lines.Length - arm.KeptTail, arm.KeptTail), Reopened = r, KeptTail = 0 };
        var tail = Capture(() => { CloseAtModel(r.Self, r.Heaps); return arm.Term; });
        return arm with { Lines = arm.Lines.AddRange(tail.Lines), Reopened = r };
    }

    /// <summary>R27.50. Whether the open receiver is still at the model it was handed.</summary>
    private bool Pristine => RegionOwner && (_pristineLoops.Count == 0 || _pristineLoops.Peek()) && !_receiverDirty;

    /// <summary>
    /// R27.50. Pristine receivers are tracked for region owners only, whose writes
    /// `DirtiesReceiver` sees (fields and regions); an array field's contents are written
    /// through aliases it does not follow.
    /// </summary>
    private bool RegionOwner =>
        _method?.DeclaringClass is { } dc && classes is not null && classes.TryGetValue(dc, out var owner) &&
        RegionsOf(owner).Any() && !owner.Fields.Any(f => f.Type is IrArrayType);

    /// <summary>
    /// R27.50. Closes a receiver that is still at its model at that model, rather than at
    /// the abstraction of its record: the two are equal, and the model is one term
    /// wherever it is closed.
    /// </summary>
    private void CloseAtModel(Slot obj, ImmutableArray<IrClassType>? heaps)
    {
        var self = obj with { PostModel = obj.PreModel };
        ImmutableArray<IrClassType>? held = self.Heaps.IsEmpty ? null : [.. self.Heaps.Select(h => h.Region)];
        if ((heaps ?? held) is { } regions)
        {
            var klass = (IrClassType)self.Type;
            var hs = regions.Select(k => (k, FreshValue(Frontend.Region.HeapBinder(k.Name)))).ToList();
            foreach (var (k, h) in hs)
                Line($"with {h}. assert ({PulseEmitter.RegionAt(k, self.Fraction ?? "1.0R", h)});");
            Line($"fold {InvHeap(klass)} {self.Binder} {self.PermArg}{self.PreModel} " +
                 $"{string.Join(" ", hs.Select(x => x.Item2))};");
        }
        else CloseObject(_method!, self);
    }

    private string Branch(string cond, Captured whenTrue, Captured whenFalse)
    {
        // R6.3a. An arm that only reads locals or the open receiver's box does nothing
        // that can fail or be observed, so its reads are made ahead of the branch, which
        // is then F*'s: Pulse's join of a value-returning `if` keeps no relation between
        // its result and a read made in one arm.
        // Only where an arm reads the box: a branch over locals alone keeps its Pulse
        // `if`, whose arms the solver sees separately rather than as one `if` term.
        if (whenTrue.Lines.All(TotalRead) && whenFalse.Lines.All(TotalRead) &&
            whenTrue.Lines.Concat(whenFalse.Lines).Any(l => l.Text.Contains("B.op_Bang")))
        {
            _lines.AddRange(whenTrue.Lines);
            _lines.AddRange(whenFalse.Lines);
            whenTrue = whenTrue with { Lines = [] };
            whenFalse = whenFalse with { Lines = [] };
        }
        if (whenTrue.Lines.Length == 0 && whenFalse.Lines.Length == 0)
            return $"(if {cond} then {whenTrue.Term} else {whenFalse.Term})";

        // A bare value beside a branch of statements is let-bound: Pulse's join of the
        // two postconditions otherwise keeps only the bare branch's fact when the other
        // ends in a nested `if` (the conditional of a switch arm, for one).
        if (whenTrue.Lines.Length == 0) whenTrue = Bound(whenTrue.Term);
        if (whenFalse.Lines.Length == 0) whenFalse = Bound(whenFalse.Term);

        // R27.50. An arm that closes the receiver around a call reopens it at a fresh
        // record, and Pulse's join keeps that arm's facts about the record only under the
        // arm's condition. The other arm closes and reopens it too, so that on both sides
        // the record is one the invariant abstracts.
        var reopened = whenTrue.Reopened ?? whenFalse.Reopened;
        if (reopened is { } r0 && Pristine && r0.Self.PreModel is not null)
        {
            // Closed and reopened through the regions it holds, whichever way the call did.
            var r = r0.Self.Heaps.IsEmpty || r0.Heaps is not null ? r0
                : (r0.Self, (ImmutableArray<IrClassType>?)[.. r0.Self.Heaps.Select(h => h.Region)]);
            reopened = r;
            whenTrue = Reclosed(whenTrue, r);
            whenFalse = Reclosed(whenFalse, r);
        }
        else reopened = null;

        var t = Fresh();
        Line($"let {t} = if ({cond}) {{");
        _indent++;
        _lines.AddRange(whenTrue.Lines);
        Line(whenTrue.Term);
        _indent--;
        Line("} else {");
        _indent++;
        _lines.AddRange(whenFalse.Lines);
        Line(whenFalse.Term);
        _indent--;
        Line("};");
        if (reopened is { } ro)
        {
            Reopen(ro.Self, ro.Heaps);
            _lastReopen = ro;
        }
        return t;
    }
}

/// <summary>PAL's <c>$(…)</c> and <c>$&amp;(…)</c> antiquotations, reused verbatim.</summary>
public static class Antiquotation
{
    /// <param name="binder">
    /// Resolves <c>$&amp;(x)</c>: the Pulse name of the thing <c>x</c> lives in, rather
    /// than <c>$(x)</c>'s value of it. A ghost lemma about an array or a reference needs
    /// the array or the reference; the value is the wrong argument and, for a lemma that
    /// relates the two, an unusable one.
    /// </param>
    public static string Expand(string text, SpecScope scope, Func<string, string?>? binder = null)
    {
        var sb = new StringBuilder();
        for (var i = 0; i < text.Length; i++)
        {
            if (text[i] != '$' || i + 1 >= text.Length)
            {
                sb.Append(text[i]);
                continue;
            }

            var cell = text[i + 1] == '&' && i + 2 < text.Length && text[i + 2] == '(';
            if (!cell && text[i + 1] != '(')
            {
                sb.Append(text[i]);
                continue;
            }

            var depth = 0;
            var start = i + (cell ? 3 : 2);
            var j = start;
            for (; j < text.Length; j++)
            {
                if (text[j] == '(') depth++;
                else if (text[j] == ')' && depth-- == 0) break;
            }

            var name = text[start..j].Trim();
            sb.Append(cell
                ? binder?.Invoke(name) ?? name
                : scope.TryGet(name, out var term) ? term.Text : name);
            i = j;
        }
        return sb.ToString();
    }
}
