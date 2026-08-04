using System.Collections.Immutable;
using System.Text;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// §10. The whole module of a <em>recursive</em> class: one that holds a field of its own
/// nullable type. Everything here is a function of <see cref="IrClass.Recursion"/>, which
/// the frontend read off the user's <c>[Model]</c> member — no rule below consults the
/// class's name, its fields' names or anything else an example could supply.
///
/// <para>
/// The departure from R3.10 is one thing only: the invariant of such a class cannot be a
/// flat <c>exists*</c> over one record, because the record contains a reference to another
/// object of the same class, whose invariant would then have to appear inside its own
/// definition. It has to be an induction, and F36 fixes what the induction is on — the
/// <em>model</em>, not the reference, because only the model has a sub-term the recursion
/// can decrease on. That is exactly why R10.5 asks the user for the model as a function of
/// the fields: the equation they write is the equation this inverts.
/// </para>
/// </summary>
internal sealed class RecursiveEmitter(SpecEmitter spec, HierarchyEmitter hierarchy)
{
    private const string Perm = "p";
    private const string Model = "m";
    private const string Reference = "x";
    private const string Record = "r";
    private const string Value = "v";

    /// <summary>The model binder for the <em>i</em>th argument of the model constructor.</summary>
    /// <summary>
    /// R10.1. Inside the group being defined the class's own names are not yet a module,
    /// so the recursive field is written unqualified. Every other field renders as it
    /// always does.
    /// </summary>
    private static string FieldType(IrClass c, IrType t, string opt) =>
        t is IrClassType k && k.Name == c.Name
            ? (k.Nullable ? opt : Names.ClassType(c.Name))
            : Types.Render(t);

    private static string Sub(int i) => $"{Model}{i}";

    public string Emit(IrClass c)
    {
        var rec = c.Recursion!;
        var mod = Names.ClassModule(c.Name);
        var raw = Names.ClassRaw(c.Name);
        var self = Names.ClassType(c.Name);
        var opt = Names.ClassOpt(c.Name);
        var model = Names.ClassModel(c.Name);
        var invOpt = Names.ClassInvOpt(c.Name);

        var sb = new StringBuilder();
        sb.AppendLine($"module {mod}");
        sb.AppendLine("#lang-pulse");
        sb.AppendLine();
        sb.AppendLine(Preamble.Opens);
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();
        sb.AppendLine("module T = FStar.Tactics");
        sb.AppendLine();

        // R10.1/F35. The representation, the reference and the nullable reference are one
        // mutually recursive group. A `type … and …` may mix a record with a type
        // abbreviation, so R3.7's record and R3.8's box come out unchanged and nothing new
        // is needed to tie the knot.
        sb.Append("noeq type ").Append(raw).AppendLine(" = {");
        foreach (var f in c.Fields)
            sb.AppendLine($"  {Names.Field(f.Name)}: {FieldType(c, f.Type, opt)};");
        sb.AppendLine("}");
        sb.AppendLine($"and {self} = B.box {raw}");
        sb.AppendLine($"and {opt} = option {self}");
        sb.AppendLine();

        hierarchy.EmitModelType(sb, c);

        // R10.3. The invariant, by cases on the model. `[@@@mkey]` marks the reference as
        // the key Pulse matches resources on; without it a goal at one model is not found
        // in a context holding the predicate at another.
        sb.AppendLine($"let rec {invOpt} ([@@@mkey] {Reference}: {opt}) ({Perm}: perm) " +
                      $"({Model}: {model})");
        sb.AppendLine($"  : Tot slprop (decreases {Model})");
        sb.AppendLine($"  = match {Model} with");
        sb.AppendLine($"    | {NilPattern(rec)} -> pure ({Reference} == None)");
        sb.AppendLine($"    | {ConsPattern(rec)} ->");
        sb.AppendLine($"      exists* ({Value}: {self}) ({Record}: {raw}).");
        sb.AppendLine($"        pure ({Reference} == Some {Value}) **");
        sb.AppendLine($"        B.pts_to {Value} #{Perm} {Record} **");
        sb.AppendLine($"        pure ({Equations(c, rec)}) **");
        var conjuncts = rec.Args
            .Select((a, i) => (a, i))
            .Where(t => t.a is IrRecField)
            .Select(t => $"        {invOpt} {Record}.{Names.Field(((IrRecField)t.a).Field)} " +
                         $"{Perm} {Sub(t.i)}")
            .ToImmutableArray();
        sb.AppendLine(string.Join(" **\n", conjuncts));
        sb.AppendLine();

        // R10.3a. The non-null invariant every §3/§4 rule already talks about is derived,
        // not primitive: a `C` is a `C?` that happens to be `Some`. So R4.10's model
        // binders, R4.5's contracts and R3.10b's nested objects need no new case — a
        // recursive class is an ordinary class whose invariant happens to be a recursion.
        sb.AppendLine($"let {Names.ClassInv(c.Name)} (this: {self}) " +
                      $"(#[T.exact (`1.0R)] {Perm}: perm) ({Model}: {model}) : slprop =");
        sb.AppendLine($"  {invOpt} (Some this) {Perm} {Model}");
        sb.AppendLine();

        EmitLemmas(sb, c, rec);
        EmitShareAndGather(sb, c, rec);

        sb.AppendLine();
        hierarchy.EmitObservations(sb, c);
        return sb.ToString();
    }

    // -----------------------------------------------------------------------
    // The model's two constructors, as patterns.
    // -----------------------------------------------------------------------

    /// <summary>R10.5. What a <em>null</em> reference denotes: the empty constructor.</summary>
    private static string NilPattern(IrRecursion rec) =>
        rec.Shape is RecursiveShape.List ? "[]" : "CTree.Leaf";

    /// <summary>The empty constructor as a term (the same thing, outside a pattern).</summary>
    private static string NilTerm(IrRecursion rec) => NilPattern(rec);

    /// <summary>The non-empty constructor with one binder per argument.</summary>
    private static string ConsPattern(IrRecursion rec)
    {
        var binders = rec.Args.Select((_, i) => Sub(i)).ToImmutableArray();
        return rec.Shape is RecursiveShape.List
            ? $"{binders[0]} :: {binders[1]}"
            : $"CTree.Branch {string.Join(" ", binders)}";
    }

    /// <summary>
    /// The non-empty constructor applied to the values the <em>representation</em> gives:
    /// each pure argument is the field expression the user's <c>[Model]</c> wrote, and each
    /// recursive argument is a sub-model binder. This is what <c>elim_cons</c> reports the
    /// model to be and what <c>intro_cons</c> establishes it to be.
    /// </summary>
    private string ConsTerm(IrClass c, IrRecursion rec, Func<int, string> subModel)
    {
        var parts = rec.Args.Select((a, i) => a is IrRecField ? subModel(i) : Pure(c, (IrRecPure)a))
            .ToImmutableArray();
        return rec.Shape is RecursiveShape.List
            ? $"{parts[0]} :: {parts[1]}"
            : $"CTree.Branch {string.Join(" ", parts)}";
    }

    /// <summary>
    /// R10.5. A pure argument of the model constructor, read off the representation. This
    /// is R3.9's abstraction function restricted to one argument, and it is emitted by the
    /// same <see cref="SpecEmitter"/> with the same scope, so a field means in a recursive
    /// class exactly what it means in any other.
    /// </summary>
    private string Pure(IrClass c, IrRecPure arg)
    {
        var scope = RepresentationScope(c);
        return arg.Value.Type is IrPrim { IsMachineInt: true } or IrPrim { Kind: PrimKind.SpecInt }
                                or IrPrim { Kind: PrimKind.SpecNat }
            ? spec.Math(arg.Value, scope)
            : spec.Emit(arg.Value, scope).Text;
    }

    private static SpecScope RepresentationScope(IrClass c)
    {
        var scope = new SpecScope { DefiningClass = c.Name };
        foreach (var f in c.Fields)
            scope.Bind(f.Name, new Term($"{Record}.{Names.Field(f.Name)}", MethodPlan.KindOf(f.Type), f.Type));
        return scope;
    }

    /// <summary>
    /// The pure half of the cons case: each pure constructor argument equated with the
    /// field expression that produces it, and then the class's own <c>[Invariant]</c>
    /// clauses, which mean here exactly what R3.9b makes them mean everywhere else.
    /// </summary>
    private string Equations(IrClass c, IrRecursion rec)
    {
        var scope = RepresentationScope(c);
        var parts = new List<string>();
        for (var i = 0; i < rec.Args.Length; i++)
            if (rec.Args[i] is IrRecPure pure)
                parts.Add($"{Sub(i)} == {Pure(c, pure)}");
        parts.AddRange(c.Invariants.Select(inv => spec.AsProp(spec.Emit(inv, scope))));
        return SpecEmitter.Conjunction(parts);
    }

    // -----------------------------------------------------------------------
    // R10.4. The six derived case lemmas.
    // -----------------------------------------------------------------------

    /// <summary>
    /// R10.4. Six ghost lemmas per recursive class, derived from the definition and emitted
    /// beside it. They are what a <em>client</em> uses; no client ever unfolds the predicate.
    /// <para>
    /// This is the point of departure from PAL for C, where a recursive predicate is written
    /// by hand inside <c>_include_pulse</c>, each of these lemmas is written by hand in
    /// Pulse, and each is invoked by hand with <c>_ghost_stmt</c>. Here the predicate is read
    /// off the C# <c>[Model]</c> member, all six lemmas are generated, and R10.7 places them
    /// at the null test the C# already had to write — so the user writes no Pulse at all.
    /// </para>
    /// </summary>
    private void EmitLemmas(StringBuilder sb, IrClass c, IrRecursion rec)
    {
        var opt = Names.ClassOpt(c.Name);
        var raw = Names.ClassRaw(c.Name);
        var model = Names.ClassModel(c.Name);
        var inv = Names.ClassInvOpt(c.Name);
        var nil = NilTerm(rec);
        var cons = ConsPattern(rec);
        var recursive = rec.Args.Select((a, i) => (a, i)).Where(t => t.a is IrRecField).ToImmutableArray();

        // Unfolding at the cons case leaves two existentials; naming both is required,
        // because binding only one leaves the other a uvar and the assertion cannot be
        // checked (F36a).
        var witness = $"    with {Value} {Record}. assert (B.pts_to {Value} #{Perm} {Record});";

        // -- the shape equivalence -------------------------------------------
        // R10.4a. What a client needs *before* it has tested anything: the shape of the
        // model and the nullity of the reference determine each other. This is what lets a
        // C# `if (n == null)` be a proof step at all — in the `else` branch it is what
        // tells the prover the model is non-empty, and hence that `elim_cons` applies.
        sb.AppendLine($"ghost fn {Names.ClassCases(c.Name)} ({Reference}: {opt}) " +
                      $"(#{Perm}: perm) (#{Model}: {model})");
        sb.AppendLine($"  preserves {inv} {Reference} {Perm} {Model}");
        sb.AppendLine($"  ensures pure (Some? {Reference} <==> {ConsTest(rec)} {Model})");
        sb.AppendLine("{");
        sb.AppendLine($"  match {Model} {{");
        sb.AppendLine($"    {NilPattern(rec)} -> {{");
        sb.AppendLine($"      unfold ({inv} {Reference} {Perm} {nil});");
        sb.AppendLine($"      fold ({inv} {Reference} {Perm} {nil});");
        sb.AppendLine("    }");
        sb.AppendLine($"    {cons} -> {{");
        sb.AppendLine($"      unfold ({inv} {Reference} {Perm} ({cons}));");
        sb.AppendLine($"  {witness}");
        sb.AppendLine($"      fold ({inv} {Reference} {Perm} ({cons}));");
        sb.AppendLine("    }");
        sb.AppendLine("  }");
        sb.AppendLine("}");
        sb.AppendLine();

        // -- the null case, preserving ---------------------------------------
        sb.AppendLine($"ghost fn {Names.ClassNilCase(c.Name)} ({Reference}: {opt}) " +
                      $"(#{Perm}: perm) (#{Model}: {model})");
        sb.AppendLine($"  preserves {inv} {Reference} {Perm} {Model}");
        sb.AppendLine($"  requires pure ({Reference} == None)");
        sb.AppendLine($"  ensures pure ({Model} == {nil})");
        sb.AppendLine("{");
        sb.AppendLine($"  match {Model} {{");
        sb.AppendLine($"    {NilPattern(rec)} -> {{ () }}");
        sb.AppendLine($"    {cons} -> {{");
        sb.AppendLine($"      unfold ({inv} {Reference} {Perm} ({cons}));");
        sb.AppendLine($"  {witness}");
        sb.AppendLine("      unreachable ()");
        sb.AppendLine("    }");
        sb.AppendLine("  }");
        sb.AppendLine("}");
        sb.AppendLine();

        // -- the null case, consuming ----------------------------------------
        // R10.4b. `nil_case` preserves the invariant, which is what a method whose
        // postcondition still owes it needs; a method that *consumes* its argument
        // (`[Consumes]`, R4.9c) has to give it up instead, and leaving it behind is a
        // leftover resource. Which one R10.7 emits is read off the contract, exactly as
        // R4.10 already reads it.
        sb.AppendLine($"ghost fn {Names.ClassElimNil(c.Name)} ({Reference}: {opt}) " +
                      $"(#{Perm}: perm) (#{Model}: {model})");
        sb.AppendLine($"  requires {inv} {Reference} {Perm} {Model} ** pure ({Reference} == None)");
        sb.AppendLine($"  ensures pure ({Model} == {nil})");
        sb.AppendLine("{");
        sb.AppendLine($"  {Names.ClassNilCase(c.Name)} {Reference};");
        sb.AppendLine($"  unfold ({inv} {Reference} {Perm} {nil});");
        sb.AppendLine("}");
        sb.AppendLine();

        // -- the empty invariant, out of nothing -----------------------------
        // The empty model owns nothing, which is what makes `C? x = null;` free.
        sb.AppendLine($"ghost fn {Names.ClassIntroNil(c.Name)} ({Reference}: {opt}) ({Perm}: perm)");
        sb.AppendLine($"  requires pure ({Reference} == None)");
        sb.AppendLine($"  ensures {inv} {Reference} {Perm} {nil}");
        sb.AppendLine("{");
        sb.AppendLine($"  fold ({inv} {Reference} {Perm} {nil})");
        sb.AppendLine("}");
        sb.AppendLine();

        // -- opening a non-null reference ------------------------------------
        // F36b. Stated over a *refined* binder, not over a bare `class_C` and not over a
        // plain option with `requires pure (Some? x)`: the latter is ill-typed, because the
        // `pure` in `requires` is not in scope when the `ensures` is typed, and the former
        // makes the client's goal `inv_opt (Some var_n)` where it holds `inv_opt var_n`.
        var elimResults = string.Join(" ", recursive.Select(t => Sub(t.i)));
        // Every sub-model is its own implicit: `(#m0 m2: t)` would make the second one
        // explicit, and a class with two recursive fields would be partially applied.
        var elimImplicits = string.Join(" ", recursive.Select(t => "#" + Sub(t.i)));
        sb.AppendLine($"ghost fn {Names.ClassElimCons(c.Name)} ({Reference}: {opt} {{ Some? {Reference} }}) " +
                      $"(#{Perm}: perm) (#{Model}: {model})");
        sb.AppendLine($"  requires {inv} {Reference} {Perm} {Model}");
        sb.AppendLine($"  ensures exists* ({Record}: {raw}) ({elimResults}: {model}).");
        sb.AppendLine($"    B.pts_to (Some?.v {Reference}) #{Perm} {Record} **");
        foreach (var (a, i) in recursive)
            sb.AppendLine($"    {inv} {Record}.{Names.Field(((IrRecField)a).Field)} {Perm} {Sub(i)} **");
        sb.AppendLine($"    pure ({Model} == {ConsTerm(c, rec, Sub)})");
        sb.AppendLine("{");
        sb.AppendLine($"  match {Model} {{");
        sb.AppendLine($"    {NilPattern(rec)} -> {{");
        sb.AppendLine($"      unfold ({inv} {Reference} {Perm} {nil});");
        sb.AppendLine("      unreachable ()");
        sb.AppendLine("    }");
        sb.AppendLine($"    {cons} -> {{");
        sb.AppendLine($"      unfold ({inv} {Reference} {Perm} ({cons}));");
        sb.AppendLine($"  {witness}");
        sb.AppendLine($"      rewrite each {Value} as (Some?.v {Reference});");
        sb.AppendLine("      ()");
        sb.AppendLine("    }");
        sb.AppendLine("  }");
        sb.AppendLine("}");
        sb.AppendLine();

        // -- closing it again ------------------------------------------------
        var some = $"(Some (Some?.v {Reference}))";
        var built = ConsTerm(c, rec, Sub);
        sb.AppendLine($"ghost fn {Names.ClassIntroCons(c.Name)} ({Reference}: {opt} {{ Some? {Reference} }})");
        sb.AppendLine($"    (#{Perm}: perm) (#{Record}: {raw}) ({elimImplicits}: {model})");
        sb.Append($"  requires B.pts_to (Some?.v {Reference}) #{Perm} {Record}");
        foreach (var (a, i) in recursive)
            sb.Append($" **\n           {inv} {Record}.{Names.Field(((IrRecField)a).Field)} {Perm} {Sub(i)}");
        sb.AppendLine();
        sb.AppendLine($"  ensures {inv} {Reference} {Perm} ({built})");
        sb.AppendLine("{");
        sb.AppendLine($"  fold ({inv} {some} {Perm} ({built}));");
        sb.AppendLine($"  rewrite ({inv} {some} {Perm} ({built}))");
        sb.AppendLine($"       as ({inv} {Reference} {Perm} ({built}));");
        sb.AppendLine("}");
        sb.AppendLine();

        // R10.4c. The same step at the *non-null* invariant, which is what R3.10b's `fold`
        // becomes for a recursive class: a constructor hands back a `C`, not a `C?`, and
        // R10.3a's two forms are related by a rewrite rather than by matching. Deriving it
        // here rather than at each allocation is what keeps R6.8's rule one line long.
        var invNn0 = Names.ClassInv(c.Name);
        var self0 = Names.ClassType(c.Name);
        sb.AppendLine($"ghost fn {Names.ClassIntro(c.Name)} (this: {self0})");
        sb.AppendLine($"    (#{Perm}: perm) (#{Record}: {raw}) ({elimImplicits}: {model})");
        sb.Append($"  requires B.pts_to this #{Perm} {Record}");
        foreach (var (a, i) in recursive)
            sb.Append($" **\n           {inv} {Record}.{Names.Field(((IrRecField)a).Field)} {Perm} {Sub(i)}");
        sb.AppendLine();
        sb.AppendLine($"  ensures {invNn0} this #{Perm} ({built})");
        sb.AppendLine("{");
        sb.AppendLine($"  rewrite (B.pts_to this #{Perm} {Record}) as (B.pts_to (Some?.v (Some this)) #{Perm} {Record});");
        sb.AppendLine($"  {Names.ClassIntroCons(c.Name)} (Some this);");
        sb.AppendLine($"  rewrite ({inv} (Some this) {Perm} ({built}))");
        sb.AppendLine($"       as ({invNn0} this #{Perm} ({built}));");
        sb.AppendLine("}");
        sb.AppendLine();

        // R10.2b. The injection. A `C` used where a `C?` is expected is the identity in
        // C#, so it must be free here too: the two forms are related by R10.3a's
        // definition and the whole lemma is the rewrite that says so.
        sb.AppendLine($"ghost fn {Names.ClassAsOpt(c.Name)} (this: {self0}) " +
                      $"(#{Perm}: perm) (#{Model}: {model})");
        sb.AppendLine($"  requires {invNn0} this #{Perm} {Model}");
        sb.AppendLine($"  ensures {inv} (Some this) {Perm} {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  rewrite ({invNn0} this #{Perm} {Model}) as ({inv} (Some this) {Perm} {Model});");
        sb.AppendLine("}");
        sb.AppendLine();
    }

    /// <summary>The discriminator of the non-empty constructor.</summary>
    private static string ConsTest(IrRecursion rec) =>
        rec.Shape is RecursiveShape.List ? "Cons?" : "CTree.Branch?";

    // -----------------------------------------------------------------------
    // R10.8. Sharing.
    // -----------------------------------------------------------------------

    /// <summary>
    /// R3.10d emits <c>share</c>/<c>gather</c> for every class, so that <c>[Frac]</c> and
    /// read-only aliasing work. For a recursive class the two are themselves recursive
    /// ghost functions (F40, F41) — the template is R3.10d's, with <c>rec</c>, a
    /// <c>decreases</c>, and the case lemmas in place of the flat <c>unfold</c>/<c>fold</c>.
    /// </summary>
    private void EmitShareAndGather(StringBuilder sb, IrClass c, IrRecursion rec)
    {
        var opt = Names.ClassOpt(c.Name);
        var model = Names.ClassModel(c.Name);
        var inv = Names.ClassInvOpt(c.Name);
        var half = "(p /. 2.0R)";
        var recursive = rec.Args.Select((a, i) => (Field: (a as IrRecField)?.Field, Index: i))
            .Where(t => t.Field is not null).ToImmutableArray();
        var subs = string.Join(" ", recursive.Select(t => Sub(t.Index)));
        var altSubs = string.Join(" ", recursive.Select(t => Names.Alt(Sub(t.Index))));

        sb.AppendLine($"ghost fn rec {Names.ClassInvOptShare(c.Name)} ({Reference}: {opt}) " +
                      $"(#{Perm}: perm) (#{Model}: {model})");
        sb.AppendLine($"  requires {inv} {Reference} {Perm} {Model}");
        sb.AppendLine($"  ensures {inv} {Reference} {half} {Model} ** {inv} {Reference} {half} {Model}");
        sb.AppendLine($"  decreases {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  {Names.ClassCases(c.Name)} {Reference};");
        sb.AppendLine($"  if (None? {Reference}) {{");
        sb.AppendLine($"    {Names.ClassElimNil(c.Name)} {Reference};");
        sb.AppendLine($"    {Names.ClassIntroNil(c.Name)} {Reference} {half};");
        sb.AppendLine($"    {Names.ClassIntroNil(c.Name)} {Reference} {half};");
        sb.AppendLine("  } else {");
        sb.AppendLine($"    {Names.ClassElimCons(c.Name)} {Reference};");
        sb.AppendLine($"    with {Record} {subs}. assert (" +
                      $"B.pts_to (Some?.v {Reference}) #{Perm} {Record}" +
                      string.Concat(recursive.Select(t =>
                          $" ** {inv} {Record}.{Names.Field(t.Field!)} {Perm} {Sub(t.Index)}")) + ");");
        sb.AppendLine($"    B.share (Some?.v {Reference});");
        foreach (var t in recursive)
            sb.AppendLine($"    {Names.ClassInvOptShare(c.Name)} {Record}.{Names.Field(t.Field!)} " +
                          $"#{Perm} #{Sub(t.Index)};");
        var introArgs = string.Concat(recursive.Select(t => $" #{Sub(t.Index)}"));
        sb.AppendLine($"    {Names.ClassIntroCons(c.Name)} {Reference} #{half} #{Record}{introArgs};");
        sb.AppendLine($"    {Names.ClassIntroCons(c.Name)} {Reference} #{half} #{Record}{introArgs};");
        sb.AppendLine("  }");
        sb.AppendLine("}");
        sb.AppendLine();

        // F41: two copies of the same predicate at different models, which is exactly the
        // ambiguity R3.10d already documents.
        sb.AppendLine("[@@allow_ambiguous]");
        sb.AppendLine($"ghost fn rec {Names.ClassInvOptGather(c.Name)} ({Reference}: {opt}) (p q: perm)");
        sb.AppendLine($"    (#{Model} #{Names.Alt(Model)}: {model})");
        sb.AppendLine($"  requires {inv} {Reference} p {Model} ** {inv} {Reference} q {Names.Alt(Model)}");
        sb.AppendLine($"  ensures {inv} {Reference} (p +. q) {Model} ** " +
                      $"pure ({Model} == {Names.Alt(Model)})");
        sb.AppendLine($"  decreases {Model}");
        sb.AppendLine("{");
        sb.AppendLine($"  {Names.ClassCases(c.Name)} {Reference} #p #{Model};");
        sb.AppendLine($"  {Names.ClassCases(c.Name)} {Reference} #q #{Names.Alt(Model)};");
        sb.AppendLine($"  if (None? {Reference}) {{");
        sb.AppendLine($"    {Names.ClassElimNil(c.Name)} {Reference} #p #{Model};");
        sb.AppendLine($"    {Names.ClassElimNil(c.Name)} {Reference} #q #{Names.Alt(Model)};");
        sb.AppendLine($"    {Names.ClassIntroNil(c.Name)} {Reference} (p +. q);");
        sb.AppendLine("  } else {");
        sb.AppendLine($"    {Names.ClassElimCons(c.Name)} {Reference} #p #{Model};");
        sb.AppendLine($"    with {Record} {subs}. assert (" +
                      $"B.pts_to (Some?.v {Reference}) #p {Record}" +
                      string.Concat(recursive.Select(t =>
                          $" ** {inv} {Record}.{Names.Field(t.Field!)} p {Sub(t.Index)}")) + ");");
        sb.AppendLine($"    {Names.ClassElimCons(c.Name)} {Reference} #q #{Names.Alt(Model)};");
        sb.AppendLine($"    with {Names.Alt(Record)} {altSubs}. assert (" +
                      $"B.pts_to (Some?.v {Reference}) #q {Names.Alt(Record)}" +
                      string.Concat(recursive.Select(t =>
                          $" ** {inv} {Names.Alt(Record)}.{Names.Field(t.Field!)} q " +
                          $"{Names.Alt(Sub(t.Index))}")) + ");");
        sb.AppendLine($"    B.gather (Some?.v {Reference});");
        // After `gather` the context holds one box at the joined permission, under whichever
        // of the two record names the prover matched first. Renaming the other onto it is
        // what leaves exactly one candidate for every existential below.
        sb.AppendLine($"    rewrite each {Names.Alt(Record)} as {Record};");
        foreach (var t in recursive)
            sb.AppendLine($"    {Names.ClassInvOptGather(c.Name)} {Record}.{Names.Field(t.Field!)} p q " +
                          $"#{Sub(t.Index)} #{Names.Alt(Sub(t.Index))};");
        sb.AppendLine($"    {Names.ClassIntroCons(c.Name)} {Reference} #(p +. q) #{Record}{introArgs};");
        sb.AppendLine("  }");
        sb.AppendLine("}");
        sb.AppendLine();

        // R3.10d's two derived forms, at the non-null invariant, so that a client of a
        // recursive class shares it exactly as it shares any other object.
        var invOpt = Names.ClassInvOpt(c.Name);
        var invNn = Names.ClassInv(c.Name);
        var self = Names.ClassType(c.Name);
        sb.AppendLine($"ghost fn {Names.ClassInvShare(c.Name)} (this: {self}) " +
                      $"(#{Perm}: perm) (#{Model}: {model})");
        sb.AppendLine($"  requires {invNn} this #{Perm} {Model}");
        sb.AppendLine($"  ensures {invNn} this #{half} {Model} ** {invNn} this #{half} {Model}");
        sb.AppendLine("{");
        // R10.3a. `__inv` is a definition, but Pulse matches resources syntactically, so
        // the two forms are related by an explicit rewrite rather than by unfolding. F*
        // discharges each of these by delta.
        sb.AppendLine($"  rewrite ({invNn} this #{Perm} {Model}) " +
                      $"as ({invOpt} (Some this) {Perm} {Model});");
        sb.AppendLine($"  {Names.ClassInvOptShare(c.Name)} (Some this);");
        sb.AppendLine($"  rewrite ({invOpt} (Some this) {half} {Model}) " +
                      $"as ({invNn} this #{half} {Model});");
        sb.AppendLine($"  rewrite ({invOpt} (Some this) {half} {Model}) " +
                      $"as ({invNn} this #{half} {Model});");
        sb.AppendLine("}");
        sb.AppendLine();

        sb.AppendLine("[@@allow_ambiguous]");
        sb.AppendLine($"ghost fn {Names.ClassInvGatherGen(c.Name)} (this: {self}) (p q: perm) " +
                      $"(#{Model} #{Names.Alt(Model)}: {model})");
        sb.AppendLine($"  requires {invNn} this #p {Model} ** {invNn} this #q {Names.Alt(Model)}");
        sb.AppendLine($"  ensures {invNn} this #(p +. q) {Model} ** " +
                      $"pure ({Model} == {Names.Alt(Model)})");
        sb.AppendLine("{");
        sb.AppendLine($"  rewrite ({invNn} this #p {Model}) as ({invOpt} (Some this) p {Model});");
        sb.AppendLine($"  rewrite ({invNn} this #q {Names.Alt(Model)}) " +
                      $"as ({invOpt} (Some this) q {Names.Alt(Model)});");
        sb.AppendLine($"  {Names.ClassInvOptGather(c.Name)} (Some this) p q;");
        sb.AppendLine($"  rewrite ({invOpt} (Some this) (p +. q) {Model}) " +
                      $"as ({invNn} this #(p +. q) {Model});");
        sb.AppendLine("}");
        sb.AppendLine();

        sb.AppendLine("[@@allow_ambiguous]");
        sb.AppendLine($"ghost fn {Names.ClassInvGather(c.Name)} (this: {self}) " +
                      $"(#{Perm}: perm) (#{Model} #{Names.Alt(Model)}: {model})");
        sb.AppendLine($"  requires {invNn} this #{half} {Model} ** {invNn} this #{half} {Names.Alt(Model)}");
        sb.AppendLine($"  ensures {invNn} this #{Perm} {Model} ** pure ({Model} == {Names.Alt(Model)})");
        sb.AppendLine("{");
        sb.AppendLine($"  {Names.ClassInvGatherGen(c.Name)} this {half} {half};");
        sb.AppendLine($"  rewrite ({invNn} this #(p /. 2.0R +. p /. 2.0R) {Model}) " +
                      $"as ({invNn} this #{Perm} {Model});");
        sb.AppendLine("}");
    }
}
