#!/usr/bin/env bash
# The analyzer must say, in the editor, exactly what `palcs` says at the command line.
#
# That is not a property this script can check by comparing two hand-written lists,
# because a hand-written list is the thing that drifts. It checks it the only way that
# stays true: it takes the *same* negative cases `test/diagnostics` uses, builds each one
# with the stock C# compiler and the analyzer loaded, and requires the build to report the
# id in the case's own `// EXPECT:` header. The cases are shared, so a case added there is
# covered here, and an id that stops being reported fails in both places at once.
#
# It also checks the two things only a real build can show:
#
#   * that a *good* program produces no pal-csharp diagnostic at all, so the analyzer
#     cannot become a source of noise in a project that is inside the language; and
#   * that C# itself still compiles the annotated source. Every case here is built, not
#     just analysed, which is the core invariant of the whole project — annotated C# is
#     C# — asserted against the compiler rather than against a document.
set -u

cd "$(dirname "$0")"
ROOT=$(cd ../.. && pwd)
ANALYZERS="$ROOT/src/Pal.Analyzers/bin/Debug/netstandard2.0"
ANNOTATIONS="$ROOT/src/Pal.Annotations/bin/Debug/net10.0/Pal.Annotations.dll"

if [ ! -f "$ANALYZERS/Pal.Analyzers.dll" ]; then
    echo "analyzer: $ANALYZERS/Pal.Analyzers.dll is missing (build the solution first)"
    exit 1
fi

fail=0
mkdir -p out

# A subset, not all of them: each case costs a full MSBuild, and what is under test here
# is the analyzer's plumbing rather than the rules, which `test/diagnostics` already
# covers case by case. They are chosen to come from different places — the frontend's type
# map, the checker's whole-program pass, the spec binder's rewriting of a C# binding error,
# a warning rather than an error, and the emitter — so that a break in the reporting path
# shows up wherever it is. The last of those is the one that is easy to lose: the analyzer
# has to run the emitter to see it, and an analyzer that stopped at the checker would still
# pass every other case here while quietly under-reporting.
CASES="StructOwnsArray ClassWithoutModel PrivateSpecMember AssumeIsUnsound ArrayInMeasure"
GOOD="$ROOT/test/counter_class/Counter.cs"

# ...and "different places" is checked, not asserted. Every directory of the compiler that
# raises an id must be represented, so a pass added later — or one the analyzer stops
# running — cannot go unnoticed here.
for pass_dir in "$ROOT"/src/Pal.Compiler/*/; do
    [ "$(basename "$pass_dir")" = "Diagnostics" ] && continue   # the catalog, not a pass
    ids=$(grep -rhoE '"PALCS[0-9]+"' "$pass_dir" 2>/dev/null | tr -d '"' | sort -u)
    [ -z "$ids" ] && continue
    covered=0
    for name in $CASES; do
        want=$(sed -n 's|^// EXPECT: *||p' "$ROOT/test/diagnostics/cases/$name.cs" 2>/dev/null | head -1)
        printf '%s\n' "$ids" | grep -qx "$want" && covered=1
    done
    if [ "$covered" = 0 ]; then
        echo "analyzer: no case covers src/Pal.Compiler/$(basename "$pass_dir")/"
        fail=1
    fi
done

build_and_report() {
    local dir=$1 source=$2
    rm -rf "$dir"
    mkdir -p "$dir"
    cp "$source" "$dir/Case.cs"
    sed -e "s|@ANALYZERS@|$ANALYZERS|g" -e "s|@ANNOTATIONS@|$ANNOTATIONS|g" \
        Probe.csproj.in > "$dir/Probe.csproj"
    (cd "$dir" && dotnet build --nologo -v quiet 2>&1)
}

for name in $CASES; do
    case_file="$ROOT/test/diagnostics/cases/$name.cs"
    if [ ! -f "$case_file" ]; then
        echo "analyzer: no such case $name"; fail=1; continue
    fi

    want=$(sed -n 's|^// EXPECT: *||p' "$case_file" | head -1)
    got=$(build_and_report "out/$name" "$case_file")

    if ! printf '%s' "$got" | grep -q "$want"; then
        echo "analyzer: $name did not report $want"
        printf '%s\n' "$got" | sed 's/^/  /' | head -20
        fail=1
        continue
    fi

    # The message has to arrive too, not just the id: a diagnostic that reaches the editor
    # as a bare code is a worse experience than the command line, not an equal one.
    if ! printf '%s' "$got" | grep -qE "$want: .+"; then
        echo "analyzer: $name reported $want with no message"
        fail=1
    fi
done

# What Pulse said arrives rather than being computed: `palcs report` writes it and the
# analyzer reads it back through `AdditionalFiles`. That path has no other test — the
# reporter's own mapping is checked in test/pulse_refusals, but whether the result reaches
# an editor is a question about MSBuild items and Roslyn's options, which only a build can
# answer.
verification="out/Verification"
rm -rf "$verification"
mkdir -p "$verification/out"
cp "$GOOD" "$verification/Case.cs"
sed -e "s|@ANALYZERS@|$ANALYZERS|g" -e "s|@ANNOTATIONS@|$ANNOTATIONS|g" \
    Probe.csproj.in > "$verification/Probe.csproj"
python3 - "$verification/Probe.csproj" <<'PATCH'
import io, sys
path = sys.argv[1]
text = io.open(path).read()
io.open(path, "w").write(text.replace(
    "</Project>",
    "  <ItemGroup>\n    <AdditionalFiles Include=\"out/verification.txt\" />\n  </ItemGroup>\n</Project>"))
PATCH
printf '%s\n' \
    "# fixture" \
    "PALCS0600	Case.cs	1	1	1	6	Error	could not prove the invariant" \
    > "$verification/out/verification.txt"

got=$(cd "$verification" && dotnet build --nologo -v quiet 2>&1)
if ! printf '%s' "$got" | grep -q "PALCS0600: could not prove the invariant"; then
    echo "analyzer: a verification result did not reach the editor"
    printf '%s\n' "$got" | sed 's/^/  /' | head -20
    fail=1
fi

# A program that is inside the language must build clean, with no pal-csharp diagnostic of
# any severity. This is the half of the contract that a negative test cannot state.
got=$(build_and_report out/Good "$GOOD")
if printf '%s' "$got" | grep -qE "PALCS[0-9]{4}"; then
    echo "analyzer: a valid program produced a pal-csharp diagnostic"
    printf '%s\n' "$got" | grep -E "PALCS[0-9]{4}" | sed 's/^/  /'
    fail=1
fi
if ! printf '%s' "$got" | grep -q "Build succeeded"; then
    echo "analyzer: a valid program failed to build"
    printf '%s\n' "$got" | sed 's/^/  /' | head -20
    fail=1
fi

if [ "$fail" = 0 ]; then
    echo "analyzer: OK ($(echo $CASES | wc -w) case(s) + verification + 1 clean build)"
fi
exit $fail
