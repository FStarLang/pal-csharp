#!/usr/bin/env bash
# Negative tests: each case in cases/ must produce the diagnostic named in its
# `// EXPECT:` header, and no case may be translated silently.
#
# These are the counterpart of the verification tests. A verification test shows that a
# *supported* program reaches F* and is proved. A diagnostics test shows that an
# *unsupported* or ill-formed one stops at the C# level, with a message that names the
# mistake in the user's source rather than in generated Pulse.
set -u

cd "$(dirname "$0")"
PALCS="../../src/Pal.Tool/bin/Debug/net10.0/palcs"
[ -x "$PALCS" ] || PALCS="dotnet ../../src/Pal.Tool/bin/Debug/net10.0/palcs.dll"

fail=0
for case in cases/*.cs; do
    name=$(basename "$case" .cs)
    want=$(sed -n 's|^// EXPECT: *||p' "$case" | head -1)
    if [ -z "$want" ]; then
        echo "diagnostics: $name has no '// EXPECT:' header"; fail=1; continue
    fi

    got=$($PALCS -q -o "out/$name" "$case" 2>&1)
    status=$?

    # An .fst.config.json per case, not one for the directory: every case emits a
    # module named `TranslationErrors`, so a single config listing all the case
    # directories would make that name ambiguous. The F* IDE takes the config nearest
    # the file being edited, so one per output directory resolves it.
    if [ -d "out/$name" ]; then
        cat > "out/$name/$name.fst.config.json" <<JSON
{
  "fstar_exe": "../../../../tools/run-fstar.sh",
  "include_dirs": [
    ".",
    "../../../../pulse",
    "../../../../pulse/_cache"
  ],
  "options": [
    "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore"
  ]
}
JSON
    fi

    if ! grep -q "$want" <<<"$got"; then
        echo "diagnostics: $name: expected $want, got:"
        sed 's/^/    /' <<<"$got"
        fail=1
        continue
    fi

    # An error must also fail the run and poison TranslationErrors.fst, so that a broken
    # translation can never be mistaken for a passing proof.
    if [[ "$want" != PALCS09* ]]; then
        if [ "$status" -eq 0 ]; then
            echo "diagnostics: $name reported $want but exited 0"; fail=1
        fi
        if ! grep -q "assert False" "out/$name/TranslationErrors.fst" 2>/dev/null; then
            echo "diagnostics: $name did not poison TranslationErrors.fst"; fail=1
        fi
    fi

    # The diagnostic must carry a real span in the user's file, not <none>.
    if ! grep -q "\"file\": \".*$name\.cs\"" "out/$name/diagnostics.json" 2>/dev/null; then
        echo "diagnostics: $name has no source-located diagnostic in diagnostics.json"
        fail=1
    fi
done

if [ "$fail" -eq 0 ]; then
    echo "diagnostics: OK ($(ls cases/*.cs | wc -l | tr -d ' ') cases)"
fi
exit "$fail"
