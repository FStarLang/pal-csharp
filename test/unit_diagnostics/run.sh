#!/usr/bin/env bash
# Negative tests for verification units (doc/translation.md §36): each case in cases/ is
# translated with `--reference` to the units its `// REFERENCES:` header names (each a
# directory under units/, translated first), and must be refused with the diagnostic its
# `// EXPECT:` header names. A unit that is referenced is also translated on its own, so
# every case starts from units that are accepted.
set -u

cd "$(dirname "$0")"
PALCS="../../src/Pal.Tool/bin/Debug/net10.0/palcs"
[ -x "$PALCS" ] || PALCS="dotnet ../../src/Pal.Tool/bin/Debug/net10.0/palcs.dll"

fail=0
for unit in units/*/; do
    name=$(basename "$unit")
    if ! got=$($PALCS -q -o "out/units/$name" "$unit"*.cs 2>&1); then
        echo "unit_diagnostics: unit $name does not translate:"
        sed 's/^/    /' <<<"$got"
        fail=1
    fi
done

for case in cases/*.cs; do
    name=$(basename "$case" .cs)
    want=$(sed -n 's|^// EXPECT: *||p' "$case" | head -1)
    refs=$(sed -n 's|^// REFERENCES: *||p' "$case" | head -1)
    if [ -z "$want" ]; then
        echo "unit_diagnostics: $name has no '// EXPECT:' header"; fail=1; continue
    fi
    args=()
    for r in $refs; do args+=(--reference "out/units/$r"); done

    got=$($PALCS -q -o "out/$name" "${args[@]}" "$case" 2>&1)
    status=$?
    if ! grep -q "$want" <<<"$got"; then
        echo "unit_diagnostics: $name: expected $want, got:"
        sed 's/^/    /' <<<"$got"
        fail=1
    elif [ "$status" -eq 0 ]; then
        echo "unit_diagnostics: $name reported $want but exited 0"; fail=1
    fi
done

if [ "$fail" -eq 0 ]; then
    echo "unit_diagnostics: OK ($(ls cases/*.cs | wc -l | tr -d ' ') cases)"
fi
exit "$fail"
