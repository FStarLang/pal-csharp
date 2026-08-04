#!/usr/bin/env bash
# R2.2, the provenance lint — the second of §7.2's two mechanical detectors of emitter
# contortion (the first is the variant tests).
#
# Every top-level construct in every generated module must trace back to a span in the
# user's C#. A construct with no provenance was invented by the translator, and anything
# the translator invents has to be justified as a numbered rule in doc/translation.md
# rather than as a response to some particular example.
#
# The check is deliberately blunt: it reads the generated .fst and .fsti files, not the
# compiler's own account of what it did, so an emitter that forgot to record a construct
# fails just as loudly as one that invented it. Interfaces (R9.17) are scanned too, or a
# construct could escape the lint simply by being declared rather than defined.
set -u

cd "$(dirname "$0")"
fail=0
checked=0

for info in */out/source_range_info.json; do
    dir=$(dirname "$(dirname "$info")")

    # Constructs the emitter claims to have produced, and the modules it declares are
    # wholly user-written Pulse (`[assembly: IncludePulse]`).
    declared=$(python3 - "$info" <<'PY'
import json, sys
for e in json.load(open(sys.argv[1])):
    print(e["construct"])
PY
)
    verbatim=$(python3 - "$info" <<'PY'
import json, sys
for e in json.load(open(sys.argv[1])):
    if e["construct"] == "*":
        print(e["file"])
PY
)

    # Every recorded span must name a C# file that exists, with a real line number.
    if ! python3 - "$info" "$dir" <<'PY'
import json, os, sys
info, dir = sys.argv[1], sys.argv[2]
bad = []
for e in json.load(open(info)):
    src = e["source"]
    path = src["file"]
    if not os.path.isabs(path):
        path = os.path.join(dir, path)
    if not os.path.exists(path):
        bad.append(f'{e["construct"]}: no such source file {src["file"]}')
    elif src["range"]["start"]["line"] < 0:
        bad.append(f'{e["construct"]}: no source position')
for b in bad:
    print(b)
sys.exit(1 if bad else 0)
PY
    then
        echo "provenance-lint: $dir: unusable spans"
        fail=1
    fi

    for fst in "$dir"/out/*.fst "$dir"/out/*.fsti; do
        [ -e "$fst" ] || continue                                  # no interface in this test
        base=$(basename "$fst")
        [ "$base" = "TranslationErrors.fst" ] && continue          # the sentinel, by design
        grep -qxF "${base%i}" <<<"$verbatim" && continue           # the user's own Pulse

        # Top-level F*/Pulse definitions: `fn f`, `let f`, `let rec f`, `ghost fn f`,
        # a `val` an interface declares (R9.17), and the type declarations a struct
        # produces (R3.4).
        while read -r name; do
            [ -z "$name" ] && continue
            checked=$((checked + 1))
            if ! grep -qxF "$name" <<<"$declared"; then
                echo "provenance-lint: $dir/out/$base declares '$name', which no C# asked for"
                fail=1
            fi
        done < <(sed -nE \
            -e 's/^(ghost )?(fn|let|val)( rec)? ([A-Za-z_][A-Za-z0-9_'"'"']*).*/\4/p' \
            -e 's/^(noeq |unopteq )?type ([A-Za-z_][A-Za-z0-9_'"'"']*).*/\2/p' "$fst")
    done
done

if [ "$fail" -eq 0 ]; then
    echo "provenance-lint: OK ($checked construct(s))"
fi
exit "$fail"
