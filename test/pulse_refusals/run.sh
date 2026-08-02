#!/usr/bin/env bash
# Programs pal-csharp translates faithfully and Pulse then refuses.
#
# These are the cases the frontend deliberately does *not* rule on. A rule about what a
# separation logic can prove belongs in the separation logic: the frontend cannot see the
# prover's context, so any answer it gives is an approximation, and an approximation in the
# frontend is worse than a precise answer in the verifier because it is the frontend that
# has to be trusted. §0 rule 3 says the emitter never invents a proof step; this is the
# same rule pointed the other way — the *checker* never invents a refusal.
#
# So the refusal has to be tested where it happens. Each case carries an `EXPECT-PULSE:`
# header naming the resource or property F* must report as unprovable. The case is
# translated with no diagnostics at all — that is half the point, the translation is
# faithful — and then F* must fail, and must fail for the stated reason rather than for
# some other reason that happens to also be a failure.
#
# Landing on the right C# line is the other half, and it is checked here too. F* reports
# against a `.fst` nobody wrote; `palcs report` reads the emitter's line map and says it
# again against the source. A `MARKER` comment in each case marks the line the message
# must arrive at, so the assertion moves when the file is edited and cannot quietly
# describe the wrong statement.
set -u

cd "$(dirname "$0")"
ROOT=$(cd ../.. && pwd)
PALCS="$ROOT/src/Pal.Tool/bin/Debug/net10.0/palcs"
FSTAR="$ROOT/tools/run-fstar.sh"

fail=0
count=0
mkdir -p out

for case_file in cases/*.cs; do
    name=$(basename "$case_file" .cs)
    want=$(sed -n 's|^// EXPECT-PULSE: *||p' "$case_file" | head -1)
    count=$((count + 1))

    if [ -z "$want" ]; then
        echo "pulse-refusals: $name has no EXPECT-PULSE header"; fail=1; continue
    fi

    work="out/$name"
    rm -rf "$work"
    mkdir -p "$work/src"
    cp "$case_file" "$work/src/"

    # The core invariant holds here too: a program Pulse refuses is still an ordinary C#
    # program, and a case that stopped compiling would be demonstrating nothing.
    if ! (cd "$work/src" && "$ROOT/test/build-cs.sh" "$name" "$name.cs" >/dev/null 2>&1); then
        echo "pulse-refusals: $name does not compile as ordinary C#"
        (cd "$work/src" && "$ROOT/test/build-cs.sh" "$name" "$name.cs" 2>&1 | sed 's/^/  /' | head -15)
        fail=1
        continue
    fi

    # Translation must be clean. A case that `palcs` refuses belongs in test/diagnostics,
    # and one that translates with a warning is not demonstrating what it claims to.
    translated=$("$PALCS" -o "$work/out" "$work/src/$name.cs" 2>&1)
    if printf '%s' "$translated" | grep -qE "PALCS[0-9]{4}"; then
        echo "pulse-refusals: $name was refused by palcs; it is a test/diagnostics case"
        printf '%s\n' "$translated" | sed 's/^/  /'
        fail=1
        continue
    fi

    # F* decides the module order itself, exactly as verify.mk does, so a case may span
    # several generated modules and still be checked in a valid order.
    opts=(--message_format json
          --cache_checked_modules --cache_dir "$work/cache"
          --already_cached 'Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore'
          --include "$work/cache" --include "$work/out"
          --include "$ROOT/pulse" --include "$ROOT/pulse/_cache")
    mkdir -p "$work/cache"
    generated=("$work"/out/*.fst)

    "$FSTAR" "${opts[@]}" --dep full "${generated[@]}" --output_deps_to "$work/depend" >/dev/null 2>&1
    # `ALL_FST_FILES` is a make variable written with line continuations, and it lists the
    # library too; what is wanted is this case's own modules in dependency order.
    order=$(tr -d '\\' < "$work/depend" | awk '/^ALL_FST_FILES=/{f=1} f{print} f&&!NF{exit}' \
            | tr ' \t' '\n' | grep "^$work/out/.*\.fst$")
    [ -z "$order" ] && order=$(printf '%s\n' "${generated[@]}")

    marker=$(grep -n "MARKER" "$case_file" | head -1 | cut -d: -f1)
    if [ -z "$marker" ]; then
        echo "pulse-refusals: $name has no MARKER comment on the offending line"; fail=1; continue
    fi
    # The comment sits on the line above the statement it marks, so that the statement
    # stays exactly the C# a reader would write.
    marker=$((marker + 1))

    got=""
    refused=0
    for module in $order; do
        case "$module" in "$work"/out/*) ;; *) continue ;; esac
        # F*'s exit status, not a grep for the word "error": a harness that decides
        # whether a proof failed by pattern-matching prose is a harness that will one day
        # pass because the prose changed.
        if out=$("$FSTAR" "${opts[@]}" "$module" 2>&1); then :; else refused=1; fi
        got="$got$out"$'\n'
    done

    if [ "$refused" = 0 ]; then
        echo "pulse-refusals: $name was expected to fail verification, and did not"
        fail=1
        continue
    fi

    # Everything from here on is checked against the *mapped* message rather than F*'s
    # own, because the mapped one is what a user is ever shown. That makes this one test
    # of the whole path: Pulse refused, it refused for the stated reason, and the refusal
    # arrived on the line that caused it.
    mapped=$(printf '%s' "$got" | "$PALCS" report -q -o "$work/out" 2>&1)

    if ! printf '%s\n' "$mapped" | grep -q -- "$want"; then
        echo "pulse-refusals: $name failed, but not for the stated reason ($want)"
        printf '%s\n' "$mapped" | sed 's/^/  /' | head -12
        fail=1
        continue
    fi

    if ! printf '%s\n' "$mapped" | grep -q "$name\.cs($marker,"; then
        echo "pulse-refusals: $name's failure was not reported at $name.cs:$marker"
        printf '%s\n' "$mapped" | sed 's/^/  /' | head -12
        fail=1
    fi
done

if [ "$fail" = 0 ]; then
    echo "pulse-refusals: OK ($count case(s))"
fi
exit $fail
