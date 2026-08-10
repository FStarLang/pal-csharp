#!/usr/bin/env bash
# Programs pal-csharp translates faithfully and Pulse then refuses.
#
# These are the cases the frontend deliberately does *not* rule on. A rule about what a
# separation logic can prove belongs in the separation logic: the frontend cannot see the
# prover's context, so any answer it gives is an approximation, and an approximation in the
# frontend is worse than a precise answer in the verifier because it is the frontend that
# has to be trusted. §0 rule 3 says the emitter never invents a proof step; this is the
# same rule pointed the other way -- the *checker* never invents a refusal.
#
# So the refusal has to be tested where it happens. Each case carries an `EXPECT-PULSE:`
# header naming the resource or property F* must report as unprovable. The case is
# translated with no diagnostics at all -- that is half the point, the translation is
# faithful -- and then F* must fail, and must fail for the stated reason rather than for
# some other reason that happens to also be a failure.
#
# Landing on the right C# line is the other half, and it is checked here too. F* reports
# against a `.fst` nobody wrote; `palcs report` reads the emitter's line map and says it
# again against the source. A `MARKER` comment in each case marks the line the message
# must arrive at, so the assertion moves when the file is edited and cannot quietly
# describe the wrong statement.
#
# The suite is organised by *obligation kind* rather than by language feature: for each
# kind of thing the translation asks F* to prove -- an index is in bounds, a sum is
# representable, a loop invariant survives an iteration, a borrow is given back -- there is
# a case where that proof is the one that fails. A negative suite grouped by feature tends
# to test the same two obligations from many angles; grouped by obligation it says which
# obligations exist, and `cases/README.md` keeps that inventory honest.
#
# Usage: run.sh [case-name ...]   -- with no arguments, every case; with arguments, just
# those, which is how you iterate on one without paying for the rest. `PAL_JOBS` caps
# concurrency (default 16); each case is an independent F* invocation over its own output
# directory, so they do not interact.
set -u

# Resolved before the `cd`, because the dispatcher re-invokes this script by path.
SELF=$(cd "$(dirname "$0")" && pwd)/$(basename "$0")
cd "$(dirname "$0")"
ROOT=$(cd ../.. && pwd)
PALCS="$ROOT/src/Pal.Tool/bin/Debug/net10.0/palcs"
FSTAR="$ROOT/tools/run-fstar.sh"
JOBS=${PAL_JOBS:-16}

# One case, start to finish. Everything it prints goes to stdout and is captured by the
# caller, so that parallel cases cannot interleave their diagnostics; the exit status is
# the verdict.
run_case() {
    local case_file=$1
    local name work want translated opts generated order marker got refused mapped module out

    name=$(basename "$case_file" .cs)
    want=$(sed -n 's|^// EXPECT-PULSE: *||p' "$case_file" | head -1)

    if [ -z "$want" ]; then
        echo "pulse-refusals: $name has no EXPECT-PULSE header"; return 1
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
        return 1
    fi

    # Translation must be clean. A case that `palcs` refuses belongs in test/diagnostics,
    # and one that translates with a warning is not demonstrating what it claims to.
    translated=$("$PALCS" -o "$work/out" "$work/src/$name.cs" 2>&1)
    if printf '%s' "$translated" | grep -qE "PALCS[0-9]{4}"; then
        echo "pulse-refusals: $name was refused by palcs; it is a test/diagnostics case"
        printf '%s\n' "$translated" | sed 's/^/  /'
        return 1
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
        echo "pulse-refusals: $name has no MARKER comment on the offending line"; return 1
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
        return 1
    fi

    # Everything from here on is checked against the *mapped* message rather than F*'s
    # own, because the mapped one is what a user is ever shown. That makes this one test
    # of the whole path: Pulse refused, it refused for the stated reason, and the refusal
    # arrived on the line that caused it.
    mapped=$(printf '%s' "$got" | "$PALCS" report -q -o "$work/out" 2>&1)

    if ! printf '%s\n' "$mapped" | grep -q -- "$want"; then
        echo "pulse-refusals: $name failed, but not for the stated reason ($want)"
        printf '%s\n' "$mapped" | sed 's/^/  /' | head -40
        return 1
    fi

    if ! printf '%s\n' "$mapped" | grep -q "$name\.cs($marker,"; then
        echo "pulse-refusals: $name's failure was not reported at $name.cs:$marker"
        printf '%s\n' "$mapped" | sed 's/^/  /' | head -40
        return 1
    fi
    return 0
}

# Invoked as `run.sh --one <file>` by the dispatcher below, so that each case is a fresh
# process with its own shell state.
if [ "${1:-}" = "--one" ]; then
    run_case "$2"
    exit $?
fi

selected=()
if [ "$#" -gt 0 ]; then
    for want_name in "$@"; do
        if [ -f "cases/$want_name.cs" ]; then
            selected+=("cases/$want_name.cs")
        else
            echo "pulse-refusals: no such case: $want_name"; exit 1
        fi
    done
else
    selected=(cases/*.cs)
fi

mkdir -p out
fail=0
count=0
pids=()
logs=()

for case_file in "${selected[@]}"; do
    count=$((count + 1))
    log="out/$(basename "$case_file" .cs).log"
    logs+=("$log")
    bash "$SELF" --one "$case_file" > "$log" 2>&1 &
    pids+=($!)

    # A fixed cap rather than one process per case: each case runs F*, which is not a
    # cheap process, and a suite that oversubscribes the machine takes longer than one
    # that does not.
    while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do wait -n; done
done

for i in "${!pids[@]}"; do
    if ! wait "${pids[$i]}"; then fail=1; fi
    cat "${logs[$i]}"
done

if [ "$fail" = 0 ]; then
    echo "pulse-refusals: OK ($count case(s))"
fi
exit $fail
