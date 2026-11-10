#!/usr/bin/env bash
# Write the `.fst.config.json` files that let the F* IDE check generated modules
# interactively.
#
# The F* VS Code assistant (and fstar-mode) looks for a file whose name ends in
# `.fst.config.json`, searching from the directory of the file being edited up to the
# workspace root and taking the nearest one. A config in `test/swap/` therefore serves
# `test/swap/out/Func_Swapping_Swap.fst` as well as anything in `test/swap/` itself.
#
# The configs are generated rather than hand-written for the same reason `verify.mk` is
# shared: an IDE that disagrees with the build about include paths or `--already_cached`
# is worse than no IDE at all. Each config mirrors the options its directory's Makefile
# actually uses.
#
#   bash test/fst-configs.sh           write (or refresh) every config
#   bash test/fst-configs.sh --check   fail if any config is missing or stale
#
# The checked-in files are what the editor reads; `--check` runs in the test suite so
# they cannot drift from the build.

set -uo pipefail

cd "$(dirname "$0")/.."
ROOT=$(pwd)

CHECK=0
[ "${1:-}" = "--check" ] && CHECK=1

status=0

# ---------------------------------------------------------------------------
# Emit one config. Arguments: <directory> <fstar_exe> <already_cached> <include...>
# ---------------------------------------------------------------------------
write_config() {
    local dir=$1 exe=$2 cached=$3
    shift 3

    local name file includes
    name=$(basename "$dir")
    file="$dir/$name.fst.config.json"

    includes=$(printf '    "%s",\n' "$@")
    includes=${includes%,}

    local body
    body=$(cat <<EOF
{
  "fstar_exe": "$exe",
  "include_dirs": [
$includes
  ],
  "options": [
    "--cache_checked_modules",
    "--cache_dir", "_cache",
    "--already_cached", "$cached"
  ]
}
EOF
)

    if [ "$CHECK" = 1 ]; then
        if [ ! -f "$file" ]; then
            echo "fst-configs: missing $file"
            status=1
        elif ! diff -q <(printf '%s\n' "$body") "$file" >/dev/null; then
            echo "fst-configs: stale $file (run 'bash test/fst-configs.sh')"
            status=1
        fi
    else
        printf '%s\n' "$body" > "$file"
        echo "fst-configs: wrote $file"
    fi
}

# The set the harness itself uses (test/verify.mk).
TEST_CACHED='Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore'
# The support library is what defines Pulse.Lib.CSharp.*, so it cannot assume it cached.
PULSE_CACHED='Prims,FStar,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore'

# ---------------------------------------------------------------------------
# The support library.
# ---------------------------------------------------------------------------
write_config pulse ../tools/run-fstar.sh "$PULSE_CACHED" . _cache

# ---------------------------------------------------------------------------
# Acceptance directories, in both trees. Which include paths a directory needs
# follows from what it holds, so nothing here is a per-test special case:
#
#   .        the directory has hand-written .fst/.fsti at its root
#   out      `palcs` writes generated modules there
#   _cache   every directory that runs F* has one
#   ../../pulse{,/_cache}   Pulse.Lib.CSharp.*, as in verify.mk
#
# `examples/` sits at the same depth as `test/`, so the relative include paths are the
# same and an example needs no special case here either.
# ---------------------------------------------------------------------------
for dir in "$ROOT"/test/*/ "$ROOT"/examples/*/; do
    dir=${dir%/}
    rel=${dir#"$ROOT"/}
    includes=()

    # Hand-written F* at the directory root (fact pins, interop modules, smoke test).
    if compgen -G "$dir/*.fst" > /dev/null || compgen -G "$dir/*.fsti" > /dev/null; then
        includes+=(.)
    fi

    if [ "$rel" = test/diagnostics ]; then
        # Negative tests get a config *per case*, written by run.sh into each case's
        # own output directory. One directory-level config cannot serve them: every
        # case emits a module named `TranslationErrors`, so putting all the case
        # directories on one include path makes the name ambiguous and F* silently
        # resolves it to the wrong case. The nearest-config rule sorts this out.
        continue
    fi

    if grep -q 'verify\.mk' "$dir/Makefile" 2>/dev/null; then
        includes+=(out)
    fi

    # A directory with no F* at all (the erasure test) gets no config: the editor would
    # never consult it.
    if [ ${#includes[@]} -eq 0 ]; then
        continue
    fi

    includes+=(_cache ../../pulse ../../pulse/_cache)
    write_config "$rel" ../../tools/run-fstar.sh "$TEST_CACHED" "${includes[@]}"
done

if [ "$CHECK" = 1 ]; then
    [ "$status" = 0 ] && echo "fst-configs: OK"
    exit "$status"
fi
