#!/usr/bin/env bash
# Anti-contortion check (doc/translation.md, rule 4):
#
#   "No example may be nameable from inside the compiler."
#
# The translator must implement the compositional translation scheme, not
# recognise individual test programs. If any test-suite directory name or
# annotated C# method name appears in Pal.Compiler, the translator has
# almost certainly been fitted to an example.

set -euo pipefail

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COMPILER_DIR="$REPO/src/Pal.Compiler"
# Both trees. An example's names are exactly as forbidden inside the compiler as a test's:
# the rule is that the translator implements a scheme, not that it passes `test/`.
TEST_DIRS=("$REPO/test" "$REPO/examples")

if [[ ! -d "$COMPILER_DIR" ]]; then
  echo "no-example-names: $COMPILER_DIR does not exist yet; skipping"
  exit 0
fi

status=0

# 1. No test directory name may appear in the compiler sources.
while IFS= read -r name; do
  if grep -rniq --include='*.cs' -- "$name" "$COMPILER_DIR"; then
    echo "error: test name '$name' appears in Pal.Compiler:" >&2
    grep -rni --include='*.cs' -- "$name" "$COMPILER_DIR" >&2
    status=1
  fi
done < <(grep -rl 'verify\.mk' --include='Makefile' "${TEST_DIRS[@]}" \
           | xargs -r -n1 dirname | xargs -r -n1 basename | sort -u)

# 2. No method name declared in a test .cs file may appear in the compiler.
while IFS= read -r ident; do
  if grep -rnqw --include='*.cs' -- "$ident" "$COMPILER_DIR"; then
    echo "error: test-declared identifier '$ident' appears in Pal.Compiler:" >&2
    grep -rnw --include='*.cs' -- "$ident" "$COMPILER_DIR" >&2
    status=1
  fi
done < <(grep -rhoP '(?<=\bstatic (?:void|int|bool|uint|long|byte) )\w+' \
           --include='*.cs' "${TEST_DIRS[@]}" 2>/dev/null | sort -u)

if [[ $status -eq 0 ]]; then
  echo "no-example-names: OK"
fi
exit $status
