#!/usr/bin/env bash
# Check a variant of `SortedSet<T>.CheckUniqueAndUnfoundElements` that is expected to FAIL
# verification (samples/dotnet-runtime/SORTEDSET-PR133116.md):
#
#   run.sh original            the body before dotnet/runtime#133116 (bitmap sized from Count)
#   run.sh pr133116-unfixed    dotnet/runtime#133116 as written, without the range check
#
# The patch is applied to the annotated runtime source, the harness is translated, the
# method's modules are checked, and the patch is reverted. Run `make` in ../ once first so
# that the referenced units (List, Queue, Stack) and the rest of the harness are checked.
set -u
here=$(cd "$(dirname "$0")" && pwd)
harness=$(dirname "$here")
root=$(git -C "$here" rev-parse --show-toplevel)

case "${1:-}" in
    original)         modules="Func_SortedSet_CheckUniqueAndUnfoundElements" ;;
    pr133116-unfixed) modules="Func_SortedSet_CheckUniqueAndUnfoundElements Func_TreeSubSet_at_SortedSet_CheckUniqueAndUnfoundElements" ;;
    *) echo "usage: $0 original|pr133116-unfixed" >&2; exit 2 ;;
esac
patch="$here/$1.patch"

git -C "$root" apply --check "$patch" || exit 2
git -C "$root" apply "$patch"
trap 'git -C "$root" apply -R "$patch"' EXIT

cd "$harness"
make --no-print-directory translate || exit 2
targets=$(for m in $modules; do printf '_cache/%s.fst.checked ' "$m"; done)
# REFERENCES as in ../Makefile.
make --no-print-directory -k -f "$root/test/verify.mk" PHASE=verify REFERENCES="../List ../Queue ../Stack" $targets
rc=$?
if [ $rc -ne 0 ]; then echo "run.sh $1: verification failed (expected)"; else echo "run.sh $1: verified (UNEXPECTED)"; fi
exit $rc
