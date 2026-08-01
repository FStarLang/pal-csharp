#!/usr/bin/env bash
# Run the pinned F* from tools/fstar with the pal-csharp Pulse support
# library on the include path.
#
# Mirrors pal/opt/run-fstar.sh.

set -euo pipefail

TOOLS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_DIR="$(dirname "$TOOLS_DIR")"
FSTAR="$TOOLS_DIR/fstar/bin/fstar.exe"

if [[ ! -x "$FSTAR" ]]; then
  echo "error: $FSTAR not found; run 'make tools' (or tools/install-fstar.sh)" >&2
  exit 1
fi

exec "$FSTAR" ${OTHERFLAGS:-} --include "$REPO_DIR/pulse" "$@"
