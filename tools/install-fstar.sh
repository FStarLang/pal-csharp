#!/usr/bin/env bash
# Install a pinned F*/Pulse toolchain into tools/fstar.
#
# The version is pinned in tools/fstar-version.txt so that the local
# toolchain and CI cannot drift. The pin matches pal/opt/install-fstar.sh
# so that Pulse.Lib.CSharp.* stays compatible with the Pulse.Lib.C.*
# modules it is seeded from.
#
# The F* binary release bundles Pulse (lib/fstar/pulse), so no separate
# Pulse install is required.
#
# Usage:  tools/install-fstar.sh [extra install-fstar.sh options]
#         tools/install-fstar.sh --list      # show available nightlies

set -euo pipefail

TOOLS_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VERSION="$(tr -d '[:space:]' < "$TOOLS_DIR/fstar-version.txt")"

curl -fsSL https://aka.ms/install-fstar | bash -s -- \
  --nightly \
  --version "$VERSION" \
  --dest "$TOOLS_DIR/fstar" \
  --no-link \
  "$@"
