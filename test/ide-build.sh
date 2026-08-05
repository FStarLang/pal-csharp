#!/usr/bin/env bash
# Build the editor projects -- the other half of the C# obligation.
#
# `test/verify.mk` compiles every acceptance directory with a *stock* project synthesised
# by `build-cs.sh`, deliberately without pal-csharp's analyzer, because the invariant it
# checks is that annotated C# is ordinary C#. That leaves the complementary property
# unchecked: that the analyzer stays *silent* on the programs the translator accepts. An
# analyzer that reports a spurious error is invisible to `make test` -- the proof still
# goes through -- but it is the first thing a contributor sees when they open the file.
#
# So: build the generated editor projects (test/pal-tests.props loads the analyzer into
# them) and require a clean build. `-warnaserror` because this tree is currently clean and
# there is no reason to let it stop being so.
#
# The project list comes from Pal.Tests.sln, which `cs-projects.sh` generates and the lint
# checks for drift, so a directory added to the tree is covered here without being named.
#
# One project is excluded, and it is excluded by design: `test/diagnostics/cases` is a
# collection of programs that pal-csharp is *supposed* to reject, so the analyzer reports
# an error in each of them and the project cannot build. That is what `test/diagnostics`
# asserts, one `// EXPECT:` line at a time. Building it here would be asserting the
# opposite.
#
# Usage:  test/ide-build.sh

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SLN="$ROOT/Pal.Tests.sln"

if [[ ! -f "$SLN" ]]; then
    echo "ide-build: $SLN not found; run 'bash test/cs-projects.sh'" >&2
    exit 1
fi

# The one project whose whole purpose is to not compile.
EXCLUDE='test/diagnostics/cases'

mapfile -t projects < <(
    grep -o '"[^"]*\.csproj"' "$SLN" | tr -d '"' | grep -v "$EXCLUDE" | sort -u
)

if [[ ${#projects[@]} -eq 0 ]]; then
    echo "ide-build: no projects found in $SLN" >&2
    exit 1
fi

failed=0
for proj in "${projects[@]}"; do
    if ! out=$(dotnet build "$ROOT/$proj" --nologo -v q -warnaserror 2>&1); then
        echo "ide-build: FAILED $proj"
        echo "$out" | grep -E 'error|warning' | sort -u | head -20
        failed=1
    fi
done

if [[ $failed -ne 0 ]]; then
    echo "ide-build: at least one editor project does not build cleanly." >&2
    echo "The analyzer must not report anything on a program pal-csharp accepts." >&2
    exit 1
fi

echo "ide-build: OK (${#projects[@]} project(s), analyzer silent)"
