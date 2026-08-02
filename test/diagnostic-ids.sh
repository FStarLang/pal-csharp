#!/usr/bin/env bash
# The analyzer has to declare every diagnostic id it might report *before* it has seen a
# program, because Roslyn drops a diagnostic whose descriptor was not declared. So
# `Diagnostics/Catalog.cs` lists the ids, and a list is a thing that drifts.
#
# This is the detector that stops it drifting. It greps the passes for `"PALCSnnnn"`
# literals — which is where an id is really born, next to the rule it belongs to — and
# requires the catalog to name exactly that set, no more and no less. An id added to a
# pass and forgotten here would otherwise be invisible in the editor while working
# perfectly at the command line, which is the worst of the two failures.
#
# Severity is checked too, for the ids reported through `Error(` or `Warning(` directly.
# The few that come from a mapping table (a C# binding error rewritten as a pal-csharp
# one) are checked for presence only, since their severity is not visible to a grep.
set -uo pipefail

cd "$(dirname "$0")/.."
COMPILER=src/Pal.Compiler
CATALOG=$COMPILER/Diagnostics/Catalog.cs

status=0

# Ids as the passes name them, and as the catalog does.
used=$(grep -rhoE '"PALCS[0-9]{4}"' $COMPILER --include='*.cs' \
       --exclude=Catalog.cs | tr -d '"' | sort -u)
listed=$(grep -oE '"PALCS[0-9]{4}"' $CATALOG | tr -d '"' | sort -u)

missing=$(comm -23 <(echo "$used") <(echo "$listed"))
extra=$(comm -13 <(echo "$used") <(echo "$listed"))

if [ -n "$missing" ]; then
    echo "diagnostic-ids: reported by a pass but absent from Catalog.cs (the editor would"
    echo "                never show these):"
    echo "$missing" | sed 's/^/  /'
    status=1
fi

if [ -n "$extra" ]; then
    echo "diagnostic-ids: in Catalog.cs but reported by no pass:"
    echo "$extra" | sed 's/^/  /'
    status=1
fi

# Severity, where a grep can see it.
while read -r id severity; do
    [ -z "$id" ] && continue
    if ! grep -qE "\(\"$id\", Severity\.$severity\)" $CATALOG; then
        echo "diagnostic-ids: $id is reported as $severity but Catalog.cs disagrees"
        status=1
    fi
done < <(grep -rhoE '(Error|Warning)\("PALCS[0-9]{4}"' $COMPILER --include='*.cs' \
         --exclude=Catalog.cs | sed -E 's/^(Error|Warning)\("(PALCS[0-9]{4})"/\2 \1/' | sort -u)

if [ $status -eq 0 ]; then
    echo "diagnostic-ids: OK ($(echo "$listed" | wc -l) id(s))"
fi
exit $status
