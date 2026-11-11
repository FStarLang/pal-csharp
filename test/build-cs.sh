#!/usr/bin/env bash
# Compile a test's C# sources with the stock compiler, with PAL *undefined*.
#
# This is the check that keeps pal-csharp honest: an annotated program must build
# and run as ordinary C#, with the annotations contributing nothing. Rather than
# ask each test to carry a .csproj, we synthesise one in obj/.
set -euo pipefail

name="$1"; shift
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
work="obj/cs"
# A program written before nullable reference types (production code verified in place,
# doc/translation.md §20) sets PAL_CS_NULLABLE=disable; the tests keep the default.
nullable="${PAL_CS_NULLABLE:-enable}"

# Library assemblies the sources call (R21.5a), as `palcs -r` is given them.
refs="$(python3 - <<'PY'
import os
from xml.sax.saxutils import escape, quoteattr

for path in os.environ.get("PAL_CS_REFERENCES", "").split():
    name = os.path.splitext(os.path.basename(path))[0]
    print(f"    <Reference Include={quoteattr(name)}>"
          f"<HintPath>{escape(os.path.abspath(path))}</HintPath></Reference>")
PY
)"

mkdir -p "$work"
cat > "$work/$name.csproj" <<EOF
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework>
    <Nullable>$nullable</Nullable>
    <ImplicitUsings>enable</ImplicitUsings>
    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>
    <TreatWarningsAsErrors>true</TreatWarningsAsErrors>
  </PropertyGroup>
  <ItemGroup>
$(for f in "$@"; do printf '    <Compile Include="%s/%s" />\n' "$(pwd)" "$f"; done)
${refs}
    <ProjectReference Include="$root/src/Pal.Annotations/Pal.Annotations.csproj" />
  </ItemGroup>
</Project>
EOF

# Independent MSBuild processes otherwise race while rebuilding their shared
# Pal.Annotations project. Only C# compilation is serialized, not verification.
# Close the child descriptor so persistent MSBuild workers cannot retain the lock.
mkdir -p "$root/src/Pal.Annotations/obj"
flock --close "$root/src/Pal.Annotations/obj/pal-tests.lock" \
  dotnet build -v q --nologo "$work/$name.csproj"
