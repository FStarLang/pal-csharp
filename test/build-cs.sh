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
    <ProjectReference Include="$root/src/Pal.Annotations/Pal.Annotations.csproj" />
  </ItemGroup>
</Project>
EOF

dotnet build -v q --nologo "$work/$name.csproj"
