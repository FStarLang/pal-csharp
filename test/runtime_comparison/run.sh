#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
root=$(cd ../.. && pwd)
work="$PWD/obj/execution"
mkdir -p "$work"

cat > "$work/Run.csproj" <<EOF
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net10.0</TargetFramework>
    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="$PWD/Driver.cs.in" />
    <Compile Include="$PWD/Semantics.cs" />
    <Compile Include="$PWD/../shape_hierarchy/*.cs" />
    <Reference Include="Pal.Annotations">
      <HintPath>$root/src/Pal.Annotations/bin/Debug/net10.0/Pal.Annotations.dll</HintPath>
    </Reference>
  </ItemGroup>
</Project>
EOF
dotnet build "$work/Run.csproj" -c Release --nologo -v quiet > "$work/csharp-build.log" 2>&1 ||
  { cat "$work/csharp-build.log"; exit 1; }
dotnet "$work/bin/Release/net10.0/Run.dll" > "$work/csharp.txt"

opts=(--cache_checked_modules --cache_dir _cache
  --already_cached 'Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore'
  --include _cache --include out --include "$root/pulse/_cache"
  --include ../shape_hierarchy/out --include ../shape_hierarchy/_cache)
for case in ArrayLengthFalse SpanLengthFalse; do
  if "$root/tools/run-fstar.sh" "${opts[@]}" "refusals/$case.fst" > "$work/$case.log" 2>&1; then
    echo "soundness: $case unexpectedly proved False"; exit 1
  fi
done
grep -q 'Expected expression of type Pulse.Lib.CSharp.Array.Base.array' "$work/ArrayLengthFalse.log" ||
  { cat "$work/ArrayLengthFalse.log"; exit 1; }
grep -q 'FStar.SizeT.v (Pulse.Lib.Slice.len s) < Prims.pow2 31' "$work/SpanLengthFalse.log" ||
  { cat "$work/SpanLengthFalse.log"; exit 1; }

extract() {
  "$root/tools/run-fstar.sh" "${opts[@]}" --codegen OCaml \
    --custard_entry "$2" "$1" -o "$work/$3.ml" > "$work/$3.log" 2>&1 ||
    { cat "$work/$3.log"; return 1; }
}
for method in Xor And Or EagerAnd ShortAnd Narrow Widen Named DebugErasure ArrayOps; do
  extract "out/Func_Semantics_$method.fst" "Func_Semantics_$method.func_Semantics_$method" "$method"
done
for method in MakeAndSum GrowTile GrowAndMeasureSide; do
  extract "../shape_hierarchy/out/Func_Shapes_$method.fst" \
    "Func_Shapes_$method.func_Shapes_$method" "$method"
done
cp Pulse_Lib_CSharp_Assumptions.ml driver.ml "$work/"
(
  cd "$work"
  "$root/tools/fstar/bin/fstar.exe" --ocamlopt -I . \
    Pulse_Lib_CSharp_Assumptions.ml Xor.ml And.ml Or.ml EagerAnd.ml ShortAnd.ml \
    Narrow.ml Widen.ml Named.ml DebugErasure.ml ArrayOps.ml MakeAndSum.ml GrowTile.ml \
    GrowAndMeasureSide.ml driver.ml -o translated.exe
  ./translated.exe > pulse.txt
)
diff -u "$work/csharp.txt" "$work/pulse.txt"
echo "soundness: C# Release and extracted Pulse agree"
