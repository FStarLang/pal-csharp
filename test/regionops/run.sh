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
    <Nullable>enable</Nullable>
    <EnableDefaultCompileItems>false</EnableDefaultCompileItems>
    <TreatWarningsAsErrors>true</TreatWarningsAsErrors>
  </PropertyGroup>
  <ItemGroup>
    <Compile Include="$PWD/*.cs" />
    <Compile Include="$PWD/Runtime.cs.in" />
    <Reference Include="Pal.Annotations">
      <HintPath>$root/src/Pal.Annotations/bin/Debug/net10.0/Pal.Annotations.dll</HintPath>
    </Reference>
  </ItemGroup>
</Project>
EOF
export MSBUILDDISABLENODEREUSE=1 DOTNET_CLI_USE_MSBUILD_SERVER=0 UseSharedCompilation=false
dotnet build "$work/Run.csproj" -c Release --nologo -v quiet
dotnet "$work/bin/Release/net10.0/Run.dll"
