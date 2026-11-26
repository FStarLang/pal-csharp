#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
work="$PWD/obj/execution"
mkdir -p "$work"
cp Runtime.csproj.in "$work/Run.csproj"
export MSBUILDDISABLENODEREUSE=1 DOTNET_CLI_USE_MSBUILD_SERVER=0 UseSharedCompilation=false
dotnet build "$work/Run.csproj" -c Release --nologo -v quiet
dotnet "$work/bin/Release/net10.0/Run.dll"
