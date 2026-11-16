import os
import subprocess
import sys
import tempfile
from pathlib import Path
from xml.sax.saxutils import escape

here = Path(__file__).resolve().parent
binary = Path(sys.argv[1]).resolve().parent
with tempfile.TemporaryDirectory(prefix="pal-spec-shim-") as directory:
    work = Path(directory)
    (work / "Program.cs").write_text((here / "SpecShim.cs.in").read_text())
    (work / "Shim.csproj").write_text("""
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>net10.0</TargetFramework><OutputType>Exe</OutputType>
    <ImplicitUsings>enable</ImplicitUsings><Nullable>enable</Nullable>
  </PropertyGroup>
  <ItemGroup>
""" + "\n".join(
        f'    <Reference Include="{name}"><HintPath>{escape(str(binary / (name + ".dll")))}</HintPath></Reference>'
        for name in ("Pal.Compiler", "Pal.Annotations", "Microsoft.CodeAnalysis", "Microsoft.CodeAnalysis.CSharp")
    ) + "\n  </ItemGroup>\n</Project>\n")
    checked = subprocess.run(
        ["dotnet", "run", "--project", str(work / "Shim.csproj"), "-p:UseSharedCompilation=false", "-v:q"],
        env=dict(os.environ, MSBUILDDISABLENODEREUSE="1", DOTNET_CLI_USE_MSBUILD_SERVER="0"),
        capture_output=True, text=True,
    )
    print(checked.stdout + checked.stderr, end="")
    raise SystemExit(checked.returncode)
