#!/usr/bin/env python3
"""Build and run identical tests against a pinned upstream snapshot and a one-line fix."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
UPSTREAM = ROOT / "upstream"
SOURCE = "src/libraries/System.Collections/src/System/Collections/Generic/SortedSet.cs"
TEST = "src/libraries/System.Collections/tests/Generic/SortedSet/SortedSet.TreeSubSet.Tests.cs"
OLD = "                int index = InternalIndexOf(item);"
NEW = "                int index = IsWithinRange(item) ? InternalIndexOf(item) : -1;"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def verify_snapshot():
    listed = set()
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split("  ", 1)
        path = UPSTREAM / name
        require(path.resolve().is_relative_to(UPSTREAM), f"Invalid manifest path: {name}")
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                f"Upstream snapshot changed: {name}")
        listed.add(path.resolve())
    actual = {p.resolve() for p in UPSTREAM.rglob("*") if p.is_file()}
    require(len(listed) == 8 and actual == listed, "Unexpected upstream file inventory")


def patch(name, before, after):
    return f"diff --git a/{name} b/{name}\n" + "".join(difflib.unified_diff(
        before.splitlines(keepends=True), after.splitlines(keepends=True),
        fromfile=f"a/{name}", tofile=f"b/{name}"))


def expected_patches():
    source = (UPSTREAM / SOURCE).read_text()
    require(source.count(OLD) == 1, "The production patch must replace exactly one lookup")
    test = (UPSTREAM / TEST).read_text()
    regression = (ROOT / "Regression.cs").read_text()
    method = regression.split("    // BEGIN UPSTREAM TEST\n")[1].split(
        "    // END UPSTREAM TEST\n")[0]
    method = "".join("    " + line if line.strip() else line
                     for line in method.splitlines(keepends=True))
    anchor = "        protected override int Min => int.MinValue;\n"
    require(test.count(anchor) == 1, "Missing integer fixture insertion point")
    return {
        "fix.patch": patch(SOURCE, source, source.replace(OLD, NEW)),
        "regression.patch": patch(TEST, test, test.replace(anchor, method + "\n" + anchor)),
    }


def prepare(write_patches):
    verify_snapshot()
    for name, content in expected_patches().items():
        path = ROOT / name
        if write_patches:
            path.write_text(content)
        else:
            require(path.read_text() == content, f"{name} differs from its reviewed scope")

    for variant in ("baseline", "fixed"):
        source_root = ROOT / "artifacts" / variant / "source"
        shutil.copytree(UPSTREAM, source_root, dirs_exist_ok=True)
        # A local repository prevents git apply from using an enclosing worktree.
        subprocess.run(["git", "init", "--quiet", str(source_root)], check=True)
        patches = [str(ROOT / "fix.patch"), str(ROOT / "regression.patch")]
        subprocess.run(["git", "apply", "--check", *patches], cwd=source_root, check=True)
        if variant == "fixed":
            subprocess.run(["git", "apply", *patches], cwd=source_root, check=True)
        for original in UPSTREAM.rglob("*"):
            if not original.is_file():
                continue
            relative = original.relative_to(UPSTREAM)
            actual = (source_root / relative).read_bytes()
            if variant == "fixed" and relative.as_posix() in (SOURCE, TEST):
                continue
            require(actual == original.read_bytes(), f"Unexpected variant change: {relative}")
        if variant == "fixed":
            require((source_root / SOURCE).read_text() ==
                    (UPSTREAM / SOURCE).read_text().replace(OLD, NEW),
                    "The fixed implementation differs by more than the range guard")


def run_variant(variant):
    directory = ROOT / "artifacts" / variant
    build = subprocess.run([
        "dotnet", "build", str(ROOT / "Repro.csproj"), "-c", "Release", "--nologo", "-v", "quiet",
        f"-p:UpstreamRoot={directory / 'source'}",
        f"-p:BaseIntermediateOutputPath={directory / 'obj'}/",
        f"-p:OutputPath={directory / 'bin'}/",
    ], cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (directory / "build.log").write_text(build.stdout)
    require(build.returncode == 0, f"{variant} build failed:\n{build.stdout}")
    result = subprocess.run(["dotnet", str(directory / "bin" / "Repro.dll")],
                            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (directory / "run.log").write_text(result.stdout)
    lines = [line.removeprefix("RESULT ") for line in result.stdout.splitlines()
             if line.startswith("RESULT ")]
    require(len(lines) == 1, f"{variant} did not complete the suite:\n{result.stdout}")
    data = json.loads(lines[0])
    buggy = variant == "baseline"
    expected = {
        "passed": 0 if buggy else 4,
        "failed": 4 if buggy else 0,
        "controls": 20,
        "observations": {name: buggy for name in
                         ("SetEquals", "IsSubsetOf", "IsProperSubsetOf", "IsProperSupersetOf")},
        "edgeFailures": [
            "outside-first-with-duplicates/IsSubsetOf",
            "outside-first-with-duplicates/IsProperSubsetOf",
            "descending-comparer/SetEquals",
            "descending-comparer/IsSubsetOf",
            "case-insensitive-comparer/SetEquals",
            "case-insensitive-comparer/IsSubsetOf",
        ] if buggy else [],
    }
    require(result.returncode == (1 if buggy else 0) and data == expected,
            f"Unexpected {variant} outcome (exit {result.returncode}):\n{result.stdout}")
    return variant, result.stdout, data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true", help="Check hashes and apply patches, without building")
    parser.add_argument("--write-patches", action="store_true", help="Regenerate patches from the one-line fix and Regression.cs")
    args = parser.parse_args()
    prepare(args.write_patches)
    if args.prepare_only:
        print("Snapshot hashes and both patches checked; variants prepared.")
        return
    with ThreadPoolExecutor(max_workers=2) as pool:
        results = list(pool.map(run_variant, ("baseline", "fixed")))
    for variant, output, _ in results:
        print(f"=== {variant} ===\n{output}", end="")
    verify_snapshot()
    (ROOT / "artifacts" / "results.json").write_text(json.dumps(
        {variant: data for variant, _, data in results}, indent=2) + "\n")
    print("Verified: exact baseline failures, identical tests passing with the one-line fix.")


if __name__ == "__main__":
    main()
