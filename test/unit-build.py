#!/usr/bin/env python3
"""Exercise verification-unit ordering, incremental rebuilds, and cache ownership."""

import os
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
PALCS = ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs"


def main():
    scratch = ROOT / "test/unit_diagnostics/out"
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="build-", dir=scratch) as temporary:
        work = Path(temporary)
        calls = work / "fstar.log"
        wrapper = work / "fstar.sh"
        wrapper.write_text(
            '#!/bin/bash\nset -eu\n'
            f'printf "%s\\n" "$PWD $*" >> "{calls}"\n'
            f'exec "{ROOT}/tools/run-fstar.sh" "$@"\n'
        )
        wrapper.chmod(0o755)
        dependencies = {
            "base": [],
            "left": ["base"],
            "right": ["base"],
            "client": ["left", "right"],
        }
        bodies = {
            "base": "return 0;",
            "left": "return Base.Get();",
            "right": "return Base.Get();",
            "client": "return Left.Get();",
        }
        for name, references in dependencies.items():
            directory = work / name
            directory.mkdir()
            (directory / "Makefile").write_text(
                f"REFERENCES := {' '.join('../' + r for r in references)}\n"
                f"include {ROOT}/test/verify.mk\n"
            )
            (directory / "Code.cs").write_text(
                "using PalLang;\n"
                f"public static class {name.title()} {{\n"
                '[Ensures("Result >= 0")]\n'
                f"public static int Get() {{ {bodies[name]} }}\n"
                "}\n"
            )
        (work / "Makefile").write_text(
            ".PHONY: all base left right client\nall: client\n"
            "client: left right\nleft right: base\n"
            "base left right client:\n"
            "\t$(MAKE) -C $@ verify REFERENCES_BUILT=1\n"
        )

        def run(*args, expected=0, directory=work):
            result = subprocess.run(
                ["make", "--no-print-directory", "-j4", *args,
                 f"FSTAR_EXE={wrapper}", f"PALCS={PALCS}"],
                cwd=directory, text=True, stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
            )
            if (result.returncode == 0) != (expected == 0):
                raise AssertionError(result.stdout)
            return result.stdout

        run()
        first_calls = calls.read_text()
        for name in dependencies:
            assert first_calls.count(f"out/Func_{name.title()}_Get.fst\n") == 1, first_calls
        stamps = {name: (work / name / "out/.stamp").stat().st_mtime_ns
                  for name in dependencies}
        run()
        assert calls.read_text() == first_calls, "unchanged build ran F* again"
        assert all((work / name / "out/.stamp").stat().st_mtime_ns == stamp
                   for name, stamp in stamps.items()), "unchanged build translated again"

        # A timestamp-only change leaves every manifest unchanged, but must still
        # propagate translation through both arms of the diamond to the client.
        os.utime(work / "base/Code.cs", None)
        run()
        assert all((work / name / "out/.stamp").stat().st_mtime_ns > stamp
                   for name, stamp in stamps.items()), "transitive change did not propagate"
        def proofs(log):
            return [line for line in log.splitlines() if " --dep " not in line]

        assert proofs(calls.read_text()) == proofs(first_calls), "unchanged emitted modules were re-proved"

        base_cache = work / "base/_cache/Func_Base_Get.fst.checked"
        obsolete = work / "left/_cache/Func_Base_Get.fst.checked"
        shutil.copy2(base_cache, obsolete)
        depend = work / "client/_cache/.depend"
        old_dependencies = depend.read_text()
        depend.write_text(old_dependencies +
                          f"\n_cache/Func_Client_Get.fst.checked: {obsolete}\n")
        os.utime(work / "left/Code.cs", None)
        run()
        assert str(obsolete) not in depend.read_text(), "obsolete dependency edge survived"

        # Old harnesses may have checked shared modules in their own cache. They must
        # not shadow the referenced unit, even if its real checked file is missing.
        shutil.copy2(base_cache, obsolete)
        base_cache.unlink()
        (work / "left/_cache/.depend").unlink()
        before = calls.read_text()
        output = run("-f", str(ROOT / "test/verify.mk"), "PHASE=verify",
                     "REFERENCES=../base", "_verify", expected=1, directory=work / "left")
        assert "verify its unit first" in output or "already_cached" in output, output
        new_calls = calls.read_text()[len(before):]
        assert " out/Func_Base_Get.fst\n" not in new_calls, "client re-proved its dependency"
        run()
        assert not (work / "left/_cache/Func_Base_Get.fst.checked").exists(), "old dependency cache survived"

        def rejected(reference, message):
            result = subprocess.run(
                [str(PALCS), "--reference", str(reference), "-o", str(work / "rejected"),
                 str(work / "client/Code.cs")],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            assert result.returncode == 2 and message in result.stdout, result.stdout

        rejected(work / "missing", "has no unit.json")
        source = work / "base/Code.cs"
        original = source.read_text()
        source.write_text(original + "\n")
        rejected(work / "left/out", "is stale")
        source.write_text(original)

        manifest = work / "base/out/unit.json"
        original = manifest.read_text()
        cyclic = json.loads(original)
        cyclic["references"] = [str(work / "client/out")]
        manifest.write_text(json.dumps(cyclic))
        rejected(work / "client/out", "form a cycle")
        manifest.write_text("{invalid")
        rejected(work / "base/out", "invalid unit.json")
        manifest.write_text(original)

    print("unit-build: OK (diamond, no-op, transitive rebuild, stale cache, invalid references)")


if __name__ == "__main__":
    main()
