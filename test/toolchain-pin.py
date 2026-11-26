#!/usr/bin/env python3
"""Check source-patch validation and toolchain cache identity without building F*."""
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent


class ToolchainPinTests(unittest.TestCase):
    def setUp(self):
        cache = ROOT / "test/_cache"
        cache.mkdir(exist_ok=True)
        self.temporary = tempfile.TemporaryDirectory(prefix="toolchain-pin-", dir=cache)
        self.addCleanup(self.temporary.cleanup)
        self.tools = Path(self.temporary.name)
        shutil.copyfile(ROOT / "tools/install-fstar.sh", self.tools / "install-fstar.sh")
        (self.tools / "fstar/bin").mkdir(parents=True)
        shutil.copyfile("/bin/true", self.tools / "fstar/bin/fstar.exe")
        (self.tools / "fstar/bin/fstar.exe").chmod(0o755)
        (self.tools / "fix.patch").write_text("fixture patch\n")
        self.digest = hashlib.sha256((self.tools / "fix.patch").read_bytes()).hexdigest()
        self.pin = {"result": "base", "patch": "fix.patch", "patch_sha256": self.digest}
        self.version = f"base-patch-{self.digest}"
        # Reaching the build path must not access the network or a real checkout.
        (self.tools / "bin").mkdir()
        for name in ("git", "opam"):
            stub = self.tools / "bin" / name
            stub.write_text("#!/bin/sh\necho toolchain-pin-build-path >&2\nexit 71\n")
            stub.chmod(0o755)
        (self.tools / "src/.git").mkdir(parents=True)

    def run_installer(self):
        (self.tools / "fstar-source.txt").write_text(
            "".join(f"{key}={value}\n" for key, value in self.pin.items()))
        (self.tools / "fstar/version.txt").write_text(self.version + "\n")
        env = dict(os.environ, FSTAR_SRC=str(self.tools / "src"),
                   PATH=str(self.tools / "bin") + os.pathsep + os.environ["PATH"])
        return subprocess.run(["bash", self.tools / "install-fstar.sh"], env=env,
                              capture_output=True, text=True, timeout=10)

    def test_matching_patched_cache(self):
        result = self.run_installer()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_unpatched_cache_compatibility(self):
        self.pin = {"result": "base"}
        self.version = "base"
        result = self.run_installer()
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_digest_mismatch_rejected_even_on_cache_hit(self):
        (self.tools / "fix.patch").write_text("changed patch\n")
        result = self.run_installer()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("does not match patch_sha256", result.stderr)

    def test_patch_and_digest_are_both_required(self):
        for missing in ("patch", "patch_sha256"):
            with self.subTest(missing=missing):
                saved = self.pin.pop(missing)
                result = self.run_installer()
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("requires both patch and patch_sha256", result.stderr)
                self.pin[missing] = saved

    def test_new_patch_does_not_reuse_old_cache(self):
        (self.tools / "fix.patch").write_text("new pinned patch\n")
        self.pin["patch_sha256"] = hashlib.sha256(
            (self.tools / "fix.patch").read_bytes()).hexdigest()
        result = self.run_installer()
        self.assertEqual(result.returncode, 71, result.stderr)
        self.assertIn("toolchain-pin-build-path", result.stderr)


if __name__ == "__main__":
    unittest.main()
