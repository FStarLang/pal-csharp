import subprocess
import re
import sys
import tempfile
from pathlib import Path

if sys.argv[1] == "--ghost-types":
    with tempfile.TemporaryDirectory(prefix="pal-plain-ghost-types-") as output:
        result = subprocess.run(
            [sys.argv[2], "-o", output, str(Path(__file__).with_name("WrongGhostType.cs.in"))],
            text=True, capture_output=True,
        )
        diagnostics = result.stdout + result.stderr
        assert result.returncode != 0 and diagnostics.count("error PALCS0885:") == 3, diagnostics
    print("Named ghost pointers reject wrong nullability, type arguments, and class names")
elif sys.argv[1] == "--null-safety":
    here = Path(__file__).resolve().parent
    root = here.parent.parent
    with tempfile.TemporaryDirectory(prefix="pal-plain-null-forgiven-") as temporary:
        output = Path(temporary)
        translated = subprocess.run(
            [sys.argv[2], "-o", temporary, str(here / "NullForgiven.cs.in")],
            text=True, capture_output=True,
        )
        assert translated.returncode == 0, translated.stdout + translated.stderr
        command = [
            str(root / "tools/run-fstar.sh"), "--cache_checked_modules",
            "--cache_dir", temporary, "--include", temporary,
            "--include", str(root / "pulse/_cache"),
        ]
        for name in ("Class_Cell", "Func_NullSafety_Keep"):
            checked = subprocess.run(
                command + [str(output / (name + ".fst"))], text=True, capture_output=True,
            )
            assert checked.returncode == 0, checked.stdout + checked.stderr
        for name in ("Func_NullSafety_BadReturn", "Func_NullSafety_BadCall"):
            checked = subprocess.run(
                command + [str(output / (name + ".fst"))], text=True, capture_output=True,
            )
            diagnostics = checked.stdout + checked.stderr
            assert checked.returncode != 0, "Null-forgiving bypassed non-null checking: " + name
            assert "Failed to prove" in diagnostics or "Could not prove" in diagnostics, diagnostics
    print("Null-forgiving does not prove non-null Plain returns or calls")
elif sys.argv[1] == "--emission":
    output = Path(__file__).with_name("out")
    direct = (output / "Func_PlainLocals_FromCalls.fst").read_text()
    applications = [
        line.strip() for line in direct.splitlines()
        if "func_PlainLocals_Make " in line
    ]
    assert applications == [
        "func_PlainLocals_Make var_calls var_left",
        "func_PlainLocals_Make var_calls var_right",
    ], applications

    cleanup = (output / "Func_PlainCleanupOwner_Conditional.fst").read_text()
    arms = re.findall(
        r"let (\w+) = func_PlainCleanupOwner_Identity var_this var_cell var_calls;"
        r"\n(.*?)\n\s*\1\s*\}",
        cleanup, re.DOTALL,
    )
    assert len(arms) == 2, cleanup
    invariant = "Class_PlainCleanupOwner.class_PlainCleanupOwner__inv var_this "
    for binder, remainder in arms:
        assert "with " in remainder and "assert (" + invariant in remainder
        assert "unfold " + invariant in remainder
    assert "B.op_Colon_Equals var_this " in cleanup
    guarded = (output / "Func_PlainLocals_NullTests.fst").read_text()
    assert "arg_cell: Class_OwnedCell.class_OwnedCell" in guarded
    assert "let mut var_cell : Class_OwnedCell.class_OwnedCell__opt = arg_cell;" in guarded
    assert "B.is_null" in guarded
    assert guarded.count("func_PlainLocals_Observe var_replacement var_calls") == 1
    print("Plain terminal calls and post-call owner cleanup emission passed")
else:
    with tempfile.TemporaryDirectory(prefix="pal-plain-definite-assignment-") as output:
        result = subprocess.run(
            [sys.argv[1], "-o", output, str(Path(__file__).with_name("Unassigned.cs.in"))],
            text=True,
            capture_output=True,
        )
        diagnostics = result.stdout + result.stderr
        if result.returncode == 0 or "CS0165" not in diagnostics:
            raise AssertionError("Missing assignment was not rejected:\n" + diagnostics)
    print("Plain local missing-assignment rejection passed")
