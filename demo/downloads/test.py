#!/usr/bin/env python3
"""Run isolated loopback servers and the real-HTTP integration checks."""
import json
from pathlib import Path
import socket
import subprocess
import tempfile
import time
import urllib.error
import urllib.request

root = Path(__file__).resolve().parent
web_dir = root / "Web"
web_dll = web_dir / "bin/Debug/net10.0/Downloads.Web.dll"
tests_dll = root / "Tests/bin/Debug/net10.0/Downloads.Tests.dll"


def free_port():
    with socket.socket() as sock:
        sock.bind(("127.0.0.1", 0))
        return sock.getsockname()[1]


def stop(process):
    if process.poll() is None:
        process.terminate()
        try:
            process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait(timeout=10)


def ready(process, base):
    deadline = time.monotonic() + 30
    while time.monotonic() < deadline:
        if process.poll() is not None:
            raise RuntimeError(f"Server exited with {process.returncode}")
        try:
            with urllib.request.urlopen(base + "health", timeout=1) as response:
                if response.status == 200:
                    return
        except (urllib.error.URLError, TimeoutError):
            time.sleep(0.1)
    raise TimeoutError(f"Server did not start: {base}")


with tempfile.TemporaryDirectory(prefix="palcs-downloads-") as scratch:
    processes = []
    logs = []
    try:
        fixture_base = f"http://127.0.0.1:{free_port()}/"
        fixture_log = open(Path(scratch) / "fixture.log", "w+")
        logs.append(fixture_log)
        fixture = subprocess.Popen(
            ["dotnet", str(web_dll), "--fixture=true", "--urls", fixture_base],
            cwd=web_dir, stdout=fixture_log, stderr=subprocess.STDOUT)
        processes.append(fixture)
        ready(fixture, fixture_base)
        web_base = f"http://127.0.0.1:{free_port()}/"
        web_log = open(Path(scratch) / "web.log", "w+")
        logs.append(web_log)
        web = subprocess.Popen(
            ["dotnet", str(web_dll), "--FixtureBase", fixture_base, "--urls", web_base],
            cwd=web_dir, stdout=web_log, stderr=subprocess.STDOUT)
        processes.append(web)
        ready(web, web_base)
        subprocess.run(["dotnet", str(tests_dll), fixture_base, web_base], check=True, timeout=60)
        with urllib.request.urlopen(web_base, timeout=5) as page:
            assert b"Verified async downloads" in page.read()
        stop(fixture)
        try:
            urllib.request.urlopen(urllib.request.Request(web_base + "api/downloads", method="POST"), timeout=10)
            raise AssertionError("An unavailable source must not publish a completed result")
        except urllib.error.HTTPError as error:
            assert error.code == 502
            problem = json.load(error)
            assert problem["status"] == 502 and "downloads" not in problem
        print("HTTP failure response and web page OK.")
    except BaseException:
        for log in logs:
            log.flush()
            log.seek(0)
            print(log.read()[-12000:])
        raise
    finally:
        for process in reversed(processes):
            stop(process)
        for log in logs:
            log.close()
