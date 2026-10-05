"""Measure native Linux isolation prerequisites using only fresh temporary fixtures.

This is not the production isolation test, a Lean build, or a proof audit.
"""
import ctypes
import errno
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import tempfile
import uuid

PAYLOAD = r'''
import errno
import json
import os
from pathlib import Path
import socket
import sys
protected, writable = map(Path, sys.argv[1:3])
results = {"payload_uid": os.getuid(), "denials": {}}
for name, action in [
    ("protected_write", lambda: protected.write_text("unexpected write")),
    ("protected_chmod", lambda: protected.chmod(0o777)),
]:
    try:
        action()
    except OSError as ex:
        results["denials"][name] = {"denied": ex.errno == errno.EROFS, "errno": ex.errno}
    else:
        results["denials"][name] = {"denied": False}
for name, family in [("unix_socket", socket.AF_UNIX), ("inet_socket", socket.AF_INET)]:
    try:
        with socket.socket(family, socket.SOCK_STREAM):
            pass
    except OSError as ex:
        results["denials"][name] = {
            "denied": ex.errno in {errno.EPERM, errno.EACCES, errno.EAFNOSUPPORT},
            "errno": ex.errno,
        }
    else:
        results["denials"][name] = {"denied": False}
(writable / "allowed.txt").write_text("dedicated build output")
results["dedicated_write"] = True
print(json.dumps(results, sort_keys=True), flush=True)
'''


def query_landlock_abi():
    # Linux v6.12 UAPI syscall 444; VERSION only queries capability.
    # https://docs.kernel.org/userspace-api/landlock.html
    if platform.machine() not in {"x86_64", "aarch64"}:
        return {"abi": None, "error": "unsupported probe architecture"}
    libc = ctypes.CDLL(None, use_errno=True)
    libc.syscall.restype = ctypes.c_long
    value = libc.syscall(ctypes.c_long(444), ctypes.c_void_p(),
                         ctypes.c_size_t(0), ctypes.c_uint(1))
    return {"abi": int(value) if value >= 0 else None,
            "errno": ctypes.get_errno() if value < 0 else 0}


def main():
    if sys.platform != "linux" or os.getuid() == 0:
        raise SystemExit("Run this native probe on Linux as the unprivileged CI user")
    root = Path(tempfile.mkdtemp(prefix="dagger-capabilities-", dir=os.environ["RUNNER_TEMP"]))
    build = root / "build"
    build.mkdir()
    sentinel = root / "trusted-sentinel.txt"
    sentinel.write_text("original trusted fixture")
    payload = root / "payload.py"
    payload.write_text(PAYLOAD)
    properties = [
        f"User={os.getuid()}", f"Group={os.getgid()}",
        "NoNewPrivileges=yes", "ProtectSystem=strict",
        f"ReadWritePaths={build}", "RestrictAddressFamilies=~AF_UNIX",
        "SystemCallFilter=~@network-io @debug", "SystemCallErrorNumber=EPERM",
        "CapabilityBoundingSet=", "RestrictSUIDSGID=yes",
        "ProtectKernelTunables=yes", "ProtectKernelModules=yes",
        "ProtectControlGroups=yes", "UMask=0077",
    ]
    command = ["sudo", "-n", "systemd-run", "--quiet", "--wait", "--pipe", "--collect",
               f"--unit=dagger-capability-{uuid.uuid4().hex}"]
    command += [f"--property={value}" for value in properties]
    command += ["--", "/usr/bin/python3", "-I", "-B", str(payload), str(sentinel), str(build)]
    result = subprocess.run(command, capture_output=True, text=True, timeout=60, check=False)
    report = {
        "scope": "native kernel/system-manager prerequisites only",
        "kernel": platform.release(), "architecture": platform.machine(),
        "systemd": subprocess.run(["systemd", "--version"], capture_output=True,
                                  text=True, check=True).stdout.splitlines()[0],
        "landlock": query_landlock_abi(), "caller_uid": os.getuid(),
        "system_manager_properties": properties,
        "payload_exit_code": result.returncode,
        "payload_stdout": result.stdout, "payload_stderr": result.stderr,
        "production_landrun_command_executed": False,
        "Lean_or_external_proofs_executed": False,
        "trusted_fixture_unchanged": sentinel.read_text() == "original trusted fixture",
        "dedicated_output": (build / "allowed.txt").read_text()
                            if (build / "allowed.txt").exists() else None,
    }
    try:
        data = json.loads(result.stdout)
    except json.JSONDecodeError:
        data = {}
    report["payload_report"] = data
    abi = report["landlock"]["abi"]
    report["minimum_abi6_available"] = abi is not None and abi >= 6
    denials = data.get("denials", {})
    report["system_manager_probe_passed"] = (
        result.returncode == 0 and data.get("payload_uid") == os.getuid()
        and set(denials) == {"protected_write", "protected_chmod", "unix_socket", "inet_socket"}
        and all(item.get("denied") for item in denials.values())
        and report["trusted_fixture_unchanged"]
        and report["dedicated_output"] == "dedicated build output"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    if not report["minimum_abi6_available"] or not report["system_manager_probe_passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
