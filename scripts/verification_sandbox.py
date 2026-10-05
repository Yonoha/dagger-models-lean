"""Fail-closed native boundary for elaboration AND every artifact consumer."""
import ctypes
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

LANDRUN_PIN = "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"
MIN_ABI = 6


def ordinary(path):
    path = Path(path)
    if path.is_symlink() or not path.is_file():
        raise ValueError("Expected an ordinary trusted file: " + str(path))
    if any(c in str(path.resolve()) for c in "\n\r\t ,:%"):
        raise ValueError("Unsupported sandbox path syntax: " + str(path))
    return path.resolve()


def native_guard(landrun):
    if sys.platform != "linux" or os.geteuid() == 0:
        raise RuntimeError("Verification requires native Linux and a nonroot controller")
    landrun = ordinary(landrun)
    source = landrun.parent
    revision = subprocess.run(["git", "-C", str(source), "rev-parse", "HEAD"],
                              check=True, capture_output=True, text=True).stdout.strip()
    if revision != LANDRUN_PIN:
        raise ValueError("Landrun source checkout is not the unchanged pin")
    changed = subprocess.run(["git", "-C", str(source), "status", "--porcelain",
                              "--untracked-files=no"], check=True,
                             capture_output=True, text=True).stdout.strip()
    if changed:
        raise ValueError("Tracked pinned Landrun sources have changed")
    if platform.machine() not in {"x86_64", "aarch64"}:
        raise RuntimeError("ABI syscall number not bound for this architecture")
    libc = ctypes.CDLL(None, use_errno=True)
    abi = libc.syscall(444, 0, 0, 1)  # landlock_create_ruleset VERSION, not a ruleset
    if abi < MIN_ABI:
        raise RuntimeError(f"Landlock ABI >= {MIN_ABI} required, observed {abi}")
    return {"platform": "linux", "uid": os.getuid(), "gid": os.getgid(),
            "landlock_abi": abi, "minimum_abi": MIN_ABI, "landrun_revision": revision,
            "landrun_binary_sha256": hashlib.sha256(landrun.read_bytes()).hexdigest()}


def execute(command, *, cwd, env, timeout):
    return subprocess.run(command, cwd=cwd, env=env, timeout=timeout,
                          capture_output=True, text=True, check=True)


class Sandbox:
    def __init__(self, landrun, prefix, python, info, runner=execute, log_file=None,
                 readonly=()):
        self.landrun = ordinary(landrun)
        self.prefix = Path(prefix).resolve()
        # Venv launch symlinks are trusted inputs; retain their argv spelling so
        # Python uses the trusted venv. The resolved interpreter must be ordinary.
        self.python = Path(python).absolute()
        ordinary(self.python.resolve())
        self.info = info
        self.runner = runner
        self.calls = []
        self.log_file = Path(log_file) if log_file else None
        self.readonly = [Path(p).resolve() for p in readonly]
        if info["uid"] == 0 or info["landlock_abi"] < MIN_ABI:
            raise RuntimeError("Invalid native boundary preflight")

    def record(self):
        if self.log_file:
            self.log_file.write_text(json.dumps(self.calls, indent=2, default=str) + "\n")

    def run(self, payload, *, cwd, writable, extra_env=None, timeout=900):
        cwd = Path(cwd).resolve()
        roots = [Path(p).resolve() for p in writable]
        if not roots or any(not p.is_dir() or p.is_symlink() for p in writable):
            raise ValueError("Writable output directories must exist and be ordinary")
        for root in roots:
            if not root.is_relative_to(cwd):
                raise ValueError("Writable directory is outside the per-run project")
            if root == cwd or cwd.is_relative_to(root):
                raise ValueError("Project/control root cannot be writable")
            if any(c in str(root) for c in "\n\r\t ,:%"):
                raise ValueError("Unsupported output path syntax")
        environment = {
            "PATH": str(self.prefix / "bin") + ":/usr/bin:/bin",
            "HOME": str(Path.home()), "LEAN_ABORT_ON_PANIC": "1",
            "PYTHONDONTWRITEBYTECODE": "1", "MATHLIB_NO_CACHE_ON_UPDATE": "1",
            "TMPDIR": str(roots[0] / "tmp"),
        }
        (roots[0] / "tmp").mkdir(exist_ok=True)
        if extra_env:
            if set(extra_env) - {"LEAN_PATH", "DAGGER_VERIFY_ARTIFACT_PROBE"}:
                raise ValueError("Unapproved sandbox environment override")
            environment.update(extra_env)
        # ProtectSystem=strict alone leaves /home writable on the measured runner.
        # Explicit per-run/control/tool roots are required; child output mounts
        # are reopened by ReadWritePaths. Mandatory native metadata denials test it.
        readonly = list(dict.fromkeys([cwd, *self.readonly, self.prefix,
                                      self.python.parent.parent,
                                      self.landrun.parent, Path(__file__).resolve().parent]))
        if any(any(c in str(p) for c in "\n\r\t ,:%") for p in readonly):
            raise ValueError("Unsupported trusted read-only path syntax")
        command = ["sudo", "-n", "systemd-run", "--quiet", "--wait", "--collect", "--pipe",
                   f"--uid={self.info['uid']}", f"--gid={self.info['gid']}",
                   "--property=Type=exec",
                   "--property=NoNewPrivileges=yes", "--property=CapabilityBoundingSet=",
                   "--property=AmbientCapabilities=", "--property=ProtectSystem=strict",
                   "--property=ProtectHome=read-only", "--property=PrivateDevices=yes",
                   "--property=ProtectKernelTunables=yes", "--property=ProtectKernelModules=yes",
                   "--property=ProtectControlGroups=yes", "--property=PrivateNetwork=yes",
                   "--property=PrivateIPC=yes", "--property=RestrictNamespaces=yes",
                   "--property=SystemCallArchitectures=native",
                   "--property=RestrictAddressFamilies=~AF_UNIX",
                   "--property=SystemCallFilter=~@network-io @debug @mount @keyring",
                   "--property=SystemCallErrorNumber=EPERM", "--property=RestrictSUIDSGID=yes",
                   "--property=KillMode=control-group", "--property=TimeoutStopSec=5",
                   f"--property=RuntimeMaxSec={timeout}",
                   "--property=ReadOnlyPaths=" + " ".join(map(str, readonly)),
                   "--property=ReadWritePaths=" + " ".join(map(str, roots)),
                   f"--working-directory={cwd}", str(self.landrun),
                   "--best-effort", "--ro", "/", "--rw", "/dev/null", "--ldd", "--add-exec"]
        # Best effort cannot drop required ABI<=6 features: guard above is mandatory.
        # ABI7 logging/8TSYNC/9pathname UNIX are NOT relied on for the boundary.
        for path in [Path("/usr"), Path("/lib"), Path("/lib64"), self.prefix,
                     self.python.parent.parent]:
            if path.is_dir():
                command += ["--rox", str(path)]
        for root in roots:
            command += ["--rwx", str(root)]
        # Read-only executable candidate companions may be loaded ONLY in this boundary.
        artifacts = cwd / ".lake/build"
        if artifacts.is_dir():
            command += ["--rox", str(artifacts)]
        for name, value in environment.items():
            command += ["--env", name + "=" + value]
        command += ["--", *map(str, payload)]
        self.calls.append({"argv": command, "cwd": str(cwd), "writable": list(map(str, roots)),
                           "readonly": list(map(str, readonly)),
                           "payload": list(map(str, payload)), "environment": environment})
        self.record()
        try:
            result = self.runner(command, cwd=cwd, env={}, timeout=timeout + 30)
        except (subprocess.SubprocessError, OSError) as exc:
            self.calls[-1]["failed"] = str(exc)
            self.calls[-1]["stdout"] = getattr(exc, "stdout", None)
            self.calls[-1]["stderr"] = getattr(exc, "stderr", None)
            self.record()
            raise
        self.calls[-1].update({"returncode": result.returncode,
                                "stdout": result.stdout, "stderr": result.stderr})
        self.record()
        if result.returncode != 0:
            raise RuntimeError("Isolated command failed; no later consumer is permitted")
        return result
