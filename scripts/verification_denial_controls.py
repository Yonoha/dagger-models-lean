"""Native-only required denials; standalone uses NO external proofs/cache.

CLI: --landrun PINNED_CHECKOUT/landrun --output FRESH_DIR --lean-prefix PINNED_PREFIX.
The same Sandbox builder/ABI guard as full verification is used. No mock CLI exists.
"""
import argparse
import ctypes
import errno
import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import sys
from verification_sandbox import Sandbox, native_guard


class Iovec(ctypes.Structure):
    _fields_ = [("base", ctypes.c_void_p), ("length", ctypes.c_size_t)]


def memory_read(pid, address):
    libc = ctypes.CDLL(None, use_errno=True)
    data = ctypes.create_string_buffer(1)
    local = Iovec(ctypes.cast(data, ctypes.c_void_p), 1)
    remote = Iovec(address, 1)
    result = libc.process_vm_readv(pid, ctypes.byref(local), 1,
                                 ctypes.byref(remote), 1, 0)
    if result < 0:
        raise OSError(ctypes.get_errno(), "process_vm_readv")
    return data.raw


def helper():
    # A disposable harmless target. Explicit permission makes the outside positive
    # check meaningful; sandbox readv must then fail due to the enforced policy.
    libc = ctypes.CDLL(None, use_errno=True)
    if libc.prctl(0x59616d61, ctypes.c_ulong(-1), 0, 0, 0) != 0:  # PR_SET_PTRACER_ANY
        raise RuntimeError("Could not prepare disposable native debug control")
    value = ctypes.create_string_buffer(b"x")
    print(json.dumps({"pid": os.getpid(), "address": ctypes.addressof(value)}), flush=True)
    while True:
        signal.pause()


def probe(config):
    d = json.loads(Path(config).read_text())
    if os.geteuid() == 0:
        raise RuntimeError("Native probe payload must be nonroot")
    statuses = []

    def denied(label, operation):
        try:
            operation()
        except OSError as exc:
            if exc.errno not in {errno.EACCES, errno.EPERM, errno.EROFS}:
                raise
            statuses.append({"label": label, "errno": exc.errno})
        else:
            raise RuntimeError("REQUIRED_DENIAL_MISSING: " + label)

    for label, name in d["protected"].items():
        path = Path(name)
        # No bytes are written even if a boundary is unexpectedly absent.
        def open_write():
            fd = os.open(path, os.O_WRONLY)
            os.close(fd)
        denied("write:" + label, open_write)
        # Same-mode chmod is harmless but must be EROFS under the mount boundary.
        denied("metadata:" + label, lambda: os.chmod(path, path.stat().st_mode & 0o777))
    for family in [socket.AF_INET, socket.AF_INET6, socket.AF_UNIX]:
        for kind in [socket.SOCK_STREAM, socket.SOCK_DGRAM]:
            def create_socket():
                with socket.socket(family, kind):
                    pass
            denied(f"socket:{family}:{kind}", create_socket)
    denied("external-signal", lambda: os.kill(d["target"]["pid"], signal.SIGCONT))
    denied("external-debug-readv", lambda: memory_read(**d["target"]))
    status = Path('/proc/self/status').read_text()
    if "NoNewPrivs:\t1" not in status or "CapEff:\t0000000000000000" not in status:
        raise RuntimeError("Privilege boundary absent")
    positive = Path(d["writable"]) / "native-positive.txt"
    positive.write_text("dedicated-output-write-allowed\n")
    if positive.read_text() != "dedicated-output-write-allowed\n":
        raise RuntimeError("Native positive output check failed")
    print("NATIVE_REQUIRED_DENIALS_PASS " + json.dumps(statuses), flush=True)


def python_denials(sandbox, root, writable, protected):
    process = subprocess.Popen([str(sandbox.python), str(Path(__file__).resolve()), "--helper"],
                               stdout=subprocess.PIPE, text=True)
    try:
        target = json.loads(process.stdout.readline())
        if memory_read(**target) != b"x":
            raise RuntimeError("Outside positive debug control failed")
        os.kill(target["pid"], signal.SIGCONT)
        config = Path(root) / "native-denial-inputs.json"
        config.write_text(json.dumps({"protected": {k: str(v) for k, v in protected.items()},
                                      "target": target, "writable": str(writable)}))
        result = sandbox.run([str(sandbox.python), str(Path(__file__).resolve()),
                              "--probe", str(config)], cwd=root, writable=[writable])
        if "NATIVE_REQUIRED_DENIALS_PASS " not in result.stdout:
            raise RuntimeError("Native denials did not run or failed")
        return result.stdout
    finally:
        process.terminate()
        process.wait(timeout=10)


def lean_denials(sandbox, root, writable, protected_file, lean_path, *, import_only=False):
    root, writable = Path(root), Path(writable)
    source_dir = root / "native-control-sources"
    artifacts = root / "native-control-artifacts"
    if not import_only:
        source_dir.mkdir()
        mutable = writable / "native-control-artifacts"
        mutable.mkdir()
        path = json.dumps(str(protected_file))
        body = f'''import Lean
open Lean Elab Command
run_cmd do
  let denied ← liftIO <| try
    let _ ← IO.FS.Handle.mk {path} .append
    pure false
  catch _ => pure true
  unless denied do throwError "ELAB_WRITE_BOUNDARY_MISSING"
  logInfo "LEAN_ELAB_DENIAL_PASS"
initialize do
  if (← IO.getEnv "DAGGER_VERIFY_ARTIFACT_PROBE") == some "1" then
    let denied ← try
      let _ ← IO.FS.Handle.mk {path} .append
      pure false
    catch _ => pure true
    unless denied do throw <| IO.userError "ARTIFACT_WRITE_BOUNDARY_MISSING"
    IO.println "LEAN_ARTIFACT_IMPORT_DENIAL_PASS"
'''
        source = source_dir / "NativeBoundaryArtifact.lean"
        source.write_text(body)
        result = sandbox.run([str(sandbox.prefix / "bin/lean"), "-DwarningAsError=true",
                              "-R", str(source_dir), "-o", str(mutable / "NativeBoundaryArtifact.olean"),
                              str(source)], cwd=root, writable=[writable],
                             extra_env={"LEAN_PATH": lean_path})
        if "LEAN_ELAB_DENIAL_PASS" not in result.stdout + result.stderr:
            raise RuntimeError("Lean elaboration denial did not run")
        import shutil
        shutil.copytree(mutable, artifacts, symlinks=False)  # data only, before candidate execution
        (source_dir / "NativeBoundaryImport.lean").write_text("import NativeBoundaryArtifact\n")
    result = sandbox.run([str(sandbox.prefix / "bin/lean"), "-DwarningAsError=true",
                          str(source_dir / "NativeBoundaryImport.lean")], cwd=root,
                         writable=[writable], extra_env={"LEAN_PATH": str(artifacts) + ":" + lean_path,
                                                       "DAGGER_VERIFY_ARTIFACT_PROBE": "1"})
    if "LEAN_ARTIFACT_IMPORT_DENIAL_PASS" not in result.stdout + result.stderr:
        raise RuntimeError("Serialized-artifact denial did not run; no silent skip")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--landrun", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--lean-prefix", type=Path)
    parser.add_argument("--probe", type=Path)
    parser.add_argument("--helper", action="store_true")
    args = parser.parse_args()
    if args.helper:
        return helper()
    if args.probe:
        return probe(args.probe)
    if not args.landrun or not args.output or not args.lean_prefix:
        parser.error("standalone requires --landrun, --output, --lean-prefix")
    info = native_guard(args.landrun)  # must run BEFORE creating a fixture or native payload
    version = subprocess.run([str(args.lean_prefix / "bin/lean"), "--version"],
                             check=True, capture_output=True, text=True).stdout
    if "version 4.27.0" not in version:
        raise ValueError("Standalone probe requires the unchanged Lean 4.27.0 toolchain")
    root = args.output.resolve()
    if root.exists():
        raise ValueError("Standalone native output must be fresh")
    root.mkdir(parents=True)
    writable = root / "outputs"
    writable.mkdir()
    protected = {}
    for label in ["Audit", "collector-source", "collector-artifact", "metadata", "trusted-cache"]:
        f = root / (label + ".sentinel")
        f.write_text("HARMLESS_BOUNDARY_SENTINEL_NOT_A_LEAN_ARTIFACT\n")
        protected[label] = f
    sandbox = Sandbox(args.landrun, args.lean_prefix, sys.executable, info,
                      log_file=root / "isolation-command-history.json", readonly=[root])
    protected["interpreter"] = sandbox.python
    protected["toolchain"] = args.lean_prefix / "bin/lean"
    py = python_denials(sandbox, root, writable, protected)
    lean = lean_denials(sandbox, root, writable, protected["Audit"],
                        str(args.lean_prefix / "lib/lean"))
    (root / "native-results.json").write_text(json.dumps({"native_preflight": info,
        "python_denials": py, "lean_elaboration_and_import_denials": lean,
        "same_production_builder": True, "calls": sandbox.calls,
        "external_or_candidate_proofs_or_mathlib_cache": False}, indent=2) + "\n")
    print("STANDALONE_NATIVE_ISOLATION_CONTROLS_PASS")


if __name__ == "__main__":
    main()
