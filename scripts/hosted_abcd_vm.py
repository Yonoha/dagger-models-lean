#!/usr/bin/env python3
"""Prepared single-command hosted current A/B/C/D CI; not yet VM-tested.

Run only from the trusted control checkout on a fresh GitHub-hosted Ubuntu
24.04 x64 job after pinned checkouts, setup-go, and lean-action. Candidate
checkout is data only. The scripts are installed; the workflow remains a preparation file until runtime verification.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import socket
import stat
import subprocess
import sys
import tempfile
import time
from urllib.request import Request, urlopen

from verify_debian_image import BUILD, IMAGE, extract_checked


HERE = Path(__file__).resolve().parent
DEBIAN_URL = "https://cloud.debian.org/images/cloud/trixie/" + BUILD + "/"
LANDRUN_COMMIT = "811cfff51ceaf3d9843708aa6d22e9b84ccac8b4"
EXPORTER_COMMIT = "bd93e5ed12fbeea19f39ec3ead659c293b2b8a95"
GUEST_KERNEL = "linux-image-7.2.6+deb13-cloud-amd64=7.2.6-1~bpo13+1"
GUEST_LINUX_BASE = "linux-base=4.17~bpo13+1"
CURRENT_GRAPH_SHA = "0a3af50bbf1dbb6ae6ddd5b679cb6d0120306c3f3d34777bc358cfd84859943f"
OLD_ASSET_SHA = "21111525e8bc72f2c40051f5ce13788beb94ca39c1e4e9daca739d8540f576b3"
CURRENT_AUDIT_SHA = "c513a930965ed19cc6d757276b6d83675eb44992bc87c1bcaefcd8ae3365db03"
CURRENT_INVENTORY_SHA = {
    "owners": "149da9a29e3cd8535e14acdb9e0c487c7692d4191fd5e9db97c03e1bee273aa2",
    "advertised": "1c8b6763d2dfef7e29d8c2142f7a07d919a7340ef9e77efa33c98c97ec0806eb",
    "main_results": "972cb0bee03545626e32f817aefb8a84603982f2a8e507c9ae57da01d9219b5b",
}
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*")


def run(*cmd: str, cwd: Path | None = None, stdout=None, input=None,
        check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, cwd=cwd, stdout=stdout, input=input,
                          check=check)


def require_dir(path: Path) -> Path:
    if not path.is_absolute() or path.is_symlink() or not path.is_dir():
        raise ValueError(f"required directory missing or symlinked: {path}")
    return path


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def bytes_free(path: Path) -> int:
    free = shutil.disk_usage(path).free
    print(f"HOST_DISK_FREE path={path} bytes={free}", flush=True)
    return free


def require_free(path: Path, gib: int) -> None:
    if bytes_free(path) < gib * 1024**3:
        raise RuntimeError(f"host disk has less than {gib} GiB free")


def download(url: str, output: Path) -> None:
    if output.exists():
        raise ValueError(f"download output already exists: {output}")
    with urlopen(Request(url, headers={"User-Agent": "dagger-bcd-hosted-vm/1"}),
                 timeout=120) as response, output.open("xb") as dest:
        shutil.copyfileobj(response, dest, 1024 * 1024)


def git_commit(checkout: Path, expected: str) -> None:
    actual = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
    if actual != expected:
        raise ValueError(f"checkout commit mismatch: {checkout}: expected {expected}, got {actual}")


def full_revision(value: str) -> str:
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise argparse.ArgumentTypeError("revision must be a full lowercase SHA-1")
    return value


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--control-revision", type=full_revision, required=True)
    parser.add_argument("--source-revision", type=full_revision, required=True)
    return parser.parse_args(argv)


def verify_checkout_revisions(workspace: Path, control_revision: str,
                              source_revision: str) -> None:
    git_commit(workspace / "control", control_revision)
    git_commit(workspace / "candidate", source_revision)


def host_receipt(control_revision: str, source_revision: str,
                 result_path: Path, audit_path: Path,
                 restored_audit_path: Path) -> dict:
    if restored_audit_path.read_bytes() != audit_path.read_bytes():
        raise RuntimeError("restored owner-audit bytes differ before host receipt")
    return {"kind": "HOSTED_CURRENT_ABCD_VM_CI_RECEIPT",
            "control_revision": control_revision,
            "candidate_source_revision": source_revision,
            "guest_result_sha256": sha256(result_path),
            "owner_audit_log_sha256": sha256(audit_path),
            "restored_owner_audit_log_sha256": sha256(restored_audit_path),
            "restored_owner_audit_byte_identical": True,
            "retained_comparator_cases": 9,
            "A_comparator_cases": 5,
            "owner_audit_negative_controls": 4,
            "owner_audit_modules": 2771,
            "owner_audit_metadata_results": 71,
            "owner_audit_main_results": 8,
            "metadata_current_passed": True,
            "A_Comparator_passed": True,
            "ABCD_aggregate_certificate_passed": True,
            "Linux_CI_passed": True}


def stage_candidate_data(candidate: Path, a_asset: Path,
                         output: Path) -> None:
    """Expose exactly the current graph's checked regular sources as data."""
    graph_path = a_asset / "current-source/source-graph.json"
    if sha256(graph_path) != CURRENT_GRAPH_SHA:
        raise ValueError("trusted source graph SHA mismatch before staging")
    graph = json.loads(graph_path.read_text())
    rows = graph["local_source_modules"]
    names = [row["module"] for row in rows]
    if (graph.get("local_module_count") != 2771 or len(names) != 2771 or
            len(set(names)) != 2771 or any(not MODULE_NAME.fullmatch(name) for name in names) or
            graph.get("roots") != ["DaggerModels", "MainTheoremsABCD"] or
            graph.get("unresolved_nonstandard_imports") or
            len(graph.get("topological_order", [])) != 2771 or
            set(graph["topological_order"]) != set(names)):
        raise ValueError("trusted graph has unexpected candidate source set")
    if output.exists():
        raise ValueError("candidate data output must be fresh")
    output.mkdir()
    hashes = {}
    for row in rows:
        name = row["module"]
        rel = Path(row["path"])
        if (rel.is_absolute() or ".." in rel.parts or
                rel != Path(*name.split(".")).with_suffix(".lean") or
                not re.fullmatch(r"[0-9a-f]{64}", row.get("sha256", "")) or
                type(row.get("bytes")) is not int or row["bytes"] <= 0):
            raise ValueError(f"unsafe current source graph row: {name}")
        source = candidate
        for part in rel.parts:
            source = source / part
            if source.is_symlink():
                raise ValueError(f"candidate source symlink: {source}")
        if not stat.S_ISREG(source.stat(follow_symlinks=False).st_mode):
            raise ValueError(f"candidate source is not regular: {source}")
        if source.stat().st_size != row["bytes"] or sha256(source) != row["sha256"]:
            raise ValueError(f"candidate source bytes/hash differ: {source}")
        target = output / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        if target.stat().st_size != row["bytes"] or sha256(target) != row["sha256"]:
            raise ValueError(f"staged current source bytes/hash differ: {target}")
        hashes[name] = sha256(target)
    (output.parent / "bcd-candidate-hashes.json").write_text(
        json.dumps(hashes, sort_keys=True, indent=2) + "\n")
    print(f"CANDIDATE_DATA_STAGED regular_modules={len(names)}", flush=True)


def choose_loopback_port() -> int:
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


class Guest:
    def __init__(self, port: int, key: Path, known_hosts: Path,
                 qemu: subprocess.Popen, temp: Path):
        self.port, self.qemu, self.temp = port, qemu, temp
        self.ssh_base = ["ssh", "-T", "-p", str(port), "-i", str(key),
                         "-o", "BatchMode=yes", "-o", "IdentitiesOnly=yes",
                         "-o", "PasswordAuthentication=no",
                         "-o", "StrictHostKeyChecking=accept-new",
                         "-o", f"UserKnownHostsFile={known_hosts}",
                         "-o", "ConnectTimeout=5", "-o", "LogLevel=ERROR",
                         "runner@127.0.0.1"]

    def command(self, command: str, *, input: bytes | None = None,
                capture: bool = False, check: bool = True):
        return subprocess.run(self.ssh_base + [command], input=input,
                              stdout=subprocess.PIPE if capture else None,
                              stderr=subprocess.PIPE if capture else None,
                              check=check)

    def wait_for_ssh(self, timeout: int = 240) -> None:
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if self.qemu.poll() is not None:
                raise RuntimeError(f"QEMU exited ({self.qemu.returncode}); see {self.temp/'qemu.log'}")
            result = self.command("/bin/true", capture=True, check=False)
            if result.returncode == 0:
                return
            time.sleep(2)
        raise TimeoutError("guest SSH never became ready")

    def reboot_and_wait(self) -> None:
        old = self.command("cat /proc/sys/kernel/random/boot_id", capture=True).stdout.strip()
        # SSH may return 255 when systemd closes the connection for reboot.
        self.command("sudo systemctl reboot", capture=True, check=False)
        deadline = time.monotonic() + 240
        while time.monotonic() < deadline:
            if self.qemu.poll() is not None:
                raise RuntimeError("QEMU exited during guest reboot")
            result = self.command("cat /proc/sys/kernel/random/boot_id",
                                  capture=True, check=False)
            if result.returncode == 0 and result.stdout.strip() != old:
                return
            time.sleep(2)
        raise TimeoutError("guest did not boot a new kernel")

    def stream_script(self, script: Path, command: str, host_temp: Path) -> None:
        with script.open("rb") as stream:
            proc = subprocess.Popen(self.ssh_base + [command], stdin=stream)
            try:
                while proc.poll() is None:
                    if self.qemu.poll() is not None:
                        raise RuntimeError("QEMU exited while source runner was active")
                    if bytes_free(host_temp) < 1024**3:
                        raise RuntimeError("host disk fell below 1 GiB; fail closed")
                    time.sleep(20)
                if proc.returncode != 0:
                    raise subprocess.CalledProcessError(proc.returncode, command)
            finally:
                if proc.poll() is None:
                    proc.terminate()
                    try:
                        proc.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        proc.kill()
                        proc.wait()

    def copy_output(self, remote: Path, local: Path) -> None:
        if local.exists():
            raise ValueError(f"host output already exists: {local}")
        with local.open("xb") as out:
            result = self.command("cat " + shlex.quote(str(remote)),
                                  capture=True, check=False)
            if result.returncode != 0:
                local.unlink(missing_ok=True)
                raise RuntimeError(f"guest output missing: {remote}")
            out.write(result.stdout)
        if local.stat().st_size == 0:
            raise ValueError(f"empty guest result: {remote}")


def prepare_host_tools(workspace: Path, temp: Path) -> None:
    control = workspace / "control"
    asset = temp / "bcd-trusted"
    a_asset = temp / "a-trusted"
    landrun = workspace / "landrun"
    exporter = workspace / "lean4export-legacy"
    git_commit(landrun, LANDRUN_COMMIT)
    git_commit(exporter, EXPORTER_COMMIT)
    run("go", "build", "-o", "landrun", "cmd/landrun/main.go", cwd=landrun)
    print("HOST_LANDRUN_BUILT", flush=True)
    require_free(temp, 5)
    if (sha256(a_asset / "current-audit/TrustedABCDAudit.lean") != CURRENT_AUDIT_SHA or
            sha256(a_asset / "pins/lean-toolchain") !=
            sha256(asset / "pins/lean-toolchain")):
        raise ValueError("current auditor or shared Lean toolchain pin differs")
    run(sys.executable, str(control / "scripts/prepare_abcd_auditor.py"),
        "--source", str(a_asset / "current-audit/TrustedABCDAudit.lean"),
        "--source-sha256", CURRENT_AUDIT_SHA,
        "--toolchain", str(a_asset / "pins/lean-toolchain"),
        "--output", str(temp / "bcd-auditor"))
    run("lake", "build", "bcdTrustedAudit", cwd=temp / "bcd-auditor")
    print("HOST_AUDITOR_BUILT", flush=True)
    require_free(temp, 5)
    run("lake", "build", "lean4export", cwd=exporter)
    print("HOST_EXPORTER_BUILT", flush=True)
    require_free(temp, 4)
    # Resolve Elan in the trusted checkout, where the pinned lean-toolchain
    # exists. The replay preparation runs outside that directory and must not
    # depend on an Elan default toolchain being configured on the runner.
    replay_lean = subprocess.check_output(
        ["elan", "which", "lean"], cwd=control, text=True).strip()
    if not Path(replay_lean).is_absolute() or not Path(replay_lean).is_file():
        raise ValueError("pinned replay Lean executable is unavailable")
    run(sys.executable,
        str(asset / "comparator-certificates/replay_certificates.py"),
        "--prepare-only", "--lean", replay_lean,
        cwd=workspace)
    print("HOST_OFFICIAL_REPLAY_FRONTEND_BUILT", flush=True)
    require_free(temp, 4)


def make_seed(temp: Path, uid: int) -> tuple[Path, Path, Path]:
    private = temp / "id_ed25519"
    public = temp / "id_ed25519.pub"
    known = temp / "known_hosts"
    run("ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", str(private))
    os.chmod(private, 0o600)
    key = public.read_text().strip()
    # Public key only. Never print or export the private key.
    (temp / "user-data").write_text(
        "#cloud-config\n"
        "disable_root: true\nssh_pwauth: false\n"
        "users:\n  - default\n  - name: runner\n"
        f"    uid: {uid}\n"
        "    shell: /bin/bash\n    groups: [sudo]\n"
        "    lock_passwd: true\n"
        "    sudo: ALL=(ALL) NOPASSWD:ALL\n"
        "    ssh_authorized_keys:\n"
        f"      - {key}\n")
    (temp / "meta-data").write_text(
        f"instance-id: bcd-ci-{os.urandom(16).hex()}\n"
        "local-hostname: bcd-ci-guest\n")
    seed = temp / "seed.iso"
    run("cloud-localds", str(seed), str(temp / "user-data"),
        str(temp / "meta-data"))
    return seed, private, known


def validate_guest_result(result: dict, *, source_revision: str, lock: dict,
                          a_lock: dict, candidate_hashes_sha256: str,
                          audit_log_sha256: str, audit_report: dict,
                          restored_audit_log_sha256: str,
                          restored_audit_report: dict) -> None:
    """Require all current-source gates before metadata checks and host receipt.

    Both audit JSON files are copied from the guest and must be byte-identical.
    Metadata validation still independently checks all 71 roots.
    """
    required_main = {
        "DaggerActualMainTheoremBProof.verified",
        "DaggerProofOriginalMainTheoremC.verified",
        "ProofActualMainTheoremD.verified",
        "DaggerComparator.mainB", "DaggerComparator.originalMainTheoremC",
        "DaggerComparator.mainD", "DaggerTheoremAProof.verified",
        "DaggerComparator.mainA",
    }
    owners = audit_report.get("owned_modules")
    main_roots = audit_report.get("main_results")
    advertised = audit_report.get("declarations")
    if (not isinstance(owners, list) or len(owners) != 2771 or
            len(set(owners)) != 2771 or
            not isinstance(main_roots, dict) or set(main_roots) != required_main or
            not isinstance(advertised, dict) or len(advertised) != 71 or
            not {"DaggerComparator.mainA", "DaggerComparator.mainB",
                 "DaggerComparator.originalMainTheoremC", "DaggerComparator.mainD"}
                <= set(advertised)):
        raise RuntimeError("copied current audit lacks 2771 owners, 71 advertised or 8 main roots")
    expected_cases = {
        "control-Solution": 0, "control-Mismatch": 1,
        "control-ForbiddenAxiom": 1, "control-ChangedDefinition-unchanged": 0,
        "control-ChangedDefinition": 1, "C-universe-zero-saved": 0,
        "B": 0, "C-generic-public": 0, "D": 0,
    }
    expected_audit_negatives = {
        "proof-hole", "unused-public-extra-axiom",
        "external-transitive-axiom", "initializer-spoof",
    }
    a_extension = result.get("A_additive_extension", {})
    a_rows = a_extension.get("results", []) if isinstance(a_extension, dict) else []
    expected_a_cases = {
        "A-normal-control": 0, "A-positive": 0,
        "A-weakened-True-negative": 1, "A-extra-axiom-negative": 1,
        "A-changed-leftProper-negative": 1,
    }
    positive = ["Running Lean default kernel on solution.",
                "Lean default kernel accepts the solution",
                "OFFICIAL_COMPARATOR_VERIFYMATCH_AND_KERNEL_REPLAY_PASSED"]
    expected_a_lines = {
        "A-normal-control": positive,
        "A-positive": positive,
        "A-weakened-True-negative": [
            "uncaught exception: Challenge and solution theorem statement do not match: 'DaggerComparator.mainA'"],
        "A-extra-axiom-negative": [
            "uncaught exception: Illegal axiom detected: 'DaggerComparator.AExtraAxiom'"],
        "A-changed-leftProper-negative": [
            "uncaught exception: Const does not match between challenge and target 'DaggerTheoremAChallenge.leftProper'"],
    }
    if (result.get("kind") != "CURRENT_2771_ABCD_LINUX_COMPARATOR_RESULT" or
            result.get("source_profile") != "current-2771" or
            result.get("A_Comparator_passed") is not True or
            result.get("ABCD_aggregate_certificate_passed") is not True or
            result.get("A_Comparator_extension_required") is not False or
            result.get("current_source_BCD_checks") is not True or
            result.get("candidate_source_revision") != source_revision or
            result.get("trusted_asset_sha256") != OLD_ASSET_SHA or
            result.get("graph_sha256") != CURRENT_GRAPH_SHA or
            result.get("auditor_source_sha256") != CURRENT_AUDIT_SHA or
            result.get("audit_inventory_sha256") != CURRENT_INVENTORY_SHA or
            {row.get("case") for row in result.get("results", [])} != set(expected_cases) or
            len(result.get("results", [])) != len(expected_cases) or
            any(type(row.get("exit")) is not int or
                type(row.get("expected_exit")) is not int or
                row.get("exit") != expected_cases.get(row.get("case")) or
                row.get("expected_exit") != expected_cases.get(row.get("case"))
                for row in result.get("results", [])) or
            {row.get("case") for row in result.get("owner_audit_negative_controls", [])} != expected_audit_negatives or
            len(result.get("owner_audit_negative_controls", [])) != 4 or
            any(type(row.get("exit")) is not int or row["exit"] == 0
                for row in result.get("owner_audit_negative_controls", [])) or
            result.get("candidate_source_modules") != 2771 or
            result.get("candidate_source_hashes_sha256") != candidate_hashes_sha256 or
            result.get("owner_audit", {}).get("metadata_result_count") != 71 or
            a_extension.get("manifest_sha256") != a_lock["manifest_sha256"] or
            a_extension.get("full_2771_source_and_olean_hashes_restored") is not True or
            len(a_extension.get("compiled_external_fixtures", [])) != 6 or
            len(a_extension.get("exports", [])) != 5 or
            len(a_rows) != 5 or
            {row.get("case") for row in a_rows} != set(expected_a_cases) or
            any(type(row.get("exit")) is not int or
                type(row.get("expected_exit")) is not int or
                row.get("exit") != expected_a_cases.get(row.get("case")) or
                row.get("expected_exit") != expected_a_cases.get(row.get("case")) or
                row.get("expected_lines") != expected_a_lines.get(row.get("case"))
                for row in a_rows) or
            result.get("generic_c_extension", {}).get("case") != "C-generic-public" or
            result.get("generic_c_extension", {}).get("guard_result_sha256") != lock["verified_local_content_sha256"]["c-universe-extension/closure-guard-result.json"] or
            result.get("tool_commits", {}).get("landrun") != LANDRUN_COMMIT or
            result.get("tool_commits", {}).get("legacy_exporter") != EXPORTER_COMMIT):
        raise RuntimeError("guest current A/B/C/D result summary is incomplete")
    if result.get("landlock_write_denial_probe_passed") is not True:
        raise RuntimeError("Landrun write-denial probe missing")
    if audit_log_sha256 != result.get("owner_audit", {}).get("log_sha256"):
        raise RuntimeError("copied owner-audit log differs from guest result")
    restored_receipt = result.get("owner_audit_restored")
    if (restored_audit_log_sha256 != audit_log_sha256 or
            restored_audit_report != audit_report or
            not isinstance(restored_receipt, dict) or
            set(restored_receipt) != {"log_sha256", "byte_identical_to_initial"} or
            restored_receipt.get("log_sha256") != restored_audit_log_sha256 or
            restored_receipt.get("byte_identical_to_initial") is not True):
        raise RuntimeError("restored owner-audit report differs from initial positive")


def main() -> None:
    a = parse_args()
    workspace = require_dir(Path(os.environ["GITHUB_WORKSPACE"]))
    runner_temp = require_dir(Path(os.environ["RUNNER_TEMP"]))
    with open("/proc/meminfo") as meminfo:
        first = meminfo.readline().split()
    if first[:1] != ["MemTotal:"] or int(first[1]) * 1024 < 14 * 1024**3:
        raise RuntimeError("hosted x64 job needs at least 14 GiB host RAM")
    if Path.home() != Path("/home/runner"):
        raise RuntimeError("expected hosted runner HOME /home/runner for guest path alignment")
    if os.getuid() < 1001:
        raise RuntimeError("host runner UID may collide with Debian default user")
    for name in ("control", "candidate", "landrun", "lean4export-legacy"):
        require_dir(workspace / name)
    verify_checkout_revisions(workspace, a.control_revision, a.source_revision)
    control = workspace / "control"
    lock_path = control / ".ci/bcd/asset-lock.json"
    lock = json.loads(lock_path.read_text())
    a_lock_path = control / ".ci/a/asset-lock.json"
    a_lock = json.loads(a_lock_path.read_text())
    if (lock.get("published_archive_sha256") != OLD_ASSET_SHA or
            a_lock.get("old_BCD_asset_dependency_sha256") != OLD_ASSET_SHA or
            a_lock.get("expected_source_graph_sha256") != CURRENT_GRAPH_SHA):
        raise ValueError("old BCD/A independent trusted lock dependency differs")
    asset = runner_temp / "bcd-trusted"
    a_asset = runner_temp / "a-trusted"
    # Both public URLs/hashes must be pinned before any large tool/image work.
    # The hosted workflow never passes --archive; null A URL fails closed.
    run(sys.executable, str(control / "scripts/fetch_a_assets.py"),
        "--lock", str(a_lock_path), "--output", str(a_asset), "--preflight-only")
    run(sys.executable, str(control / "scripts/fetch_bcd_assets.py"),
        "--lock", str(lock_path), "--output", str(asset), "--preflight-only")
    run("bash", str(HERE / "host_prereq.sh"))
    require_free(runner_temp, 10)
    run("sudo", "env", "DEBIAN_FRONTEND=noninteractive", "apt-get", "update")
    run("sudo", "env", "DEBIAN_FRONTEND=noninteractive", "apt-get", "install",
        "-y", "--no-install-recommends", "qemu-system-x86", "qemu-utils",
        "cloud-image-utils")
    for name in ("qemu-system-x86_64", "qemu-img", "cloud-localds", "ssh"):
        if not shutil.which(name):
            raise RuntimeError(f"host tool missing: {name}")
    print("RUNNER_IMAGE_VERSION " + os.environ.get("ImageVersion", "unknown"), flush=True)
    run("qemu-system-x86_64", "--version")
    run("qemu-img", "--version")
    run(sys.executable, str(control / "scripts/fetch_bcd_assets.py"),
        "--lock", str(lock_path), "--output", str(asset))
    run(sys.executable, str(control / "scripts/fetch_a_assets.py"),
        "--lock", str(a_lock_path), "--output", str(a_asset))
    # The fetcher adds a verified receipt outside its locked payload set;
    # retain it separately so the source runner's exact A-file-set gate holds.
    receipt_file = a_asset / "fetch-receipt.json"
    receipt = json.loads(receipt_file.read_text())
    if (receipt.get("kind") != "A_ADDITIVE_TRUSTED_INPUTS_FETCHED_NOT_LINUX_ACCEPTANCE" or
            receipt.get("archive_sha256") != a_lock["published_archive_sha256"] or
            receipt.get("manifest_sha256") != a_lock["manifest_sha256"] or
            receipt.get("source_graph_sha256") != CURRENT_GRAPH_SHA or
            receipt.get("old_BCD_asset_dependency_sha256") != OLD_ASSET_SHA or
            receipt.get("Linux_CI_passed") is not False or
            receipt.get("publication_performed") is not False):
        raise ValueError("A fetch receipt differs")
    os.replace(receipt_file, runner_temp / "a-fetch-receipt.json")
    candidate_data = runner_temp / "bcd-candidate-data"
    stage_candidate_data(workspace / "candidate", a_asset, candidate_data)
    prepare_host_tools(workspace, runner_temp)

    with tempfile.TemporaryDirectory(prefix="bcd-hosted-vm-", dir=runner_temp) as d:
        vm = Path(d)
        require_free(runner_temp, 8)
        archive = vm / (IMAGE + ".tar.xz")
        sums = vm / "SHA512SUMS"
        download(DEBIAN_URL + "SHA512SUMS", sums)
        download(DEBIAN_URL + archive.name, archive)
        raw = vm / "guest.raw"
        image_record = extract_checked(archive, sums, raw)
        print("DEBIAN_IMAGE_VERIFIED " + json.dumps(image_record, sort_keys=True), flush=True)
        archive.unlink()
        require_free(runner_temp, 6)
        run("qemu-img", "resize", "-f", "raw", str(raw), "32G")
        seed, private, known = make_seed(vm, os.getuid())
        port = choose_loopback_port()
        shares = [
            ("bcdcontrol", workspace / "control"),
            ("bcdcandidate", candidate_data),
            ("bcdasset", asset),
            ("bcdassetA", a_asset),
            ("bcdlandrun", workspace / "landrun"),
            ("bcdexporter", workspace / "lean4export-legacy"),
            ("bcdauditor", runner_temp / "bcd-auditor"),
            ("bcdeelan", Path.home() / ".elan"),
        ]
        for _, path in shares:
            require_dir(path)
            if "," in str(path):
                raise ValueError("QEMU 9p export path contains comma")
        qemu_cmd = [
            "qemu-system-x86_64", "-machine", "q35", "-accel", "kvm",
            "-cpu", "host",
            "-smp", "3", "-m", "10240", "-display", "none",
            "-serial", f"file:{vm/'serial.log'}", "-monitor", "none",
            "-drive", f"file={raw},format=raw,if=virtio",
            "-drive", f"file={seed},media=cdrom,readonly=on",
            "-netdev", f"user,id=net0,hostfwd=tcp:127.0.0.1:{port}-:22",
            "-device", "virtio-net-pci,netdev=net0",
            "-device", "virtio-rng-pci",
        ]
        for tag, path in shares:
            qemu_cmd += ["-virtfs", f"local,path={path},mount_tag={tag},"
                         "security_model=none,readonly=on"]
        with (vm / "qemu.log").open("wb") as qemu_log:
            qemu_env = {key: os.environ[key] for key in ("PATH", "HOME", "LANG")
                        if key in os.environ}
            qemu = subprocess.Popen(qemu_cmd, stdout=qemu_log,
                                    stderr=subprocess.STDOUT, env=qemu_env)
            guest = Guest(port, private, known, qemu, vm)
            failed = False
            try:
                guest.wait_for_ssh()
                guest.command("sudo cloud-init status --wait")
                snapshot_gate = guest.command(
                    "python3 -", input=(HERE / "guest_snapshot_gate.py").read_bytes(),
                    capture=True, check=False)
                print(snapshot_gate.stdout.decode(), end="", flush=True)
                if snapshot_gate.returncode != 0:
                    print(snapshot_gate.stderr.decode(), file=sys.stderr)
                    raise RuntimeError("fixed Debian snapshot index gate failed")
                apt = (
                    "set -euo pipefail; "
                    "printf '%s\\n' 'deb [signed-by=/usr/share/keyrings/debian-archive-keyring.gpg check-valid-until=no] "
                    "https://snapshot.debian.org/archive/debian/20261018/ trixie-backports main' | "
                    "sudo tee /etc/apt/sources.list.d/bcd-backports.list >/dev/null; "
                    "sudo env DEBIAN_FRONTEND=noninteractive apt-get update; "
                    "sudo env DEBIAN_FRONTEND=noninteractive apt-get install -y "
                    "--no-install-recommends git python3 python3-venv ca-certificates "
                    "build-essential libgmp10 libtinfo6 libzstd1 dbus-user-session "
                    # Backports have priority 100: explicitly select the base
                    # package required by this kernel instead of upgrading all
                    # guest packages from backports.
                    + shlex.quote(GUEST_KERNEL) + " " + shlex.quote(GUEST_LINUX_BASE)
                )
                guest.command("bash -lc " + shlex.quote(apt))
                guest.reboot_and_wait()
                kernel_gate = guest.command(
                    "python3 -", input=(HERE / "guest_kernel_gate.py").read_bytes(),
                    capture=True, check=False)
                print(kernel_gate.stdout.decode(), end="", flush=True)
                if kernel_gate.returncode != 0:
                    print(kernel_gate.stderr.decode(), file=sys.stderr)
                    raise RuntimeError("guest exact kernel or ABI 9 gate failed")
                env = {
                    "GITHUB_WORKSPACE": str(workspace),
                    "RUNNER_TEMP": str(runner_temp),
                    "BCD_SOURCE_REVISION": a.source_revision,
                    "MATHLIB_NO_CACHE_ON_UPDATE": "1",
                }
                assignment = " ".join(k + "=" + shlex.quote(v) for k, v in env.items())
                guest.stream_script(HERE / "guest_abcd_run.sh",
                                    assignment + " /bin/bash -s", runner_temp)
                output = runner_temp / "bcd-run"
                output.mkdir()
                guest.copy_output(output / "audit-all-owners.log",
                                  output / "audit-all-owners.log")
                guest.copy_output(output / "audit-restored-owners.log",
                                  output / "audit-restored-owners.log")
                guest.copy_output(output / "ci-candidate-result.json",
                                  output / "ci-candidate-result.json")
            except Exception:
                failed = True
                raise
            finally:
                qemu.terminate()
                try:
                    qemu.wait(timeout=15)
                except subprocess.TimeoutExpired:
                    qemu.kill()
                    qemu.wait()
                if failed:
                    diagnostics = runner_temp / "bcd-vm-diagnostics"
                    diagnostics.mkdir(exist_ok=True)
                    for name in ("qemu.log", "serial.log"):
                        source = vm / name
                        if source.is_file():
                            shutil.copyfile(source, diagnostics / name)

    result_path = runner_temp / "bcd-run/ci-candidate-result.json"
    result = json.loads(result_path.read_text())
    audit_path = runner_temp / "bcd-run/audit-all-owners.log"
    audit_report = json.loads(audit_path.read_text())
    restored_audit_path = runner_temp / "bcd-run/audit-restored-owners.log"
    if restored_audit_path.read_bytes() != audit_path.read_bytes():
        raise RuntimeError("copied restored owner-audit bytes differ")
    restored_audit_report = json.loads(restored_audit_path.read_text())
    validate_guest_result(result, source_revision=a.source_revision,
                          lock=lock, a_lock=a_lock,
                          candidate_hashes_sha256=sha256(runner_temp / "bcd-candidate-hashes.json"),
                          audit_log_sha256=sha256(audit_path), audit_report=audit_report,
                          restored_audit_log_sha256=sha256(restored_audit_path),
                          restored_audit_report=restored_audit_report)
    venv = runner_temp / "bcd-metadata-venv"
    run(sys.executable, "-m", "venv", str(venv))
    vpython = str(venv / "bin/python")
    run(vpython, "-m", "pip", "install", "-r", str(control / ".ci/requirements.txt"))
    run(vpython, str(control / "scripts/check_metadata.py"), "--scope", "current",
        "--candidate-root", str(workspace / "candidate"),
        "--trusted-root", str(control),
        "--axioms", str(runner_temp / "bcd-run/audit-all-owners.log"))
    receipt = host_receipt(a.control_revision, a.source_revision, result_path,
                           audit_path, restored_audit_path)
    (runner_temp / "bcd-run/hosted-ci-receipt.json").write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print("HOSTED_CURRENT_ABCD_VM_CI_PASSED", flush=True)


if __name__ == "__main__":
    main()
