"""reuse the accepted Linux launcher for exactly three cases."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


def completed_build_export_phases(stdout: str, stderr: str) -> bool:
    cursor = 0
    for pattern in (r"^Building Challenge$", r"^Exporting [\s\S]*? from Challenge$",
            r"^Building Solution$", r"^Exporting [\s\S]*? from Solution$"):
        match = re.search(pattern, stdout[cursor:], re.MULTILINE)
        if match is None:
            return False
        cursor += match.end()
    diagnostic = r"\berror(?:\([^\n)]*\))?\s*:|\bwarning\s*:|\bsorryAx\b"
    if re.search(r"\berror(?:\([^\n)]*\))?\s*:", stdout):
        return False
    solution = stdout[stdout.find("Building Solution"):]
    if re.search(diagnostic, solution):
        return False
    for line in stderr.splitlines():
        if re.search(diagnostic, line):
            if "Challenge.lean:" not in line or "warning:" not in line:
                return False
    return "Child exited with" not in stdout + stderr


def preserve_owned_artifacts(project: Path, destination: Path, require_primary: bool) -> list:
    build = project / ".lake/build"
    if (project / ".lake").is_symlink() or build.is_symlink():
        raise RuntimeError("Own output directory may not be a symlink")
    if require_primary:
        for name in ("Challenge", "Solution"):
            primary = build / "lib/lean" / (name + ".olean")
            if (not primary.is_file() or primary.is_symlink()
                    or any(parent.is_symlink() for parent in primary.parents if parent != project)):
                raise RuntimeError(f"Missing regular own primary artifact: {primary}")
    records = []
    for root, dirs, files in os.walk(build, followlinks=False):
        dirs[:] = [d for d in dirs if not (Path(root) / d).is_symlink()]
        for name in sorted(files):
            if not any(name.startswith(role + ".") for role in ("Challenge", "Solution")):
                continue
            source = Path(root) / name
            if source.is_symlink() or not source.is_file():
                raise RuntimeError(f"Own output is not a regular file: {source}")
            relative = source.relative_to(build)
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
            records.append({"path": str(relative), "bytes": target.stat().st_size,
                "sha256": hashlib.sha256(target.read_bytes()).hexdigest()})
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--projects", type=Path, required=True)
    parser.add_argument("--comparator", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args()
    if sys.platform != "linux" or os.geteuid() == 0:
        raise RuntimeError("Run on Linux as an unprivileged user; no fake sandbox is supported")
    landrun = os.environ["COMPARATOR_LANDRUN"]
    exporter = os.environ["COMPARATOR_LEAN4EXPORT"]
    args.evidence.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(args.projects / "prepared-source-bindings.json",
        args.evidence / "prepared-source-bindings.json")
    cases = {
        "weakened-statement": (
            "Challenge and solution theorem statement do not match: "
            "'DaggerModels.LawMarkerPathExample.enrichment_eq'"
        ),
        "changed-definition": (
            "Const does not match between challenge and target "
            "'DaggerModels.LawMarkerPathExample.enrichment'"
        ),
        "positive-law-marker-path": None,
    }
    results = []
    for case, expected_error in cases.items():
        project = (args.projects / case).resolve()
        case_evidence = args.evidence / case
        case_evidence.mkdir()
        record = {"case": case, "state": "PREPARING", "passed": False}
        try:
            for name in ("Challenge.lean", "Solution.lean", "config.json",
                    "lean-toolchain", "lake-manifest.json", "lakefile.lean"):
                shutil.copyfile(project / name, case_evidence / name)
            shutil.copytree(args.projects / "cache/.lake", project / ".lake", symlinks=False)
            command = [
                "systemd-run", "--user", "--quiet", "--wait", "--collect", "--pipe",
                "--property=RestrictAddressFamilies=~AF_UNIX",
                "--property=NoNewPrivileges=yes",
                f"--setenv=PATH={os.environ['PATH']}",
                f"--setenv=COMPARATOR_LANDRUN={landrun}",
                f"--setenv=COMPARATOR_LEAN4EXPORT={exporter}",
                f"--working-directory={project}",
                "lake", "env", str(args.comparator.resolve()), "config.json",
            ]
            (case_evidence / "launch-intent.json").write_text(json.dumps(
                {"case": case, "command": command, "state": "ABOUT_TO_LAUNCH_WRAPPER"}, indent=2) + "\n")
            record.update(command=command, state="ABOUT_TO_LAUNCH_WRAPPER")
            print(f"Running Comparator: {case}", flush=True)
            proc = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            record.update(wrapper_pid=proc.pid)
            (case_evidence / "wrapper-pid.json").write_text(
                json.dumps({"wrapper_pid": proc.pid, "qualification": "systemd-run wrapper, not a Lean PID"}) + "\n")
            try:
                stdout, stderr = proc.communicate(timeout=900)
            except subprocess.TimeoutExpired as error:
                (case_evidence / "stdout.partial.bin").write_bytes(error.output or b"")
                (case_evidence / "stderr.partial.bin").write_bytes(error.stderr or b"")
                (case_evidence / "unknown-live.json").write_text(json.dumps(
                    {"state": "UNKNOWN_OR_LIVE", "wrapper_pid": proc.pid,
                     "timeout_seconds": 900, "no_next_case_or_retry": True}, indent=2) + "\n")
                record.update(state="UNKNOWN_OR_LIVE", wrapper_pid=proc.pid)
                raise RuntimeError("Unknown/live native unit: preserve handle and stop") from error
            (case_evidence / "stdout.bin").write_bytes(stdout)
            (case_evidence / "stderr.bin").write_bytes(stderr)
            log = case_evidence / "combined.log"
            log.write_bytes(stdout + stderr)
            output = (stdout + stderr).decode("utf-8", errors="replace")
            phases_complete = completed_build_export_phases(
                stdout.decode("utf-8", errors="replace"), stderr.decode("utf-8", errors="replace"))
            passed = phases_complete and (proc.returncode == 0 and "Your solution is okay!" in output
                if expected_error is None else proc.returncode == 1 and expected_error in output)
            record.update(state="TERMINAL", returncode=proc.returncode,
                build_export_phases_complete=phases_complete)
            own_artifacts = preserve_owned_artifacts(project, case_evidence / "artifacts", phases_complete)
            record = {"case": case, "state": "TERMINAL", "command": command, "returncode": proc.returncode,
                "expected_error": expected_error, "passed": passed,
                "build_export_phases_complete": phases_complete,
                "raw_stdout_sha256": hashlib.sha256(stdout).hexdigest(),
                "raw_stderr_sha256": hashlib.sha256(stderr).hexdigest(),
                "combined_log_order": "stdout bytes then stderr bytes, not chronological interleaving",
                "own_artifacts": own_artifacts,
                "log_sha256": hashlib.sha256(log.read_bytes()).hexdigest()}
            print(output, end="" if output.endswith("\n") else "\n", flush=True)
            if not passed:
                raise RuntimeError(f"Native case did not meet its exact outcome: {case}")
            if expected_error is None:
                count = len(json.loads((project / "config.json").read_text())["theorem_names"])
                print(f"Comparator accepted {case}: {count} roots and replayed proof dependencies.")
            else:
                print(f"Negative control passed: {expected_error}", flush=True)
            shutil.rmtree(project / ".lake")
        except BaseException as error:
            record.update(failure_type=type(error).__name__, failure_message=str(error))
            raise
        finally:
            results.append(record)
            (case_evidence / "diagnostic-state.json").write_text(
                json.dumps(record, indent=2) + "\n", encoding="utf-8")
            (args.evidence / "native-results.json").write_text(
                json.dumps(results, indent=2) + "\n", encoding="utf-8")



if __name__ == "__main__":
    main()
