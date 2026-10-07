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


def repository_metadata_warning(line: str, project: Path, verified: bool) -> bool:
    return verified and line in {
        f"warning: {name}: repository '{project / '.lake/packages' / name}' has local changes"
        for name in ("mathlib", "batteries")
    }


def verify_trusted_dependency_state(project: Path, evidence: Path) -> dict:
    """Read only the two fresh trusted repositories before native code starts."""
    manifest = json.loads((project / "lake-manifest.json").read_text())
    state = {"verified": False, "repositories": []}
    evidence.mkdir()
    for name in ("mathlib", "batteries"):
        entries = [p for p in manifest["packages"] if p["name"] == name and p["type"] == "git"]
        if len(entries) != 1:
            raise RuntimeError(f"Missing unique pinned dependency: {name}")
        expected = entries[0]["rev"]
        repo = project / ".lake/packages" / name
        if not repo.is_dir() or repo.is_symlink():
            raise RuntimeError(f"Trusted dependency repository missing: {repo}")
        item = {"name": name, "path": str(repo), "expected_rev": expected, "commands": []}
        state["repositories"].append(item)

        def capture(role: str, command: list) -> tuple:
            prefix = evidence / f"{name}-{role}"
            prefix.with_suffix(".command.json").write_text(
                json.dumps({"command": command, "cwd": str(repo)}, indent=2) + "\n")
            try:
                result = subprocess.run(command, cwd=repo, capture_output=True, timeout=30, check=False)
                stdout, stderr, code = result.stdout, result.stderr, result.returncode
            except subprocess.TimeoutExpired as error:
                stdout, stderr, code = error.output or b"", error.stderr or b"", None
            prefix.with_suffix(".stdout.bin").write_bytes(stdout)
            prefix.with_suffix(".stderr.bin").write_bytes(stderr)
            record = {"role": role, "command": command, "cwd": str(repo), "returncode": code,
                "terminal": code is not None, "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
                "stderr_sha256": hashlib.sha256(stderr).hexdigest()}
            item["commands"].append(record)
            return code, stdout

        head_code, head = capture("HEAD", ["git", "rev-parse", "HEAD"])
        head_matches = head_code == 0 and head.decode("ascii", errors="replace").strip() == expected
        diff_command = ["git", "-c", "core.fsmonitor=false", "diff", "--no-ext-diff",
            "--no-textconv", "--exit-code", "HEAD", "--", "."]
        diff_code, _ = capture("diff", diff_command) if head_matches else (None, b"")
        item.update(head_matches=head_matches, diff_clean=diff_code == 0)
        if not head_matches or diff_code != 0:
            if all(command["terminal"] for command in item["commands"]):
                _, paths = capture("tracked-paths", ["git", "-c", "core.fsmonitor=false", "diff",
                    "--no-ext-diff", "--no-textconv", "--name-only", "HEAD", "--", "."])
                all_paths = paths.decode("utf-8", errors="replace").splitlines()
                item.update(changed_tracked_paths=all_paths[:32], paths_truncated=len(all_paths) > 32)
            (evidence / "dependency-state.json").write_text(json.dumps(state, indent=2) + "\n")
            raise RuntimeError(f"Trusted dependency state is not verified: {name}")
    state["verified"] = True
    (evidence / "dependency-state.json").write_text(json.dumps(state, indent=2) + "\n")
    return state


def completed_build_export_phases(stdout: str, stderr: str, project: Path, verified: bool) -> bool:
    cursor = 0
    for pattern in (r"^Building Challenge$", r"^Exporting [\s\S]*? from Challenge$",
            r"^Building Solution$", r"^Exporting [\s\S]*? from Solution$"):
        match = re.search(pattern, stdout[cursor:], re.MULTILINE)
        if match is None:
            return False
        cursor += match.end()
    diagnostic = r"\b(?:error|warning)(?:\([^\n)]*\))?\s*:|\bsorryAx\b"
    for line in (stdout + "\n" + stderr).splitlines():
        if repository_metadata_warning(line, project, verified):
            continue
        if re.search(diagnostic, line):
            if not re.fullmatch(
                    r"(?:warning: )?Challenge\.lean:\d+:\d+: (?:warning: )?declaration uses 'sorry'", line):
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
            dependency_state = verify_trusted_dependency_state(
                project, case_evidence / "trusted-dependency-state")
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
                stdout.decode("utf-8", errors="replace"), stderr.decode("utf-8", errors="replace"),
                project, dependency_state["verified"])
            passed = phases_complete and (proc.returncode == 0 and "Your solution is okay!" in output
                if expected_error is None else proc.returncode == 1 and expected_error in output)
            record.update(state="TERMINAL", returncode=proc.returncode,
                build_export_phases_complete=phases_complete)
            own_artifacts = preserve_owned_artifacts(project, case_evidence / "artifacts", phases_complete)
            record = {"case": case, "state": "TERMINAL", "command": command, "returncode": proc.returncode,
                "expected_error": expected_error, "passed": passed,
                "build_export_phases_complete": phases_complete,
                "trusted_dependency_state_verified": dependency_state["verified"],
                "lake_repository_metadata_warnings": [line for line in output.splitlines()
                    if repository_metadata_warning(line, project, dependency_state["verified"])],
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
