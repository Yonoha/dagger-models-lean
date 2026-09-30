"""Run the real Linux sandbox and require specific mismatch diagnostics."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from check_challenges import CHALLENGES


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--projects", type=Path, required=True)
    parser.add_argument("--comparator", type=Path, required=True)
    args = parser.parse_args()
    if sys.platform != "linux" or os.geteuid() == 0:
        raise RuntimeError("Run on Linux as an unprivileged user; no fake sandbox is supported")
    landrun = os.environ["COMPARATOR_LANDRUN"]
    exporter = os.environ["COMPARATOR_LEAN4EXPORT"]
    cases = {
        "weakened-statement": (
            "Challenge and solution theorem statement do not match: "
            "'DaggerModels.WordObstruction.no_dagger_preserving_section'"
        ),
        "changed-definition": (
            "Const does not match between challenge and target "
            "'DaggerModels.DaggerSSet.FreeCofibration'"
        ),
        **{f"positive-{group.replace('_', '-')}": None for group in CHALLENGES},
    }
    # Real candidates run last. Never load their writable .lake artifacts
    # outside Comparator's sandbox, including after the comparison finishes.
    for case, expected_error in cases.items():
        project = (args.projects / case).resolve()
        # A fresh independent copy for every case, staged just before use.
        # Discarding it afterwards keeps disk usage bounded as the coverage grows.
        # Never reuse artifacts that have been writable by a candidate build.
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
        print(f"Running Comparator: {case}", flush=True)
        result = subprocess.run(command, text=True, capture_output=True, timeout=900, check=False)
        output = result.stdout + result.stderr
        (args.projects / f"{case}.log").write_text(output, encoding="utf-8")
        if expected_error is None:
            if result.returncode != 0 or "Your solution is okay!" not in output:
                raise RuntimeError(f"Candidate failed Comparator:\n{output}")
            count = len(json.loads((project / "config.json").read_text())["theorem_names"])
            print(f"Comparator accepted {case}: {count} roots and replayed proof dependencies.")
        elif result.returncode == 0 or expected_error not in output:
            raise RuntimeError(f"Negative control did not fail for the expected reason:\n{output}")
        else:
            print(f"Negative control passed: {expected_error}", flush=True)
        # shutil.rmtree does not follow symlinks and refuses a symlink root.
        # Keep the source and log, but never load the candidate's artifacts again.
        shutil.rmtree(project / ".lake")


if __name__ == "__main__":
    main()
