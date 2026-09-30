"""Prepare isolated Comparator projects without executing candidate code."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

from check_challenges import CHALLENGES, validate_challenges


BASELINE = "dce8401a23588ba65b8aa4ca41de26cb0203d444"
MODULES = (
    "DaggerModels/ReverseSimplex.lean",
    "DaggerModels/SimplicialSet.lean",
    "DaggerModels/WordObstruction.lean",
)
CASES = {
    "weakened-statement": "word_obstruction",
    "changed-definition": "simplicial_set",
    "positive-reverse-simplex": "reverse_simplex",
    "positive-simplicial-set": "simplicial_set",
    "positive-word-obstruction": "word_obstruction",
}


def copy_sources(source: Path, target: Path) -> None:
    source = source.resolve()
    files = [source / "DaggerModels.lean", *(source / "DaggerModels").rglob("*.lean")]
    if len(files) < 2:
        raise ValueError("No candidate library sources found")
    for path in files:
        if path.is_symlink() or not path.resolve().is_relative_to(source):
            raise ValueError(f"Source must be an ordinary file inside the checkout: {path}")
        destination = target / path.relative_to(source)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)


def prepare(baseline: Path, candidate: Path, output: Path, control: Path) -> None:
    validate_challenges(control)
    revision = subprocess.check_output(
        ["git", "-C", str(baseline), "rev-parse", "HEAD"], text=True
    ).strip()
    if revision != BASELINE:
        raise ValueError(f"Build inputs and negative controls must use v0.1.0, got {revision}")
    def reference(name: str) -> str:
        return subprocess.check_output(
            ["git", "-C", str(baseline), "show", f"{BASELINE}:{name}"], text=True
        )
    if output.exists():
        raise ValueError("Use a fresh Comparator output directory")
    output.mkdir(parents=True)
    contracts = (control / ".ci/comparator/Contracts.lean").read_text(encoding="utf-8")
    for case in ["cache", *CASES]:
        project = output / case
        project.mkdir()
        for name in ["lean-toolchain", "lake-manifest.json", "lakefile.lean"]:
            (project / name).write_text(reference(name), encoding="utf-8")
        with (project / "lakefile.lean").open("a") as handle:
            handle.write("\nlean_lib Challenge\nlean_lib Solution\n")
        if case == "cache":
            continue
        group = CASES[case]
        challenge_path, config_path = CHALLENGES[group]
        # These specifications come from the trusted control checkout (the PR
        # base), never from candidate sources or the old implementation snapshot.
        challenge = (control / challenge_path).read_text(encoding="utf-8")
        configuration = json.loads((control / config_path).read_text())
        if case.startswith("positive-"):
            copy_sources(candidate, project)
        else:
            for name in ["DaggerModels.lean", *MODULES]:
                path = project / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(reference(name), encoding="utf-8")
        (project / "Challenge.lean").write_text(challenge, encoding="utf-8")
        (project / "Solution.lean").write_text("import DaggerModels\n\n" + contracts, encoding="utf-8")
        (project / "config.json").write_text(json.dumps(configuration, indent=2) + "\n")

    # Both adversarial variants still compile. A rejected Lean build alone must
    # not count as successful detection of a changed statement or definition.
    path = output / "weakened-statement/DaggerModels/WordObstruction.lean"
    text = path.read_text(encoding="utf-8")
    start = text.index("theorem no_dagger_preserving_section :")
    end = text.index("\nend DaggerModels.WordObstruction", start)
    text = text[:start] + "theorem no_dagger_preserving_section : True := by trivial\n" + text[end:]
    path.write_text(text, encoding="utf-8")

    path = output / "changed-definition/DaggerModels/SimplicialSet.lean"
    text = path.read_text(encoding="utf-8")
    start = text.index("def FreeCofibration ")
    end = text.index("\nend DaggerSSet", start)
    text = text[:start] + (
        "def FreeCofibration {X Y : DaggerSSet.{u}} (f : X ⟶ Y) : Prop :=\n"
        "  f = f\n"
    ) + text[end:]
    path.write_text(text, encoding="utf-8")
    print("Prepared three independent statement specifications and two negative controls.")
    print(f"Dependency pins and negative-control implementations remain fixed at {BASELINE}.")


def copy_cache(output: Path) -> None:
    cache = output / "cache/.lake"
    if not cache.is_dir():
        raise ValueError("Fetch the trusted mathlib cache before copying it")
    for case in CASES:
        # Independent copies: an untrusted build cannot modify another case's
        # dependency artifacts through shared writable package directories.
        shutil.copytree(cache, output / case / ".lake", symlinks=False)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--candidate", type=Path)
    parser.add_argument("--control", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--copy-cache", action="store_true")
    args = parser.parse_args()
    if args.copy_cache:
        copy_cache(args.output)
    else:
        if any(value is None for value in [args.baseline, args.candidate, args.control]):
            parser.error("--baseline, --candidate, and --control are required when preparing")
        prepare(args.baseline, args.candidate, args.output, args.control)


if __name__ == "__main__":
    main()
