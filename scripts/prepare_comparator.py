"""Prepare isolated Comparator projects without executing candidate code."""

import argparse
import json
from pathlib import Path
import hashlib
import shutil
import subprocess

from check_challenges import CHALLENGES, validate_challenges
from lean_imports import header_imports
from source_layout import library_source_root


BASELINE = "dce8401a23588ba65b8aa4ca41de26cb0203d444"
FOUNDATION_MANIFEST = ".ci/comparator/foundation-source-manifest.json"
FOUNDATION_MANIFEST_SHA256 = "90acf1ff8b0966a29c31cf76902f0fc4a959039431d6ac61c9f4dbb1c48fbc87"
FROZEN_BARREL = ".ci/comparator/retained/DaggerModels.lean"
FOUNDATION_COUNT = 110
BARREL_SHA256 = "3b434f66add76d7422d1bccc86b163f0c1f97a9c6e5a128da74603cfbda117d5"
MODULES = (
    "DaggerModels/ReverseSimplex.lean",
    "DaggerModels/SimplicialSet.lean",
    "DaggerModels/WordObstruction.lean",
)
CASES = {
    "weakened-statement": "word_obstruction",
    "changed-definition": "simplicial_set",
    **{f"positive-{group.replace('_', '-')}": group for group in CHALLENGES},
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked_source(root: Path, relative: str) -> Path:
    path = root / relative
    if not path.is_file() or path.is_symlink() or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"Source must be an ordinary file inside the checkout: {path}")
    return path


def checked_imports(path: Path, allowed_modules: set[str], external: set[str]) -> None:
    for module in header_imports(path):
        if (module not in allowed_modules and module not in external and
                not module.startswith("Mathlib.")):
            raise ValueError(f"Import escapes retained foundation closure: {path}: {module}")


def copy_sources(source: Path, target: Path, control: Path) -> None:
    source = library_source_root(source).resolve()
    manifest_path = checked_source(control, FOUNDATION_MANIFEST)
    if digest(manifest_path) != FOUNDATION_MANIFEST_SHA256:
        raise ValueError("The retained foundation source manifest changed")
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    paths = manifest["source_paths"]
    if (manifest.get("kind") != "retained_foundation_source_allowlist" or
            len(paths) != FOUNDATION_COUNT or len(paths) != len(set(paths)) or
            paths != sorted(paths) or
            any(not p.startswith("DaggerModels/") or not p.endswith(".lean") for p in paths) or
            manifest.get("barrel_sha256") != BARREL_SHA256):
        raise ValueError("The retained foundation source manifest changed")
    barrel = checked_source(control, FROZEN_BARREL)
    candidate_barrel = checked_source(source, "DaggerModels.lean")
    if digest(barrel) != BARREL_SHA256 or digest(candidate_barrel) != BARREL_SHA256:
        raise ValueError("The published foundation barrel changed")
    allowed_modules = {"DaggerModels", *(p[:-5].replace("/", ".") for p in paths)}
    external = set(manifest["allowed_external_imports"])
    if external != {"Std"}:
        raise ValueError("The retained external import allowlist changed")
    checked_imports(barrel, allowed_modules, external)
    for relative in paths:
        path = checked_source(source, relative)
        checked_imports(path, allowed_modules, external)
        destination = target / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, destination)
    shutil.copyfile(barrel, target / "DaggerModels.lean")


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
            copy_sources(candidate, project, control)
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
    print(f"Prepared {len(CHALLENGES)} independent statement specifications and two negative controls.")
    print(f"Dependency pins and negative-control implementations remain fixed at {BASELINE}.")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path)
    parser.add_argument("--candidate", type=Path)
    parser.add_argument("--control", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if any(value is None for value in [args.baseline, args.candidate, args.control]):
        parser.error("--baseline, --candidate, and --control are required when preparing")
    prepare(args.baseline, args.candidate, args.output, args.control)


if __name__ == "__main__":
    main()
