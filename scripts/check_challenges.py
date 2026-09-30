"""Check review size, direct Mathlib imports, and complete Comparator registration.

These are source-hygiene checks, not a Lean parser or a security boundary.
The Challenge sources themselves remain trusted, human-reviewable inputs.
"""

import json
from pathlib import Path
import re


CHALLENGES = {
    "reverse_simplex": (
        ".ci/comparator/ReverseSimplexChallenge.lean", ".ci/comparator/reverse_simplex.json"
    ),
    "simplicial_set": (
        ".ci/comparator/SimplicialSetChallenge.lean", ".ci/comparator/simplicial_set.json"
    ),
    "word_obstruction": (
        ".ci/comparator/WordObstructionChallenge.lean", ".ci/comparator/word_obstruction.json"
    ),
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def validate_challenges(root: Path) -> None:
    registered = json.loads((root / ".ci/comparator/targets.json").read_text())["theorem_names"]
    if len(registered) != len(set(registered)) or not registered:
        raise ValueError("The coverage registry must be nonempty and have no duplicate targets")
    covered = []
    total_lines = 0
    for source_path, config_path in CHALLENGES.values():
        source = (root / source_path).read_text(encoding="utf-8")
        lines = source.splitlines()
        if len(lines) > 100:
            raise ValueError(f"{source_path} exceeds the 100-line review budget: {len(lines)}")
        total_lines += len(lines)
        # Import declarations are deliberately plain, one module per line.
        imports = re.findall(r"^import (\S+)\s*$", source, flags=re.MULTILINE)
        if not imports or any(not name.startswith("Mathlib.") for name in imports):
            raise ValueError(f"{source_path} must directly import only Mathlib modules")
        for line in lines:
            if re.match(r"^\s*import\b", line) and not re.fullmatch(r"import Mathlib\.\S+", line):
                raise ValueError(f"{source_path}: unexpected import syntax: {line}")
        config = json.loads((root / config_path).read_text())
        if config["challenge_module"] != "Challenge" or config["solution_module"] != "Solution":
            raise ValueError(f"{config_path}: unexpected module names")
        if config.get("definition_names") or not config["theorem_names"]:
            raise ValueError(f"{config_path}: definition holes or empty theorem list")
        if set(config["permitted_axioms"]) != STANDARD_AXIOMS:
            raise ValueError(f"{config_path}: changed axiom policy")
        covered.extend(config["theorem_names"])
        print(f"{source_path}: {len(lines)} lines, {len(config['theorem_names'])} comparison roots")
    if len(covered) != len(set(covered)) or set(covered) != set(registered):
        raise ValueError("The three Comparator configurations must cover the registry exactly once")
    print(f"Total review surface: {total_lines} lines; {len(covered)} comparison roots.")


if __name__ == "__main__":
    validate_challenges(Path(__file__).resolve().parent.parent)
