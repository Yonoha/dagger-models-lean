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
    "presheaf": (
        ".ci/comparator/PresheafChallenge.lean", ".ci/comparator/presheaf.json"
    ),
    "normal_cofibration": (
        ".ci/comparator/NormalCofibrationChallenge.lean", ".ci/comparator/normal_cofibration.json"
    ),
    "unitary_obstruction": (
        ".ci/comparator/UnitaryObstructionChallenge.lean", ".ci/comparator/unitary_obstruction.json"
    ),
    "free_cofibration": (
        ".ci/comparator/FreeCofibrationChallenge.lean", ".ci/comparator/free_cofibration.json"
    ),
    "vertices": (
        ".ci/comparator/VerticesChallenge.lean", ".ci/comparator/vertices.json"
    ),
    "free_dagger_pushout": (
        ".ci/comparator/FreeDaggerPushoutChallenge.lean", ".ci/comparator/free_dagger_pushout.json"
    ),
    "relative_skeleton": (
        ".ci/comparator/RelativeSkeletonChallenge.lean", ".ci/comparator/relative_skeleton.json"
    ),
    "free_dagger_cofibration": (
        ".ci/comparator/FreeDaggerCofibrationChallenge.lean",
        ".ci/comparator/free_dagger_cofibration.json"
    ),
    "relative_cell_boundary": (
        ".ci/comparator/RelativeCellBoundaryChallenge.lean",
        ".ci/comparator/relative_cell_boundary.json"
    ),
    "dagger_simplicial_category": (
        ".ci/comparator/DaggerSimplicialCategoryChallenge.lean",
        ".ci/comparator/dagger_simplicial_category.json"
    ),
    "free_simplicial_paths": (
        ".ci/comparator/FreeSimplicialPathsChallenge.lean",
        ".ci/comparator/free_simplicial_paths.json"
    ),
    "free_dagger_universal": (
        ".ci/comparator/FreeDaggerUniversalChallenge.lean",
        ".ci/comparator/free_dagger_universal.json"
    ),
    "dagger_monadicity": (
        ".ci/comparator/DaggerMonadicityChallenge.lean",
        ".ci/comparator/dagger_monadicity.json"
    ),
    "dagger_graph_presentable": (
        ".ci/comparator/DaggerGraphPresentableChallenge.lean",
        ".ci/comparator/dagger_graph_presentable.json"
    ),
    "dagger_simplicial_presentable": (
        ".ci/comparator/DaggerSimplicialPresentableChallenge.lean",
        ".ci/comparator/dagger_simplicial_presentable.json"
    ),
    "dagger_ordinary_creation": (
        ".ci/comparator/DaggerOrdinaryCreationChallenge.lean",
        ".ci/comparator/dagger_ordinary_creation.json"
    ),
    "two_object_dagger_cell": (
        ".ci/comparator/TwoObjectDaggerCellChallenge.lean",
        ".ci/comparator/two_object_dagger_cell.json"
    ),
    "finite_two_object_cell": (
        ".ci/comparator/FiniteTwoObjectCellChallenge.lean",
        ".ci/comparator/finite_two_object_cell.json"
    ),
    "simplicial_colimits": (
        ".ci/comparator/SimplicialColimitsChallenge.lean",
        ".ci/comparator/simplicial_colimits.json"
    ),
    "dagger_object_generator": (
        ".ci/comparator/DaggerObjectGeneratorChallenge.lean",
        ".ci/comparator/dagger_object_generator.json"
    ),
    "sset_boundary_fibration": (
        ".ci/comparator/SSetBoundaryFibrationChallenge.lean",
        ".ci/comparator/sset_boundary_fibration.json"
    ),
    "sset_boundary_cells": (
        ".ci/comparator/SSetBoundaryCellsChallenge.lean",
        ".ci/comparator/sset_boundary_cells.json"
    ),
    "sset_boundary_retraction": (
        ".ci/comparator/SSetBoundaryRetractionChallenge.lean",
        ".ci/comparator/sset_boundary_retraction.json"
    ),
    "small_object_finite_domains": (
        ".ci/comparator/SmallObjectFiniteDomainsChallenge.lean",
        ".ci/comparator/small_object_finite_domains.json"
    ),
    "ordinary_free_dagger": (
        ".ci/comparator/OrdinaryFreeDaggerChallenge.lean",
        ".ci/comparator/ordinary_free_dagger.json"
    ),
    "dagger_lift": (
        ".ci/comparator/DaggerLiftChallenge.lean", ".ci/comparator/dagger_lift.json"
    ),
}
# Literal category and adjunction statements need complete category structures,
# actual forgetful functors, and the original Hom/unit/counit correspondence.
# These separately reviewed exceptions keep all of that data visible.
# All other Challenges retain the original 100-line budget.
LINE_BUDGET_EXCEPTIONS = {
    ".ci/comparator/DaggerMonadicityChallenge.lean": 160,
    ".ci/comparator/DaggerOrdinaryCreationChallenge.lean": 116,
    ".ci/comparator/OrdinaryFreeDaggerChallenge.lean": 118,
    ".ci/comparator/DaggerLiftChallenge.lean": 234,
}
# The same colimits proof marker is needed by the original chosen Kan extension
# in both specifications. Comparator must check its type in each environment;
# otherwise it compares the marker's proof body to the implementation's proof.
# No other cross-group repeats, or repeats within one group, are permitted.
REPEATED_ROOT_GROUPS = {
    "DaggerModels.simplicialCatHasColimits": {"simplicial_colimits", "dagger_lift"},
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def validate_challenges(root: Path) -> None:
    registered = json.loads((root / ".ci/comparator/targets.json").read_text())["theorem_names"]
    if len(registered) != len(set(registered)) or not registered:
        raise ValueError("The coverage registry must be nonempty and have no duplicate targets")
    covered = []
    root_groups = {}
    total_lines = 0
    for group, (source_path, config_path) in CHALLENGES.items():
        source = (root / source_path).read_text(encoding="utf-8")
        lines = source.splitlines()
        budget = LINE_BUDGET_EXCEPTIONS.get(source_path, 100)
        if len(lines) > budget:
            raise ValueError(f"{source_path} exceeds the {budget}-line review budget: {len(lines)}")
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
        if len(config["theorem_names"]) != len(set(config["theorem_names"])):
            raise ValueError(f"{config_path}: repeated target within one group")
        if set(config["permitted_axioms"]) != STANDARD_AXIOMS:
            raise ValueError(f"{config_path}: changed axiom policy")
        covered.extend(config["theorem_names"])
        for name in config["theorem_names"]:
            root_groups.setdefault(name, set()).add(group)
        print(f"{source_path}: {len(lines)} lines, {len(config['theorem_names'])} comparison roots")
    if set(covered) != set(registered):
        raise ValueError("The Comparator configurations must cover the complete registry")
    for name, groups in root_groups.items():
        expected = REPEATED_ROOT_GROUPS.get(name)
        if expected is not None:
            if groups != expected:
                raise ValueError(f"{name}: expected exactly the supporting groups {sorted(expected)}")
        elif len(groups) != 1:
            raise ValueError(f"{name}: unapproved cross-group repeat")
    print(f"Total review surface: {total_lines} lines; {len(registered)} unique roots; "
          f"{len(covered)} comparisons.")


if __name__ == "__main__":
    validate_challenges(Path(__file__).resolve().parent.parent)
