"""Validate v0.4 metadata against the explicitly selected Lean audit scope."""

import argparse
import hashlib
import json
from pathlib import Path

import jsonschema
import yaml

from source_layout import library_source_root


FOUNDATION_REGISTRY = ".ci/metadata/foundation-results.json"
FOUNDATION_REGISTRY_SHA256 = "8fa455a83b97b5b78f5f62b5ed548964b0c1077716b3ff2f3df870cf4bb1bded"
PUBLIC_CONFIG = ".ci/bcd/public-results.json"
PUBLIC_RESULTS = (
    "DaggerComparator.mainB",
    "DaggerComparator.originalMainTheoremC",
    "DaggerComparator.mainD",
)
PUBLIC_CONFIGS = {
    PUBLIC_RESULTS[0]: ".ci/bcd/main-b.json",
    PUBLIC_RESULTS[1]: ".ci/bcd/original-main-c.json",
    PUBLIC_RESULTS[2]: ".ci/bcd/main-d.json",
}
A_RESULT = "DaggerComparator.mainA"
A_CONFIG = ".ci/a/main-a.json"
CURRENT_MAIN_RESULTS = (
    "DaggerActualMainTheoremBProof.verified",
    "DaggerProofOriginalMainTheoremC.verified",
    "ProofActualMainTheoremD.verified",
    *PUBLIC_RESULTS,
    "DaggerTheoremAProof.verified",
    A_RESULT,
)
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CURRENT_OWNER_MODULES = {"ProofTheoremA", "MainTheoremsA", "MainTheoremsABCD"}


def ordinary_file(root: Path, relative: str) -> Path:
    path = root / relative
    if (Path(relative).is_absolute() or ".." in Path(relative).parts or
            not path.is_file() or path.is_symlink() or
            not path.resolve().is_relative_to(root.resolve())):
        raise ValueError(f"Expected an ordinary file within the checkout: {path}")
    return path


def read_report(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    try:
        report = json.loads(text)
    except json.JSONDecodeError:
        reports = []
        for line in text.splitlines():
            if not line.startswith("{"):
                continue
            try:
                item = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(item, dict) and "declarations" in item:
                reports.append(item)
        if len(reports) != 1:
            raise ValueError("Expected exactly one data-only Lean audit report")
        report = reports[0]
    if not isinstance(report, dict) or not isinstance(report.get("declarations"), dict):
        raise ValueError("Invalid Lean declaration report")
    return report


def validate(candidate: Path, trusted: Path, report_path: Path, scope: str) -> None:
    candidate = candidate.resolve()
    trusted = trusted.resolve()
    source_prefix = library_source_root(candidate).relative_to(candidate)
    metadata = yaml.safe_load(
        ordinary_file(candidate, "formalization.yaml").read_text(encoding="utf-8")
    )
    schema = json.loads(ordinary_file(trusted, ".ci/schema/formalization-v0.4.schema.json").read_text())
    jsonschema.Draft7Validator(schema).validate(metadata)
    if metadata["version"] != "v0.4":
        raise ValueError("This checker is pinned to schema v0.4")

    registry_path = ordinary_file(trusted, FOUNDATION_REGISTRY)
    if hashlib.sha256(registry_path.read_bytes()).hexdigest() != FOUNDATION_REGISTRY_SHA256:
        raise ValueError("The retained 67-result registry changed")
    registry = json.loads(registry_path.read_text())
    foundation = registry.get("declarations")
    if (registry.get("kind") != "retained_foundation_result_names" or
            not isinstance(foundation, list) or len(foundation) != 67 or
            len(foundation) != len(set(foundation)) or
            any(not isinstance(name, str) or not name.startswith("DaggerModels.")
                for name in foundation)):
        raise ValueError("The retained 67-result registry changed")
    foundation = set(foundation)
    public = set(PUBLIC_RESULTS)
    current = foundation | public | {A_RESULT}
    trusted_public_config = json.loads(ordinary_file(trusted, PUBLIC_CONFIG).read_text())
    if (trusted_public_config.get("kind") != "bcd_source_comparator_public_results" or
            set(trusted_public_config.get("theorem_names", [])) != public or
            len(trusted_public_config["theorem_names"]) != 3 or
            trusted_public_config.get("config_paths") != PUBLIC_CONFIGS):
        raise ValueError("The trusted BCD public result registration changed")

    results = metadata["status"]["main_results"]
    by_name = {result["declaration"]: result for result in results}
    if len(by_name) != len(results):
        raise ValueError("Duplicate main result declaration")
    names = set(by_name)
    if scope == "foundations":
        # Retain all 67 checks before and after B/C/D and A registration.
        if names not in (foundation, foundation | public, current):
            raise ValueError("Foundations metadata must contain exact 67, 70 or 71 results")
        required = foundation
    elif scope == "full":
        if names != foundation | public:
            raise ValueError("Full metadata must contain exactly the retained 67 and public B/C/D results")
        required = foundation | public
    elif scope == "current":
        if names != current:
            raise ValueError("Current metadata must contain exactly the retained 67, B/C/D three and A")
        required = current
    else:
        raise ValueError(f"Unknown audit scope: {scope}")

    report = read_report(report_path)
    declarations = report["declarations"]
    if not declarations:
        raise ValueError("Empty Lean declaration report")
    if set(metadata["status"]["axioms"]) != set(report.get("project_axioms", [])):
        raise ValueError("Reported project axioms do not match Lean's dependency collector")
    if metadata["status"]["sorry_count"] != 0 or metadata["status"]["sorry_in_definitions"] != 0:
        raise ValueError("The current library is required to have no proof holes")
    if scope == "full":
        if (set(declarations) != required or
                "MainTheoremsBCD" not in report.get("owned_modules", []) or
                not public <= set(report.get("main_results", {}))):
            raise ValueError("Full owner audit does not cover the exact 70 advertised results")
    if scope == "current":
        owners = report.get("owned_modules")
        owned = report.get("owned_declarations")
        main = report.get("main_results")
        counts = report.get("roots_by_owner")
        if (not isinstance(owners, list) or len(owners) != 2771 or
                len(owners) != len(set(owners)) or
                not CURRENT_OWNER_MODULES <= set(owners) or
                not isinstance(owned, list) or len(owned) != len(set(owned)) or
                report.get("declaration_count") != len(owned) or
                not isinstance(counts, dict) or
                not set(counts) <= set(owners) or
                any(type(n) is not int or n <= 0 for n in counts.values()) or
                sum(counts.values()) != len(owned) or
                counts.get("ProofTheoremA", 0) < 1 or
                counts.get("MainTheoremsA", 0) < 1 or
                not isinstance(main, dict) or
                set(main) != set(CURRENT_MAIN_RESULTS) or
                not set(main) <= set(owned) or
                "DaggerTheoremAProof.verified" not in owned or
                A_RESULT not in owned or
                set(declarations) != required or len(declarations) != 71 or
                not required <= set(owned) or
                not set(report.get("project_axioms", [])) <= STANDARD_AXIOMS or
                any(not isinstance(ax, list) or not set(ax) <= STANDARD_AXIOMS
                    for ax in main.values())):
            raise ValueError("Current owner audit lacks exact 2771/71/8 coverage or standard axioms")

    for name in required:
        result = by_name[name]
        if name not in declarations:
            raise ValueError(f"Claimed result does not exist in the selected Lean report: {name}")
        if set(result["axioms"]) != set(declarations[name]):
            raise ValueError(f"Incorrect axiom list for {name}")
        if result["sorry_count"] != 0:
            raise ValueError(f"Invalid proof status for {name}")
        ordinary_file(candidate, result["file"])
        config_path = result["comparator_config"]
        config = json.loads(ordinary_file(candidate, config_path).read_text())
        if name in public:
            trusted_config = json.loads(ordinary_file(trusted, PUBLIC_CONFIGS[name]).read_text())
            if (result["file"] != (source_prefix / "MainTheoremsBCD.lean").as_posix() or
                    config_path != PUBLIC_CONFIGS[name] or
                    trusted_config.get("kind") != "bcd_source_comparator_case" or
                    trusted_config.get("theorem_names") != [name] or
                    config != trusted_config):
                raise ValueError(f"Public BCD result has incorrect source or configuration: {name}")
        if name == A_RESULT and scope == "current":
            trusted_config = json.loads(ordinary_file(trusted, A_CONFIG).read_text())
            if (result["file"] != (source_prefix / "MainTheoremsA.lean").as_posix() or
                    config_path != A_CONFIG or
                    trusted_config != {"kind": "a_source_comparator_case",
                                       "case": "A", "theorem_names": [A_RESULT]} or
                    config != trusted_config):
                raise ValueError("Public A result has incorrect source or configuration")
        if name not in config["theorem_names"]:
            raise ValueError(f"Result is not protected by the stated Comparator configuration: {name}")
    print(f"formalization.yaml passed schema v0.4 and {scope} Lean axiom checks ({len(required)} results).")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scope", choices=("foundations", "full", "current"), default="full")
    parser.add_argument("--axioms", type=Path, required=True)
    parser.add_argument("--candidate-root", type=Path, default=Path.cwd())
    parser.add_argument("--trusted-root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    validate(args.candidate_root, args.trusted_root, args.axioms, args.scope)
