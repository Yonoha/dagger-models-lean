"""Validate the upstream schema and compare reported axioms with Lean output."""

import argparse
import json
from pathlib import Path

import jsonschema
import yaml


def validate(root: Path, report_path: Path) -> None:
    metadata = yaml.safe_load((root / "formalization.yaml").read_text(encoding="utf-8"))
    schema = json.loads((root / ".ci/schema/formalization-v0.4.schema.json").read_text())
    jsonschema.Draft7Validator(schema).validate(metadata)
    if metadata["version"] != "v0.4":
        raise ValueError("This checker is pinned to schema v0.4")
    report = json.loads(report_path.read_text())
    if not report["declarations"]:
        raise ValueError("Empty Lean declaration report")
    if set(metadata["status"]["axioms"]) != set(report["project_axioms"]):
        raise ValueError("Reported project axioms do not match Lean's dependency collector")
    if metadata["status"]["sorry_count"] != 0 or metadata["status"]["sorry_in_definitions"] != 0:
        raise ValueError("The current library is required to have no proof holes")
    for result in metadata["status"]["main_results"]:
        name = result["declaration"]
        if name not in report["declarations"]:
            raise ValueError(f"Claimed result does not exist: {name}")
        if set(result["axioms"]) != set(report["declarations"][name]):
            raise ValueError(f"Incorrect axiom list for {name}")
        if result["sorry_count"] != 0 or not (root / result["file"]).is_file():
            raise ValueError(f"Invalid proof status or file for {name}")
        config = json.loads((root / result["comparator_config"]).read_text())
        if name not in config["theorem_names"]:
            raise ValueError(f"Result is not protected by the stated Comparator configuration: {name}")
    print("formalization.yaml passed the upstream v0.4 schema and Lean axiom consistency checks.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--axioms", type=Path, required=True)
    args = parser.parse_args()
    validate(Path(__file__).resolve().parent.parent, args.axioms)
