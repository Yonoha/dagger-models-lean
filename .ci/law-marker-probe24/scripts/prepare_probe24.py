"""stage one exact native pair and two named mismatch controls."""

import argparse
import hashlib
import json
from pathlib import Path


PAYLOAD_SHA256 = {
    "Challenge.lean": "7ad4a9813fc470f333833a921365d5537ebdc44bb8972a54e54b3011af283afb",
    "Solution.lean": "0d708e4c2863590af9fe40a85602eefcbceffea85521d9318142490d4c48d24d",
    "config.json": "b987761759d545e931f7e9e86a15c25544443054db15ce5d7bfabad5439fc8bd",
}
REFERENCE_SHA256 = {
    "lean-toolchain": "d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb",
    "lake-manifest.json": "1c6eb229691c7b0d1b38a574a7897e19dbe7f0bc2674d62c640fdc2e105e3c48",
    "lakefile.lean": "ffe067c2e5d3441a679b6a34d5739808491d7af28b33096125aa7586e5523a13",
}
ROLE_APPENDIX = '''
lean_lib Challenge where
  moreLeanArgs := #["-DwarningAsError=false"]

lean_lib Solution where
  moreLeanArgs := #["-DwarningAsError=true"]
'''
CASES = ("weakened-statement", "changed-definition", "positive-law-marker-path")


def checked_bytes(root: Path, name: str, expected: str) -> bytes:
    path = root / name
    if path.is_symlink() or not path.is_file():
        raise ValueError(f"Expected ordinary bound file: {path}")
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError(f"Source bytes differ: {path}")
    return data


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--payload", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    reference = {k: checked_bytes(args.reference, k, v) for k, v in REFERENCE_SHA256.items()}
    payload = {k: checked_bytes(args.payload, k, v) for k, v in PAYLOAD_SHA256.items()}
    config = json.loads(payload["config.json"])
    if (len(config["theorem_names"]) != 24 or config["definition_names"] != []
            or config["challenge_module"] != "Challenge"
            or config["solution_module"] != "Solution"):
        raise ValueError("The frozen 24-target role contract must remain exact")
    if args.output.exists():
        raise ValueError("Use a fresh isolated output directory")
    args.output.mkdir(parents=True)
    source = payload["Solution.lean"].decode("utf-8")
    full_eq = '''theorem enrichment_eq (G : DaggerSimplicialGraph.{u}) :
    enrichment G = FreeSimplicialPaths.enrichedCategory G := by
  rfl'''
    if source.count(full_eq) != 1:
        raise ValueError("The complete original equality contract must occur once")
    marker = "/-- The same Hom, empty-path identity and concatenation, with named law wiring. -/"
    if source.count(marker) != 1:
        raise ValueError("The unique enrichment data declaration marker is required")
    before, after = source.split(marker)
    copy = '''def homCopy (G : DaggerSimplicialGraph.{u}) (x y : G.Obj) : SSet.{u} :=
  FreeSimplicialPaths.hom G x y

'''
    changed = before + copy + marker + after.replace("  Hom := hom G\n", "  Hom := homCopy G\n", 1)
    variants = {
        "weakened-statement": source.replace(full_eq,
            "theorem enrichment_eq (_G : DaggerSimplicialGraph.{u}) : True := by\n  trivial"),
        "changed-definition": changed,
        "positive-law-marker-path": source,
    }
    for case in ("cache", *CASES):
        project = args.output / case
        project.mkdir()
        for name, data in reference.items():
            if name == "lakefile.lean":
                data += ROLE_APPENDIX.encode("utf-8")
            (project / name).write_bytes(data)
        if case == "cache":
            continue
        (project / "Challenge.lean").write_bytes(payload["Challenge.lean"])
        (project / "Solution.lean").write_bytes(variants[case].encode("utf-8"))
        (project / "config.json").write_bytes(payload["config.json"])
    inventory = []
    for path in sorted(args.output.rglob("*")):
        if path.is_file():
            data = path.read_bytes()
            inventory.append({"path": str(path.relative_to(args.output)), "bytes": len(data),
                "sha256": hashlib.sha256(data).hexdigest()})
    (args.output / "prepared-source-bindings.json").write_text(
        json.dumps(inventory, indent=2) + "\n", encoding="utf-8")
    print("Prepared exact 24-target positive and two fixture-only native controls")


if __name__ == "__main__":
    main()
