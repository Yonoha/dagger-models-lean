#!/usr/bin/env python3
"""Fetch and verify the separately pinned additive A trusted-input archive.

This checks portable input bytes only. It neither runs Lean nor establishes Linux
CI, Comparator, or publication acceptance. The default lock is intentionally
unconfigured until an independently published archive is reviewed and pinned.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import tarfile
import tempfile
from urllib.parse import urlsplit
from urllib.request import Request, urlopen


ROOT = "dagger-A-additive-trusted-inputs"
SCHEMA = "dagger-A-additive-trusted-inputs/v1"
LOCK_SCHEMA = "dagger-A-additive-trusted-inputs-lock/v1"
GRAPH_SHA = "0a3af50bbf1dbb6ae6ddd5b679cb6d0120306c3f3d34777bc358cfd84859943f"
BCD_SHA = "21111525e8bc72f2c40051f5ce13788beb94ca39c1e4e9daca739d8540f576b3"
PINNED = {
    "current-audit/TrustedABCDAudit.lean": "c513a930965ed19cc6d757276b6d83675eb44992bc87c1bcaefcd8ae3365db03",
    "current-audit/owners.txt": "149da9a29e3cd8535e14acdb9e0c487c7692d4191fd5e9db97c03e1bee273aa2",
    "current-audit/advertised.txt": "1c8b6763d2dfef7e29d8c2142f7a07d919a7340ef9e77efa33c98c97ec0806eb",
    "current-audit/main-results.txt": "972cb0bee03545626e32f817aefb8a84603982f2a8e507c9ae57da01d9219b5b",
    "pins/lake-manifest.json": "1c6eb229691c7b0d1b38a574a7897e19dbe7f0bc2674d62c640fdc2e105e3c48",
    "pins/lean-toolchain": "d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb",
    "external-sources/ComparatorChallengeTheoremA.lean": "e63def08b85954c44e515c1c098dd4aa50368f0f1e99d57074e213fd244a6deb",
    "external-sources/ComparatorSolutionAWeakened.lean": "be46b25e9b145f32b95260ae07eac9b24ba0e6c5a51894c84fe64cbdd643a207",
    "external-sources/ComparatorSolutionAExtraAxiom.lean": "dd7da4738ad39329403276d8344377f7d9f6a97c8844dc7ca00e479c658f15b2",
    "changed-definition/ChallengeTheoremA.lean": "49a59fa469314b662fc34533f48c118710ce2e1886fa13c1e2b99096e1637b31",
    "changed-definition/ProofTheoremA.lean": "fd7505746ee206f2f53ab4c5c4b5ccd4eb02970041c64b5410bce0bdcb12c39b",
    "changed-definition/MainTheoremsA.lean": "fcd075451ab72dedb96b1adb0463775d6fd728ff80104e8aeaf7497c725e13d6",
    "statement-library/ChallengeTheoremA.lean": "2591c2201f9dea1f9c533878c996a89669426d89516655c475308e138ee7dfcf",
    "statement-library/ProofTheoremA.lean": "108dfb28670dbb641564f25442e5089be34e208c83fca91cf9be65d1ef303e76",
    "statement-library/MainTheoremsA.lean": "fcd075451ab72dedb96b1adb0463775d6fd728ff80104e8aeaf7497c725e13d6",
}
DATA_PATHS = set(PINNED) | {
    "current-source/source-graph.json",
    "current-source/ChallengeTheoremA-closure.json",
    "A-frozen/A.challenge.export.gz",
    "evidence/selected-native-summary.json",
}
ALL_PATHS = DATA_PATHS | {"manifest.json"}
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
MAIN_ROOTS = {"DaggerModels", "MainTheoremsABCD", "MainTheoremsBCD",
              "MainTheoremsA", "ProofTheoremA", "ChallengeTheoremA"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def unique_pairs(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def json_file(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=unique_pairs)
    require(isinstance(value, dict), f"expected JSON object: {path}")
    return value


def valid_sha(value: object) -> bool:
    return isinstance(value, str) and HEX64.fullmatch(value) is not None


def https_url(value: object) -> bool:
    if not isinstance(value, str) or any(ord(c) < 33 for c in value):
        return False
    parsed = urlsplit(value)
    return (parsed.scheme == "https" and bool(parsed.hostname) and
            parsed.username is None and parsed.password is None and
            not parsed.fragment)


def check_lock(lock: dict, local: bool) -> dict:
    require(lock.get("schema") == LOCK_SCHEMA, "unknown A asset lock schema")
    require(lock.get("old_BCD_asset_dependency_sha256") == BCD_SHA,
            "old B/C/D dependency digest differs")
    require(lock.get("expected_source_graph_sha256") == GRAPH_SHA,
            "current source graph digest differs")
    require(valid_sha(lock.get("published_archive_sha256")),
            "whole-archive SHA256 must be pinned independently")
    require(valid_sha(lock.get("manifest_sha256")),
            "manifest SHA256 must be pinned independently")
    if not local:
        require(https_url(lock.get("published_archive_url")),
                "public archive requires a pinned HTTPS URL")
    elif lock.get("published_archive_url") is not None:
        require(https_url(lock["published_archive_url"]), "invalid optional HTTPS URL")
    return lock


def safe_name(name: str) -> str:
    require(isinstance(name, str) and name.startswith(ROOT + "/"),
            f"archive prefix differs: {name}")
    require("\\" not in name and "\x00" not in name, f"unsafe archive path: {name}")
    path = PurePosixPath(name)
    require(not path.is_absolute() and name == path.as_posix() and
            all(part not in ("", ".", "..") for part in name.split("/")),
            f"unsafe archive path: {name}")
    relative = "/".join(path.parts[1:])
    require(relative in ALL_PATHS, f"unexpected archive path: {relative}")
    return relative


def read_lines(path: Path, count: int) -> list[str]:
    rows = path.read_text(encoding="utf-8").splitlines()
    require(len(rows) == count and len(rows) == len(set(rows)) and all(rows),
            f"inventory count or duplicates differ: {path.name}")
    return rows


def verify_graph(root: Path) -> dict:
    graph = json_file(root / "current-source/source-graph.json")
    require(graph.get("local_module_count") == 2771 and
            graph.get("roots") == ["DaggerModels", "MainTheoremsABCD"] and
            not graph.get("unresolved_nonstandard_imports"),
            "2771 source graph header differs")
    rows = graph.get("local_source_modules")
    order = graph.get("topological_order")
    require(isinstance(rows, list) and len(rows) == 2771 and
            isinstance(order, list) and len(order) == 2771, "source graph coverage differs")
    names = {}
    for row in rows:
        require(isinstance(row, dict) and isinstance(row.get("module"), str) and
                isinstance(row.get("path"), str) and valid_sha(row.get("sha256")) and
                type(row.get("bytes")) is int and row["bytes"] >= 0 and
                isinstance(row.get("imports"), list), "invalid source graph row")
        require(row["module"] not in names, "duplicate source module")
        names[row["module"]] = row
    require(set(order) == set(names) and len(set(order)) == 2771 and
            MAIN_ROOTS <= set(names), "source graph order or A roots differ")
    closure = json_file(root / "current-source/ChallengeTheoremA-closure.json")
    require(closure.get("root") == "ChallengeTheoremA" and
            closure.get("source_graph_sha256") == GRAPH_SHA and
            closure.get("local_module_count") == 366, "A closure header differs")
    seen = set()
    todo = ["ChallengeTheoremA"]
    while todo:
        name = todo.pop()
        require(name in names, f"missing local closure module: {name}")
        if name in seen:
            continue
        seen.add(name)
        todo.extend(imp for imp in names[name]["imports"] if imp in names)
    require(len(seen) == 366 and
            not seen.intersection({"ProofTheoremA", "MainTheoremsA", "MainTheoremsABCD",
                                   "MainTheoremsBCD"}), "A challenge closure differs")
    expected = [{k: names[name][k] for k in ("module", "path", "bytes", "sha256")}
                for name in order if name in seen]
    require(closure.get("modules") == expected, "366 closure rows differ from graph")
    for name in ("ChallengeTheoremA", "ProofTheoremA", "MainTheoremsA"):
        require(names[name]["sha256"] == PINNED[f"statement-library/{name}.lean"],
                f"statement source and graph differ: {name}")
    return graph


def verify_summary(root: Path) -> None:
    summary = json_file(root / "evidence/selected-native-summary.json")
    require(summary.get("kind") == "PORTABLE_SELECTED_NATIVE_A_EVIDENCE_MACOS_ONLY",
            "native summary kind differs")
    for key in ("Linux_CI_passed", "publication_performed"):
        require(summary.get(key) is False, f"{key} must be explicitly false")
    for key in ("full_2771_native_build_record_verified",
                "expanded_2771_71_8_native_audit_verified", "frozen_BCD_package_unchanged"):
        require(summary.get(key) is True, f"{key} must be explicitly true")
    require(summary.get("source_graph_sha256") == GRAPH_SHA and
            summary.get("old_BCD_asset_dependency_sha256") == BCD_SHA,
            "native summary dependencies differ")
    for key in ("native_original_receipt_sha256", "accepted_build_receipt_sha256",
                "expanded_audit_receipt_sha256", "A_challenge_raw_export_sha256"):
        require(valid_sha(summary.get(key)), f"invalid native summary digest: {key}")
    require(type(summary.get("A_challenge_raw_export_bytes")) is int and
            summary["A_challenge_raw_export_bytes"] > 0, "invalid A export size")
    with gzip.open(root / "A-frozen/A.challenge.export.gz", "rb") as source:
        h = hashlib.sha256()
        size = 0
        for block in iter(lambda: source.read(1024 * 1024), b""):
            h.update(block)
            size += len(block)
            require(size <= summary["A_challenge_raw_export_bytes"], "A export exceeds native size")
    require(size == summary["A_challenge_raw_export_bytes"] and
            h.hexdigest() == summary["A_challenge_raw_export_sha256"],
            "compressed A export differs from native summary")
    cases = summary.get("comparisons")
    expected_cases = {"control-Solution", "control-Mismatch", "control-ForbiddenAxiom",
                      "control-ChangedDefinition-unchanged", "control-ChangedDefinition",
                      "A-normal-control", "A-positive", "A-weakened-True-negative",
                      "A-extra-axiom-negative", "A-changed-leftProper-negative"}
    require(isinstance(cases, list) and len(cases) == 10 and
            {c.get("name") for c in cases if isinstance(c, dict)} == expected_cases,
            "native selected Comparator cases differ")
    for case in cases:
        require(case.get("exit") == (0 if case["name"] in
                {"control-Solution", "control-ChangedDefinition-unchanged",
                 "A-normal-control", "A-positive"} else 1),
                "native Comparator expected result differs")


def verify_payload(root: Path, manifest_sha: str) -> dict:
    manifest_file = root / "manifest.json"
    require(digest(manifest_file) == manifest_sha,
            "independently locked manifest SHA256 mismatch")
    manifest = json_file(manifest_file)
    require(manifest.get("schema") == SCHEMA and
            manifest.get("old_BCD_asset_dependency_sha256") == BCD_SHA and
            manifest.get("source_graph_sha256") == GRAPH_SHA and
            manifest.get("Linux_CI_passed") is False and
            manifest.get("publication_performed") is False,
            "A manifest schema or scope differs")
    files = manifest.get("files")
    require(isinstance(files, dict) and set(files) == DATA_PATHS,
            "A manifest exact file set differs")
    for relative, row in files.items():
        require(isinstance(row, dict) and set(row) == {"sha256", "bytes"} and
                valid_sha(row["sha256"]) and type(row["bytes"]) is int and row["bytes"] >= 0,
                f"invalid manifest row: {relative}")
        path = root.joinpath(*PurePosixPath(relative).parts)
        require(path.is_file() and not path.is_symlink() and
                path.stat().st_size == row["bytes"] and digest(path) == row["sha256"],
                f"manifest byte/hash mismatch: {relative}")
    for relative, expected in PINNED.items():
        require(files[relative]["sha256"] == expected,
                f"builder pinned input differs: {relative}")
    require(files["current-source/source-graph.json"]["sha256"] == GRAPH_SHA,
            "source graph SHA256 differs")
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
    require(actual == ALL_PATHS, "extracted payload exact set differs")
    verify_graph(root)
    owners = read_lines(root / "current-audit/owners.txt", 2771)
    advertised = read_lines(root / "current-audit/advertised.txt", 71)
    main = read_lines(root / "current-audit/main-results.txt", 8)
    graph = json_file(root / "current-source/source-graph.json")
    require(set(owners) == set(graph["topological_order"]) and
            owners == sorted(owners), "2771 audit owner inventory differs")
    require(set(main[3:6] + main[7:]) <= set(advertised) and
            main[-2:] == ["DaggerTheoremAProof.verified", "DaggerComparator.mainA"],
            "71/8 audit result inventory differs")
    require("DaggerComparator.mainA" in advertised and
            "DaggerComparator.mainA" in main, "A main result absent")
    verify_summary(root)
    return {"files_verified": len(ALL_PATHS), "local_modules": 2771,
            "challenge_context_modules": 366, "advertised_results": 71,
            "main_results": 8}


def extract_verified(archive: Path, payload: Path, manifest_sha: str) -> dict:
    with tarfile.open(archive, "r:gz") as tar:
        members = tar.getmembers()
        require(len(members) == len(ALL_PATHS), "archive file count differs")
        names = {}
        for member in members:
            require(member.isfile() and not member.linkname,
                    f"non-regular or linked archive member: {member.name}")
            relative = safe_name(member.name)
            require(relative not in names, f"duplicate archive member: {relative}")
            names[relative] = member
        require(set(names) == ALL_PATHS, "archive exact file set differs")
        for relative, member in names.items():
            target = payload.joinpath(*PurePosixPath(relative).parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            source = tar.extractfile(member)
            require(source is not None, f"missing tar member body: {relative}")
            with source, target.open("xb") as sink:
                shutil.copyfileobj(source, sink)
    return verify_payload(payload, manifest_sha)


def fetch(lock_path: Path, output: Path | None, archive: Path | None,
          preflight_only: bool) -> dict:
    lock = check_lock(json_file(lock_path), archive is not None)
    if archive is not None:
        require(archive.is_file() and not archive.is_symlink(), "local archive must be a regular file")
        require(digest(archive) == lock["published_archive_sha256"],
                "whole-archive SHA256 mismatch")
    if preflight_only:
        return {"kind": "A_ASSET_PREFLIGHT_CONTENTS_UNVERIFIED",
                "whole_archive_sha256": lock["published_archive_sha256"],
                "whole_archive_bytes_checked": archive is not None,
                "manifest_contents_checked": False, "Linux_CI_passed": False,
                "publication_performed": False}
    require(output is not None, "--output is required unless --preflight-only")
    require(not output.exists() and not output.is_symlink() and output.parent.is_dir(),
            "asset output must be a fresh directory with an existing parent")
    temporary = Path(tempfile.mkdtemp(prefix="A-asset-fetch-", dir=output.parent))
    try:
        candidate = temporary / "trusted-inputs-A-additive.tar.gz"
        if archive is None:
            url = lock["published_archive_url"]
            with urlopen(Request(url, headers={"User-Agent": "dagger-A-source-ci/1"}),
                         timeout=120) as source, candidate.open("xb") as sink:
                require(https_url(source.geturl()), "archive redirect left HTTPS")
                shutil.copyfileobj(source, sink)
        else:
            shutil.copyfile(archive, candidate)
        require(digest(candidate) == lock["published_archive_sha256"],
                "whole-archive SHA256 mismatch")
        payload = temporary / "payload"
        payload.mkdir()
        coverage = extract_verified(candidate, payload, lock["manifest_sha256"])
        receipt = {"kind": "A_ADDITIVE_TRUSTED_INPUTS_FETCHED_NOT_LINUX_ACCEPTANCE",
                   "archive_sha256": lock["published_archive_sha256"],
                   "manifest_sha256": lock["manifest_sha256"],
                   "source_graph_sha256": GRAPH_SHA,
                   "old_BCD_asset_dependency_sha256": BCD_SHA,
                   **coverage, "Linux_CI_passed": False,
                   "publication_performed": False}
        (payload / "fetch-receipt.json").write_text(
            json.dumps(receipt, sort_keys=True, separators=(",", ":")) + "\n",
            encoding="utf-8")
        require(not output.exists() and not output.is_symlink(), "asset output appeared during fetch")
        os.replace(payload, output)
        return receipt
    finally:
        shutil.rmtree(temporary)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lock", type=Path,
                        default=Path(__file__).resolve().parents[1] / ".ci/a/asset-lock.json")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--archive", type=Path,
                        help="independently supplied local archive; HTTPS URL is optional")
    parser.add_argument("--preflight-only", action="store_true")
    args = parser.parse_args()
    try:
        result = fetch(args.lock, args.output, args.archive, args.preflight_only)
    except (OSError, ValueError, tarfile.TarError, gzip.BadGzipFile) as error:
        parser.exit(1, f"A asset fetch rejected: {error}\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
