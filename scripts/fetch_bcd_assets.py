#!/usr/bin/env python3
"""Fetch only a separately SHA-pinned trusted B/C/D asset archive."""

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import tarfile
from urllib.request import Request, urlopen


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def verify_manifest(root: Path, expected: str) -> None:
    manifest = root / "manifest.json"
    if sha(manifest) != expected:
        raise ValueError(f"manifest hash mismatch: {manifest}")
    body = json.loads(manifest.read_text())
    if isinstance(body, dict) and isinstance(body.get("files"), list):
        rows = body["files"]
    elif isinstance(body, dict):
        rows = [{"path": path, "sha256": value} for path, value in body.items()]
    else:
        raise ValueError("invalid trusted manifest")
    seen = set()
    for row in rows:
        relative = PurePosixPath(row["path"])
        if (relative.is_absolute() or ".." in relative.parts or
                relative.as_posix() in seen):
            raise ValueError(f"invalid manifest path: {relative}")
        seen.add(relative.as_posix())
        path = root.joinpath(*relative.parts)
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"invalid manifest file: {path}")
        if ("bytes" in row and path.stat().st_size != row["bytes"]) or sha(path) != row["sha256"]:
            raise ValueError(f"manifest member mismatch: {path}")
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
    if actual != seen | {"manifest.json"}:
        raise ValueError(f"unlisted or missing files in trusted package: {root}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lock", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--preflight-only", action="store_true")
    parser.add_argument("--archive", type=Path,
                        help="use an independently supplied local archive with the locked SHA256")
    args = parser.parse_args()
    lock = json.loads(args.lock.read_text())
    if lock.get("schema") != "bcd-trusted-source-inputs/v1":
        raise ValueError("unknown asset lock schema")
    url = lock.get("published_archive_url")
    expected = lock.get("published_archive_sha256")
    if not isinstance(expected, str) or not re.fullmatch("[0-9a-f]{64}", expected):
        raise SystemExit("B/C/D source CI lacks a pinned whole-archive SHA256")
    if args.archive is None and (not isinstance(url, str) or not url.startswith("https://")):
        raise SystemExit(
            "B/C/D source CI is unconfigured: publish independently reviewed assets "
            "and pin their HTTPS URL and whole-archive SHA256 in asset-lock.json"
        )
    for rel, value in lock["verified_local_content_sha256"].items():
        if not isinstance(value, str) or not re.fullmatch("[0-9a-f]{64}", value):
            raise SystemExit(f"B/C/D source CI lacks an accepted immutable digest: {rel}")
    if args.preflight_only:
        if args.archive is None:
            print("Immutable asset destination and digest are configured")
        else:
            if not args.archive.is_file() or sha(args.archive) != expected:
                raise ValueError("local archive SHA256 mismatch")
            print("Local archive matches locked SHA256; contents not yet extracted or verified")
        return
    if args.output.exists():
        raise ValueError("asset output must be a fresh directory")
    args.output.mkdir(parents=True)
    if args.archive is None:
        archive = args.output / "trusted-inputs.tar.gz"
        with urlopen(Request(url, headers={"User-Agent": "dagger-bcd-source-ci/1"}),
                     timeout=120) as response, archive.open("wb") as output:
            shutil.copyfileobj(response, output)
    else:
        archive = args.archive
    if not archive.is_file() or sha(archive) != expected:
        raise ValueError("trusted archive SHA256 mismatch")
    roots = {"source-graph.json", "trusted-audit",
             "comparator-certificates", "c-universe-extension",
             "changed-definition", "pins"}
    with tarfile.open(archive, "r:gz") as tar:
        seen = set()
        for member in tar:
            rel = PurePosixPath(member.name)
            if (rel.is_absolute() or ".." in rel.parts or not rel.parts or
                    rel.parts[0] not in roots or member.name in seen or
                    not (member.isfile() or member.isdir())):
                raise ValueError(f"unsafe or duplicate archive entry: {member.name}")
            seen.add(member.name)
            target = args.output.joinpath(*rel.parts)
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
                continue
            target.parent.mkdir(parents=True, exist_ok=True)
            with tar.extractfile(member) as source, target.open("xb") as out:
                shutil.copyfileobj(source, out)
    for rel, value in lock["verified_local_content_sha256"].items():
        if sha(args.output / rel) != value:
            raise ValueError(f"locked content SHA256 mismatch: {rel}")
    verify_manifest(args.output / "comparator-certificates",
                    lock["verified_local_content_sha256"]["comparator-certificates/manifest.json"])
    verify_manifest(args.output / "changed-definition",
                    lock["verified_local_content_sha256"]["changed-definition/manifest.json"])
    verify_manifest(args.output / "c-universe-extension",
                    lock["verified_local_content_sha256"]["c-universe-extension/manifest.json"])
    if {p.name for p in (args.output / "pins").iterdir()} != {"lake-manifest.json", "lean-toolchain"}:
        raise ValueError("trusted Lake pin directory contains extra or missing files")
    if {p.name for p in (args.output / "trusted-audit").iterdir()} != {
            "TrustedBCDAudit.lean", "owners.txt", "advertised.txt", "main-results.txt"}:
        raise ValueError("trusted auditor directory contains extra or missing files")
    print("Trusted archive, locked content, and package manifests verified")


if __name__ == "__main__":
    main()
