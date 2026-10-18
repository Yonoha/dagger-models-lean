#!/usr/bin/env python3
"""Fail-closed extraction of the pinned Debian 13 amd64 cloud disk image.

The compressed TAR and its single raw-disk member have distinct, independently
published SHA512 values.  Both must match before QEMU is allowed to boot.
"""

import argparse
import hashlib
import json
from pathlib import Path
import tarfile


BUILD = "20261017-2634"
IMAGE = f"debian-13-genericcloud-amd64-{BUILD}"
ARCHIVE_SHA512 = "dc58995ecf0345272ed9f1d67721395f385e115809ea46012fc348c5a66f152a0fb4690fad87f256aaebc973654025b24848a1697ad24f3174e05aa4fe855bf8"
RAW_SHA512 = "0640ad994f64d7d65d183038806517ec8cbcc86d97bd442e3bd015b67c45f51b7f5871480b346a6bed6576bb1f19899618e5d27fa42601460be1bdd2c42c735c"
RAW_BYTES = 3 * 1024**3


def digest(path: Path) -> str:
    h = hashlib.sha512()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def verify_published_sums(path: Path) -> None:
    rows = {}
    for line in path.read_text().splitlines():
        words = line.split()
        if len(words) != 2 or words[1] in rows:
            raise ValueError("invalid or duplicate SHA512SUMS row")
        rows[words[1]] = words[0]
    if rows.get(IMAGE + ".tar.xz") != ARCHIVE_SHA512:
        raise ValueError("Debian archive SHA512 differs from reviewed pin")
    if rows.get(IMAGE + ".raw") != RAW_SHA512:
        raise ValueError("Debian raw SHA512 differs from reviewed pin")


def extract_checked(archive: Path, sums: Path, output: Path) -> dict:
    verify_published_sums(sums)
    if archive.name != IMAGE + ".tar.xz" or digest(archive) != ARCHIVE_SHA512:
        raise ValueError("compressed Debian image SHA512 mismatch")
    if output.exists() or output.is_symlink():
        raise ValueError("output disk must not exist")
    h = hashlib.sha512()
    count = 0
    created = False
    try:
        with tarfile.open(archive, "r:xz") as tf:
            members = tf.getmembers()
            if (len(members) != 1 or members[0].name != "disk.raw" or
                    not members[0].isfile() or members[0].size != RAW_BYTES):
                raise ValueError("unexpected Debian TAR layout")
            stream = tf.extractfile(members[0])
            if stream is None:
                raise ValueError("raw disk TAR member unreadable")
            with stream, output.open("xb") as dst:
                created = True
                while block := stream.read(1024 * 1024):
                    count += len(block)
                    if count > RAW_BYTES:
                        raise ValueError("raw disk exceeds reviewed size")
                    h.update(block)
                    if not any(block):
                        dst.seek(len(block), 1)
                    else:
                        dst.write(block)
                dst.truncate(count)
        if count != RAW_BYTES or h.hexdigest() != RAW_SHA512:
            raise ValueError("extracted Debian raw disk SHA512 mismatch")
    except Exception:
        if created:
            output.unlink(missing_ok=True)
        raise
    return {"image": IMAGE, "archive_sha512": ARCHIVE_SHA512,
            "raw_sha512": RAW_SHA512, "raw_bytes": count}


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--archive", type=Path, required=True)
    p.add_argument("--sums", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    print(json.dumps(extract_checked(args.archive, args.sums, args.output), sort_keys=True))


if __name__ == "__main__":
    main()
