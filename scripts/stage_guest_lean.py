#!/usr/bin/env python3
"""Stage the pinned, read-only 9p Lean toolchain on guest ext4.

Run as the unprivileged ``runner`` user after the trusted 9p exports are
mounted.  The only privileged operations are copying the already selected
toolchain, making its copy root-owned and unwritable, and binding that copy
read-only over the original absolute prefix.  Emit a compact JSON receipt on
stdout only after the complete copy and mount have been checked.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import pwd
import re
import stat
import subprocess
import sys


SOURCE = Path("/home/runner/.elan/toolchains/leanprover--lean4---v4.27.0")
DESTINATION = Path("/opt/dagger-lean-v4.27.0")
FREE_RESERVE_BYTES = 8 * 1024**3


def run(*command: str) -> str:
    return subprocess.run(command, check=True, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE).stdout.strip()


def sudo(*command: str) -> None:
    subprocess.run(("sudo", "-n", "--", *command), check=True)


def mount_info(path: Path) -> tuple[str, str, set[str]]:
    raw = run("findmnt", "--json", "--output", "TARGET,FSTYPE,OPTIONS",
              "--target", str(path))
    filesystems = json.loads(raw)["filesystems"]
    if len(filesystems) != 1:
        raise RuntimeError(f"ambiguous mount for {path}")
    item = filesystems[0]
    return item["target"], item["fstype"], set(item["options"].split(","))


def tree_manifest(root: Path) -> tuple[list[dict[str, object]], int]:
    """Inventory ordinary files, directories, and literal symlink targets.

    Symlinks are never followed.  Special files are not part of a Lean
    toolchain and are rejected before any privileged copy or mount.
    """
    if not stat.S_ISDIR(root.lstat().st_mode) or root.is_symlink():
        raise RuntimeError(f"toolchain root is not an ordinary directory: {root}")
    records: list[dict[str, object]] = []
    total_file_bytes = 0

    def visit(directory: Path, relative: Path) -> None:
        nonlocal total_file_bytes
        for entry in sorted(os.scandir(directory), key=lambda item: item.name):
            child = directory / entry.name
            rel = relative / entry.name
            info = entry.stat(follow_symlinks=False)
            if stat.S_ISDIR(info.st_mode):
                records.append({"path": rel.as_posix(), "type": "directory"})
                visit(child, rel)
            elif stat.S_ISREG(info.st_mode):
                sha = hashlib.sha256()
                size = 0
                with child.open("rb") as handle:
                    for block in iter(lambda: handle.read(1024 * 1024), b""):
                        size += len(block)
                        sha.update(block)
                if size != info.st_size:
                    raise RuntimeError(f"file changed while hashing: {child}")
                total_file_bytes += size
                records.append({"path": rel.as_posix(), "type": "file",
                                "bytes": size, "sha256": sha.hexdigest()})
            elif stat.S_ISLNK(info.st_mode):
                records.append({"path": rel.as_posix(), "type": "symlink",
                                "target": os.readlink(child)})
            else:
                raise RuntimeError(f"unsupported toolchain entry: {child}")

    visit(root, Path())
    return records, total_file_bytes


def manifest_sha256(records: list[dict[str, object]]) -> str:
    encoded = json.dumps(records, ensure_ascii=True, sort_keys=True,
                         separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def verify_root_owned_read_only(root: Path) -> None:
    def check(path: Path) -> None:
        info = path.lstat()
        if info.st_uid != 0 or info.st_gid != 0:
            raise RuntimeError(f"staged toolchain entry is not root-owned: {path}")
        # Linux symlink permissions are not used for access control and cannot
        # be changed with chmod.  The bind mount itself must be read-only.
        if not stat.S_ISLNK(info.st_mode) and info.st_mode & 0o222:
            raise RuntimeError(f"staged toolchain entry is writable: {path}")
        if stat.S_ISDIR(info.st_mode):
            for entry in os.scandir(path):
                check(path / entry.name)

    check(root)


def stage(source: Path, destination: Path) -> dict[str, object]:
    if sys.platform != "linux" or os.geteuid() == 0 or \
            pwd.getpwuid(os.getuid()).pw_name != "runner":
        raise RuntimeError("Linux unprivileged runner user required")
    if source != SOURCE or destination != DESTINATION:
        raise RuntimeError("unexpected Lean toolchain source or destination")
    if destination.exists() or destination.is_symlink():
        raise RuntimeError(f"staged destination already exists: {destination}")
    if not destination.parent.is_dir() or destination.parent.is_symlink() or \
            destination.parent.resolve() != destination.parent:
        raise RuntimeError("destination parent must be an existing ordinary directory")

    source_mount, source_fs, source_options = mount_info(source)
    destination_mount, destination_fs, destination_options = mount_info(destination.parent)
    if source_fs != "9p" or "ro" not in source_options or \
            source_mount != str(SOURCE.parent.parent):
        raise RuntimeError("source is not on the expected read-only 9p export")
    if destination_fs != "ext4" or "rw" not in destination_options or \
            destination_mount != "/":
        raise RuntimeError("destination is not on the writable guest ext4 root")

    # This is a progress event, not a success receipt.  Hashing a complete
    # toolchain may take time before the privileged copy begins.
    print(json.dumps({"kind": "TRUSTED_GUEST_LEAN_STAGE_PROGRESS",
                      "phase": "copy-start", "source": str(source),
                      "destination": str(destination)}, sort_keys=True), flush=True)
    original, regular_bytes = tree_manifest(source)
    free_bytes = os.statvfs(destination.parent).f_bavail * \
        os.statvfs(destination.parent).f_frsize
    if free_bytes < regular_bytes + FREE_RESERVE_BYTES:
        raise RuntimeError("insufficient guest ext4 space for Lean copy and 8 GiB reserve")

    # Never place a writable overlay over the source.  A failed copy leaves
    # its destination in place so any retry requires deliberate inspection.
    sudo("cp", "-a", "--", str(source), str(destination))
    sudo("chown", "-hR", "0:0", "--", str(destination))
    sudo("chmod", "-R", "a-w", "--", str(destination))
    copied, copied_bytes = tree_manifest(destination)
    unchanged_source, _ = tree_manifest(source)
    if copied != original or unchanged_source != original or copied_bytes != regular_bytes:
        raise RuntimeError("copied Lean tree differs from the immutable 9p source")
    verify_root_owned_read_only(destination)

    mounted = False
    try:
        sudo("mount", "--bind", str(destination), str(source))
        mounted = True
        sudo("mount", "-o", "remount,bind,ro", str(source))
        mount_target, mounted_fs, mounted_options = mount_info(source)
        if mount_target != str(source) or mounted_fs != "ext4" or \
                "ro" not in mounted_options or "rw" in mounted_options:
            raise RuntimeError("Lean bind mount is not the expected read-only ext4 mount")
        if os.stat(source).st_dev != os.stat(destination).st_dev or \
                os.stat(source).st_ino != os.stat(destination).st_ino:
            raise RuntimeError("Lean bind mount does not point at the staged tree")
        rebound, rebound_bytes = tree_manifest(source)
        if rebound != original or rebound_bytes != regular_bytes:
            raise RuntimeError("Lean bind mount content differs from the 9p source")
        version = run(str(source / "bin/lean"), "--version")
        if not re.match(r"^Lean \(version 4\.27\.0(?:,|\))", version):
            raise RuntimeError(f"unexpected staged Lean version: {version}")
        return {
            "kind": "TRUSTED_GUEST_LEAN_EXT4_READONLY_BIND",
            "source": str(source), "destination": str(destination),
            "source_filesystem_before": "9p", "bound_filesystem": mounted_fs,
            "read_only_bind": True, "entries": len(original),
            "regular_file_bytes": regular_bytes,
            "content_manifest_sha256": manifest_sha256(original),
            "lean_version": version,
        }
    except BaseException:
        if mounted:
            sudo("umount", str(source))
        raise


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--destination", type=Path, required=True)
    args = parser.parse_args()
    receipt = stage(args.source, args.destination)
    print(json.dumps(receipt, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
