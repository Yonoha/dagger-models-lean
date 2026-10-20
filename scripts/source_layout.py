"""Locate library sources while retaining support for historical flat snapshots.

Module-relative names and frozen source manifests stay unchanged. Current
checkouts store those same bytes under lean/; isolated verifier projects and
older snapshots retain their original flat layout.
"""

from pathlib import Path


def library_source_root(checkout: Path) -> Path:
    checkout = Path(checkout)
    if checkout.is_symlink() or not checkout.is_dir():
        raise ValueError(f"Invalid source checkout: {checkout}")
    source = checkout / "lean"
    if source.is_symlink():
        raise ValueError(f"Source directory must not be a symlink: {source}")
    if source.exists():
        if not source.is_dir():
            raise ValueError(f"Source directory must be a directory: {source}")
        return source
    return checkout
