#!/usr/bin/env python3
"""Build an isolated trusted Lean audit project, without candidate imports."""

import argparse
import hashlib
from pathlib import Path
import re
import shutil


TOOLCHAIN_SHA256 = "d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb"
LAKEFILE = '''import Lake
open Lake DSL

package bcdTrustedAudit where
  moreLeanArgs := #["-DwarningAsError=true"]

lean_exe bcdTrustedAudit where
  root := `TrustedBCDAudit
'''


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--source-sha256", required=True)
    parser.add_argument("--toolchain", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[0-9a-f]{64}", args.source_sha256):
        raise ValueError("trusted auditor source needs an accepted full SHA256")
    if digest(args.source) != args.source_sha256:
        raise ValueError("trusted auditor source SHA256 mismatch")
    if digest(args.toolchain) != TOOLCHAIN_SHA256:
        raise ValueError("trusted Lean toolchain mismatch")
    if args.output.exists():
        raise ValueError("trusted auditor project must be fresh")
    args.output.mkdir(parents=True)
    shutil.copyfile(args.source, args.output / "TrustedBCDAudit.lean")
    shutil.copyfile(args.toolchain, args.output / "lean-toolchain")
    (args.output / "lakefile.lean").write_text(LAKEFILE)
    print("Trusted minimal audit project prepared; compile outside candidate project")


if __name__ == "__main__":
    main()
