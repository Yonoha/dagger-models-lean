#!/usr/bin/env python3
"""Create a trusted Lake cache project without any candidate source."""

import argparse
import hashlib
from pathlib import Path
import shutil


FILES = {
    "lake-manifest.json": "1c6eb229691c7b0d1b38a574a7897e19dbe7f0bc2674d62c640fdc2e105e3c48",
    "lean-toolchain": "d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb",
}

LAKEFILE = '''import Lake
open Lake DSL

package «dagger-models-lean» where
  moreLeanArgs := #["-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "a3a10db0e9d66acbebf76c5e6a135066525ac900"

lean_lib DaggerModels
'''


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pins", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("cache project must be fresh")
    args.output.mkdir(parents=True)
    for name, expected in FILES.items():
        source = args.pins / name
        if hashlib.sha256(source.read_bytes()).hexdigest() != expected:
            raise ValueError(f"trusted pin mismatch: {name}")
        shutil.copyfile(source, args.output / name)
    (args.output / "lakefile.lean").write_text(LAKEFILE)
    print("Trusted cache project prepared; run lake exe cache get in this directory")


if __name__ == "__main__":
    main()
