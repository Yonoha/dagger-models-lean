#!/usr/bin/env python3
"""Select every pinned Mathlib import of the fixed 2771-source graph."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


GRAPH_SHA = "0a3af50bbf1dbb6ae6ddd5b679cb6d0120306c3f3d34777bc358cfd84859943f"
PROJECT_SHA = {
    "lake-manifest.json": "1c6eb229691c7b0d1b38a574a7897e19dbe7f0bc2674d62c640fdc2e105e3c48",
    "lean-toolchain": "d55ca0039a5479db5b38919d005b2c427b89b3be4f0184a20f2f4eae931f5bdb",
    "lakefile.lean": "eeb7b879c350dfeff90912265d61118c477da867c005f3ac2500e2aef7a41abc",
}
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*")
LOCAL_COUNT = 2771
ROOTS = ["DaggerModels", "MainTheoremsABCD"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def selectors_for_graph(graph):
    """Pure selection/structure check; fixed-file SHA is checked by load_graph."""
    require(graph.get("roots") == ROOTS, "unexpected source roots")
    rows = graph.get("local_source_modules")
    order = graph.get("topological_order")
    require(isinstance(rows, list) and len(rows) == LOCAL_COUNT, "invalid source rows")
    require(graph.get("local_module_count") == LOCAL_COUNT, "invalid local count")
    require(isinstance(order, list) and len(order) == LOCAL_COUNT, "invalid module order")
    names = [row.get("module") for row in rows if isinstance(row, dict)]
    require(len(names) == LOCAL_COUNT and
            all(isinstance(n, str) and MODULE.fullmatch(n) for n in names) and
            len(set(names)) == LOCAL_COUNT, "invalid or duplicate local module")
    require(all(isinstance(n, str) for n in order) and
            len(set(order)) == LOCAL_COUNT and set(order) == set(names),
            "module order differs from rows")
    require(all(root in names for root in ROOTS), "source root missing")
    require(graph.get("unresolved_nonstandard_imports") == [],
            "unresolved source imports")
    positions = {name: i for i, name in enumerate(order)}
    external = set()
    for row in rows:
        imports = row.get("imports")
        require(isinstance(imports, list), "invalid imports list")
        for module in imports:
            require(isinstance(module, str) and MODULE.fullmatch(module),
                    "invalid import name")
            if module in positions:
                require(positions[module] < positions[row["module"]],
                        "local import violates module order")
            else:
                external.add(module)
    unsupported = sorted(m for m in external if m == "Mathlib" or
                         m.split(".")[0] not in {"Mathlib", "Lean", "Init", "Std"})
    require(not unsupported, f"unknown external import roots: {unsupported}")
    return sorted(m for m in external if m.startswith("Mathlib."))


def load_graph(path):
    require(digest(path) == GRAPH_SHA, "fixed source graph SHA mismatch")
    graph = json.loads(path.read_bytes())
    require(graph.get("kind") == "PORTABLE_SOURCE_GRAPH_INVENTORY_NOT_BUILD_ACCEPTANCE",
            "unexpected graph kind")
    return selectors_for_graph(graph)


def verify_project(project):
    require(project.is_dir(), "cache project missing")
    for name, expected in PROJECT_SHA.items():
        path = project / name
        require(path.is_file() and not path.is_symlink() and digest(path) == expected,
                f"trusted cache project mismatch: {name}")
    require(not (project / "lakefile.toml").exists(), "alternate Lakefile present")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, required=True)
    parser.add_argument("--cache-project", type=Path, required=True)
    parser.add_argument("--lake", type=Path, required=True)
    parser.add_argument("--plan-only", action="store_true")
    args = parser.parse_args(argv)
    try:
        selectors = load_graph(args.graph)
        verify_project(args.cache_project)
        require(args.lake.is_absolute() and args.lake.is_file() and
                os.access(args.lake, os.X_OK), "absolute executable Lake path required")
        require(bool(selectors), "empty Mathlib selector set")
        command = [str(args.lake), "exe", "cache", "get", *selectors]
        if args.plan_only:
            print(json.dumps({"graph_sha256": GRAPH_SHA,
                              "mathlib_selector_count": len(selectors),
                              "selectors": selectors, "command": command,
                              "linux_acceptance": False, "publication": False},
                             sort_keys=True))
            return 0
        result = subprocess.run(command, cwd=args.cache_project,
                                env={**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"},
                                check=False)
        return result.returncode
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        parser.exit(2, f"cache selection rejected: {exc}\n")


if __name__ == "__main__":
    raise SystemExit(main())
