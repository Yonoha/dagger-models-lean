#!/usr/bin/env python3
"""Bounded, read-only Linux guest diagnostics; never load candidate code."""

import argparse
import json
import os
from pathlib import Path
import stat


def tail_regular(path: Path, limit: int = 16384) -> dict | None:
    """Refuse symlinks and special files, including replacement races."""
    try:
        fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
        with os.fdopen(fd, "rb") as stream:
            info = os.fstat(stream.fileno())
            if not stat.S_ISREG(info.st_mode):
                return None
            stream.seek(max(0, info.st_size - limit))
            lines = stream.read(limit).decode("utf-8", errors="replace").splitlines()
    except (OSError, ValueError):
        return None
    markers = [line[:600] for line in lines
               if line.startswith(("START_SOURCE ", "BUILT_SOURCE "))]
    return {"name": path.name, "bytes": info.st_size,
            "mtime": info.st_mtime, "last_lines": [s[:600] for s in lines[-2:]],
            "last_source_markers": markers[-2:]}


def snapshot(work: Path) -> dict:
    report = {"kind": "GUEST_PROGRESS", "work_exists": False, "logs": []}
    # The directory is created by the trusted runner. Do not traverse a symlink.
    if not work.is_symlink() and work.is_dir():
        report["work_exists"] = True
        paths = sorted(p for p in work.iterdir()
                       if p.name.endswith((".log", ".stderr")))[:64]
        report["logs"] = [entry for p in paths
                          if (entry := tail_regular(p)) is not None]
    try:
        report["memory_kib"] = {
            line.split(":", 1)[0]: int(line.split()[1])
            for line in Path("/proc/meminfo").read_text().splitlines()
            if line.split(":", 1)[0] in
            {"MemTotal", "MemAvailable", "SwapTotal", "SwapFree"}}
    except (OSError, ValueError):
        pass
    processes = []
    proc = Path("/proc")
    if proc.is_dir():
        for entry in proc.iterdir():
            if not entry.name.isdecimal():
                continue
            try:
                comm = (entry / "comm").read_text().strip()
                if comm not in {"lean", "lake", "lean4export", "local_comparato",
                                "bcdTrustedAudit", "leantar", "git", "cp"}:
                    continue
                fields = (entry / "stat").read_text().rsplit(")", 1)[1].split()
                status = (entry / "status").read_text().splitlines()
                memory = next((s.split(":", 1)[1].strip() for s in status
                               if s.startswith("VmRSS:")), None)
                processes.append({"pid": int(entry.name), "comm": comm,
                                  "state": fields[0], "cpu_ticks": int(fields[11]) + int(fields[12]),
                                  "rss": memory})
                if len(processes) >= 32:
                    break
            except (OSError, ValueError, IndexError):
                continue
    report["processes"] = processes
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("work", type=Path)
    args = parser.parse_args()
    print(json.dumps(snapshot(args.work), sort_keys=True))
