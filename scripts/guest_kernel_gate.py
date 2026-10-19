#!/usr/bin/env python3
"""Require the exact Debian backports kernel and Landlock ABI 9+ in x64 guest."""

import ctypes
import json
import os
import platform
import subprocess


KERNEL = "7.2.6+deb13-amd64"
PACKAGE = "linux-image-" + KERNEL
VERSION = "7.2.6-1~bpo13+1"
SYS_LANDLOCK_CREATE_RULESET_X86_64 = 444
LANDLOCK_CREATE_RULESET_VERSION = 1


def main() -> None:
    if os.geteuid() == 0 or platform.machine() != "x86_64":
        raise SystemExit("nonroot x86_64 guest required")
    installed = subprocess.check_output(
        ["dpkg-query", "-W", "-f=${Version}", PACKAGE], text=True).strip()
    running = platform.release()
    libc = ctypes.CDLL(None, use_errno=True)
    abi = libc.syscall(SYS_LANDLOCK_CREATE_RULESET_X86_64,
                       ctypes.c_void_p(), ctypes.c_size_t(0),
                       ctypes.c_uint(LANDLOCK_CREATE_RULESET_VERSION))
    if installed != VERSION or running != KERNEL or abi < 9:
        errno = ctypes.get_errno() if abi < 0 else 0
        raise SystemExit(f"kernel gate failed: installed={installed}, running={running}, "
                         f"landlock_abi={abi}, errno={errno}")
    print(json.dumps({"package": PACKAGE, "version": installed,
                      "running_kernel": running, "landlock_abi": abi}))


if __name__ == "__main__":
    main()
