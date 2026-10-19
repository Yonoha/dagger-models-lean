#!/usr/bin/env python3
"""Verify one official Debian snapshot index before guest apt uses it."""

import hashlib
import lzma
import re
from urllib.request import Request, urlopen

BASE = "https://snapshot.debian.org/archive/debian/20261018/"
INRELEASE_URL = BASE + "dists/trixie-backports/InRelease"
PACKAGES_URL = BASE + "dists/trixie-backports/main/binary-amd64/Packages.xz"
INRELEASE_SHA256 = "22444984a243f2b27cd47058c7783975904f33cf7d9211dee682cc2310ec148b"
PACKAGES_SHA256 = "648c05d7f805521a30ee009894d75a95e4e41fc2f1c177624d9d7758509d838b"
VERSION = "7.2.6-1~bpo13+1"
LINUX_BASE_VERSION = "4.17~bpo13+1"
PACKAGES = {
    "linux-base": (
        "pool/main/l/linux-base/linux-base_4.17~bpo13+1_all.deb",
        26836, "9c1a30ccf8d94672d8a89425fe419d954096718527155fd58974bd1a1043c55f"),
    "linux-image-7.2.6+deb13-cloud-amd64": (
        "pool/main/l/linux-signed-amd64/linux-image-7.2.6+deb13-cloud-amd64_7.2.6-1~bpo13+1_amd64.deb",
        1928, "58e279d3794660d9150c715a7200aca6e2e1f9b41a668d71fc495f2d82b7ae6d"),
    "linux-base-7.2.6+deb13-cloud-amd64": (
        "pool/main/l/linux/linux-base-7.2.6+deb13-cloud-amd64_7.2.6-1~bpo13+1_amd64.deb",
        981540, "fad4866d4907d0dc680c3b07ec23a8fcb0dc2dd523459e884f7320070b61ddb7"),
    "linux-binary-7.2.6+deb13-cloud-amd64": (
        "pool/main/l/linux-signed-amd64/linux-binary-7.2.6+deb13-cloud-amd64_7.2.6-1~bpo13+1_amd64.deb",
        13422984, "c213df3839b725e0309ca93a4c351f072ea06984a16a565415813ca9e722a31c"),
    "linux-modules-7.2.6+deb13-cloud-amd64": (
        "pool/main/l/linux/linux-modules-7.2.6+deb13-cloud-amd64_7.2.6-1~bpo13+1_amd64.deb",
        37672576, "90a1300d864a2ccaed2b56d80344f3e4ccedb4304453cf3234ff19a276560108"),
}


def checked_get(url: str, expected: str) -> bytes:
    with urlopen(Request(url, headers={"User-Agent": "dagger-current-abcd-ci/1"}),
                 timeout=45) as response:
        if not response.geturl().startswith("https://snapshot.debian.org/"):
            raise RuntimeError("Debian snapshot redirect left pinned HTTPS host")
        data = response.read()
    if hashlib.sha256(data).hexdigest() != expected:
        raise RuntimeError("Debian snapshot bytes differ: " + url)
    return data


def check(inrelease: bytes, packages: bytes) -> None:
    text = inrelease.decode()
    section = text.split("SHA256:\n", 1)[1].split("\nSHA512:", 1)[0]
    entry = re.search(
        r"^\s*([0-9a-f]{64})\s+(\d+) main/binary-amd64/Packages.xz$",
        section, re.M,
    )
    if (not entry or entry[1] != PACKAGES_SHA256 or
            int(entry[2]) != len(packages) or
            hashlib.sha256(packages).hexdigest() != PACKAGES_SHA256):
        raise RuntimeError("snapshot Packages.xz is not in pinned InRelease")
    records = lzma.decompress(packages).decode().split("\n\n")
    for package, (filename, size, digest) in PACKAGES.items():
        found = [r for r in records if r.startswith("Package: " + package + "\n")]
        if len(found) != 1:
            raise RuntimeError("exact kernel component absent: " + package)
        version = LINUX_BASE_VERSION if package == "linux-base" else VERSION
        for key, expected in (("Version", version), ("Filename", filename),
                              ("Size", str(size)), ("SHA256", digest)):
            value = re.search(r"^" + key + r": (.+)$", found[0], re.M)
            if not value or value[1] != expected:
                raise RuntimeError("exact kernel component metadata differs: " + package + "/" + key)


def main() -> None:
    inrelease = checked_get(INRELEASE_URL, INRELEASE_SHA256)
    packages = checked_get(PACKAGES_URL, PACKAGES_SHA256)
    check(inrelease, packages)
    print("DEBIAN_SNAPSHOT_EXACT_KERNEL_INDEX_VERIFIED")


if __name__ == "__main__":
    main()
