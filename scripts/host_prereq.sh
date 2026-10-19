#!/usr/bin/env bash
# Prepared helper. Run on a fresh GitHub-hosted ubuntu-24.04 x64 job after the
# trusted-asset URL preflight, before downloading large tools or images.
set -euo pipefail

[[ "${GITHUB_ACTIONS:-}" == true ]]
[[ "${RUNNER_OS:-}" == Linux ]]
[[ "${RUNNER_ARCH:-}" == X64 ]]
[[ "${RUNNER_ENVIRONMENT:-}" == github-hosted ]] || {
  echo 'SDK cleanup is confined to a fresh GitHub-hosted runner' >&2
  exit 1
}
[[ "$(uname -m)" == x86_64 ]]
[[ "$(. /etc/os-release; printf '%s' "$ID:$VERSION_ID")" == ubuntu:24.04 ]]
# The hosted image may expose KVM only to root/the kvm group. Grant this
# ephemeral job user access to that device without enabling emulation or
# changing the guest isolation requirements.
if [[ -c /dev/kvm && ( ! -r /dev/kvm || ! -w /dev/kvm ) ]]; then
  command -v setfacl >/dev/null || {
    echo 'setfacl is required to grant the hosted job user KVM access' >&2
    exit 1
  }
  sudo setfacl -m "u:$(id -un):rw" /dev/kvm
fi
ls -l /dev/kvm 2>/dev/null || true
[[ -c /dev/kvm && -r /dev/kvm && -w /dev/kvm ]] || {
  echo 'KVM is unavailable; refusing emulation fallback' >&2
  exit 1
}

df -B1 "${RUNNER_TEMP:?}"
for sdk in /usr/local/lib/android/sdk /usr/share/dotnet/sdk; do
  if [[ -e "$sdk" ]]; then
    [[ -d "$sdk" && ! -L "$sdk" && "$(realpath -- "$sdk")" == "$sdk" ]] || {
      echo "Refusing unexpected SDK path: $sdk" >&2
      exit 1
    }
    sudo du -sh -- "$sdk"
    sudo rm -rf -- "$sdk"
  fi
done
df -B1 "$RUNNER_TEMP"

# This is a measured floor for reaching the image/guest probe, not an estimate
# that the complete 2771-module source run will fit. Later phase gates must
# measure capacity again and fail on ENOSPC.
free_bytes="$(df -B1 --output=avail "$RUNNER_TEMP" | tail -1 | tr -d ' ')"
[[ "$free_bytes" =~ ^[0-9]+$ && "$free_bytes" -ge 10737418240 ]] || {
  echo "At least 10 GiB free required after explicit SDK cleanup; got $free_bytes" >&2
  exit 1
}
