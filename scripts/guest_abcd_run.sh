#!/usr/bin/env bash
# Runs as the nonroot Debian guest user. All source/build gates remain in the
# trusted control scripts; the candidate checkout is mounted as read-only data.
set -euo pipefail

# Preserve bounded text diagnostics before the host shuts down a failed guest.
# Compiler/export payloads remain in the guest; these are only log tails.
source_failure_logs() {
  local source_status=$? source_log source_count=0
  trap - EXIT
  set +e
  if [[ "$source_status" != 0 && -n "${RUNNER_TEMP:-}" ]]; then
    for source_log in "$RUNNER_TEMP/bcd-run/"*.log "$RUNNER_TEMP/bcd-run/"*.log.stderr; do
      [[ -f "$source_log" && ! -L "$source_log" ]] || continue
      source_count=$((source_count + 1))
      [[ "$source_count" -le 40 ]] || break
      printf '\nGUEST_FAILURE_LOG %s (last 32768 bytes)\n' "${source_log##*/}"
      tail -c 32768 -- "$source_log"
    done
  fi
  exit "$source_status"
}
trap source_failure_logs EXIT

[[ "$(id -un)" == runner && "$(id -u)" != 0 ]]
[[ "$HOME" == /home/runner ]]
[[ "${GITHUB_WORKSPACE:-}" == /home/runner/work/* ]]
[[ "${RUNNER_TEMP:-}" == /home/runner/work/* ]]
[[ "${BCD_SOURCE_REVISION:-}" =~ ^[0-9a-f]{40}$ ]]
export MATHLIB_NO_CACHE_ON_UPDATE=1
export PATH="$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"
sudo install -d -o runner -g "$(id -gn)" -m 0755 -- "$RUNNER_TEMP"
disk_size="$(df -B1 --output=size "$RUNNER_TEMP" | tail -1 | tr -d ' ')"
disk_free="$(df -B1 --output=avail "$RUNNER_TEMP" | tail -1 | tr -d ' ')"
[[ "$disk_size" =~ ^[0-9]+$ && "$disk_size" -ge 30064771072 &&
   "$disk_free" =~ ^[0-9]+$ && "$disk_free" -ge 17179869184 ]] || {
  echo 'Guest root disk was not grown to 28 GiB with 16 GiB free' >&2
  exit 1
}

# The standard Debian kernel supplies these modules; its cloud flavor does not.
sudo modprobe 9pnet_virtio
sudo modprobe 9p

mount_ro_9p() {
  local tag="$1" target="$2" options fstype source
  sudo install -d -m 0755 -- "$target"
  # All exports are immutable for this VM's lifetime and read-only at both
  # ends. Cache metadata so 9p reuses inode identities across Landlock checks.
  # Uncached 9p can otherwise deny execve even for an explicitly allowed file.
  sudo mount -t 9p -o trans=virtio,version=9p2000.L,ro,cache=loose,msize=1048576 \
    "$tag" "$target"
  options="$(findmnt -n -o OPTIONS --target "$target")"
  fstype="$(findmnt -n -o FSTYPE --target "$target")"
  source="$(findmnt -n -o SOURCE --target "$target")"
  [[ "$fstype" == 9p && "$source" == "$tag" ]] || {
    echo "unexpected mount type or source: $tag -> $target" >&2
    exit 1
  }
  [[ ",$options," == *,ro,* ]] || {
    echo "9p share is not read-only: $tag -> $target" >&2
    exit 1
  }
  [[ ",$options," != *,noexec,* ]] || {
    echo "9p executable tool share has noexec: $tag" >&2
    exit 1
  }
}

mount_ro_9p bcdcontrol "$GITHUB_WORKSPACE/control"
mount_ro_9p bcdcandidate "$GITHUB_WORKSPACE/candidate"
mount_ro_9p bcdasset "$RUNNER_TEMP/bcd-trusted"
mount_ro_9p bcdassetA "$RUNNER_TEMP/a-trusted"
mount_ro_9p bcdlandrun "$GITHUB_WORKSPACE/landrun"
mount_ro_9p bcdexporter "$GITHUB_WORKSPACE/lean4export-legacy"
mount_ro_9p bcdauditor "$RUNNER_TEMP/bcd-auditor"
mount_ro_9p bcdeelan "$HOME/.elan"

asset="$RUNNER_TEMP/bcd-trusted"
a_asset="$RUNNER_TEMP/a-trusted"
control="$GITHUB_WORKSPACE/control"
replay="$asset/comparator-certificates/.replay-work/tools"
lock="$control/.ci/bcd/asset-lock.json"
a_lock="$control/.ci/a/asset-lock.json"
[[ -r "$lock" && -r "$a_lock" && -r "$a_asset/current-source/source-graph.json" ]]
# SSH starts in the home directory, which deliberately has no default toolchain.
# Resolve the installed binary using the trusted pinned control project, then
# use its bin directory for every subprocess, including those outside a project.
pinned_lean="$(cd "$control" && elan which lean)"
[[ "$pinned_lean" == /*/bin/lean && -x "$pinned_lean" ]]
export PATH="${pinned_lean%/lean}:$PATH"
[[ -x "$GITHUB_WORKSPACE/landrun/landrun" ]]
[[ -x "$GITHUB_WORKSPACE/lean4export-legacy/.lake/build/bin/lean4export" ]]
[[ -x "$RUNNER_TEMP/bcd-auditor/.lake/build/bin/bcdTrustedAudit" ]]
[[ -x "$replay/comparator/.lake/build/bin/local_comparator_replay" ]]
for binary in \
  "$GITHUB_WORKSPACE/lean4export-legacy/.lake/build/bin/lean4export" \
  "$RUNNER_TEMP/bcd-auditor/.lake/build/bin/bcdTrustedAudit" \
  "$replay/comparator/.lake/build/bin/local_comparator_replay"; do
  if ldd "$binary" 2>&1 | grep -q 'not found'; then
    echo "Missing Debian runtime library for $binary" >&2
    exit 1
  fi
done
command -v lean
command -v lake
command -v git
lean --version
lake --version

sudo loginctl enable-linger runner
sudo systemctl start "user@$(id -u).service"
export XDG_RUNTIME_DIR="/run/user/$(id -u)"
export DBUS_SESSION_BUS_ADDRESS="unix:path=$XDG_RUNTIME_DIR/bus"
systemd-run --user --quiet --wait --collect --pipe /bin/true

# Check execution of a trusted binary from a shared filesystem under the same
# strict wrapper before downloading caches or preparing the full source tree.
systemd-run --user --quiet --wait --collect --pipe \
  --property=RestrictAddressFamilies=~AF_UNIX \
  --property=NoNewPrivileges=yes --setenv=PATH="$PATH" \
  "$GITHUB_WORKSPACE/landrun/landrun" --log-level debug \
  --ro / --rw /dev -ldd -add-exec --env PATH \
  --rox "$(lean --print-prefix)" -- "$pinned_lean" --version

df -B1 "$RUNNER_TEMP"
cache="$RUNNER_TEMP/bcd-cache"
python3 "$control/scripts/prepare_bcd_cache.py" \
  --pins "$asset/pins" --output "$cache"
python3 "$control/scripts/current_mathlib_cache.py" \
  --graph "$a_asset/current-source/source-graph.json" \
  --cache-project "$cache" \
  --lake "$(command -v lake)"
df -B1 "$RUNNER_TEMP"
free_bytes="$(df -B1 --output=avail "$RUNNER_TEMP" | tail -1 | tr -d ' ')"
[[ "$free_bytes" =~ ^[0-9]+$ && "$free_bytes" -ge 8589934592 ]] || {
  echo "Guest has less than 8 GiB free after trusted Mathlib cache" >&2
  exit 1
}

lock_sha() {
  python3 - "$lock" "$1" <<'PY'
import json, re, sys
data = json.load(open(sys.argv[1]))
value = data["published_archive_sha256"] if sys.argv[2] == "archive" else data["verified_local_content_sha256"][sys.argv[2]]
if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{64}", value):
    raise SystemExit("untrusted lock digest")
print(value)
PY
}

asset_sha="$(lock_sha archive)"
a_file_sha() {
  python3 - "$a_lock" "$a_asset/manifest.json" "$1" <<'PY'
import hashlib, json, re, sys
lock = json.load(open(sys.argv[1]))
manifest_path = sys.argv[2]
if hashlib.sha256(open(manifest_path, 'rb').read()).hexdigest() != lock['manifest_sha256']:
    raise SystemExit('A manifest SHA differs from independent lock')
value = json.load(open(manifest_path))['files'][sys.argv[3]]['sha256']
if not isinstance(value, str) or not re.fullmatch(r'[0-9a-f]{64}', value):
    raise SystemExit('A file SHA absent')
print(value)
PY
}
a_manifest_sha="$(python3 - "$a_lock" <<'PY'
import json, re, sys
lock = json.load(open(sys.argv[1]))
value = lock['manifest_sha256']
if not isinstance(value, str) or not re.fullmatch(r'[0-9a-f]{64}', value):
    raise SystemExit('A manifest SHA unpinned')
print(value)
PY
)"
graph_sha="$(a_file_sha current-source/source-graph.json)"
audit_sha="$(a_file_sha current-audit/TrustedABCDAudit.lean)"
owners_sha="$(a_file_sha current-audit/owners.txt)"
advertised_sha="$(a_file_sha current-audit/advertised.txt)"
main_sha="$(a_file_sha current-audit/main-results.txt)"
c_manifest_sha="$(lock_sha c-universe-extension/manifest.json)"
c_extension_sha="$(lock_sha c-universe-extension/extension.json)"
c_guard_sha="$(lock_sha c-universe-extension/CheckGenericCClosure.lean)"
c_guard_result_sha="$(lock_sha c-universe-extension/closure-guard-result.json)"
trusted_lean_path="$(cd "$cache" && lake env printenv LEAN_PATH)"
[[ -n "$trusted_lean_path" ]]

# The current-2771 runner keeps all retained B/C/D gates and adds A. The
# source runner generates its own Lakefile from the pinned A graph.
python3 "$control/scripts/bcd_source_ci.py" \
  --source-profile current-2771 \
  --a-extension "$a_asset" \
  --a-extension-manifest-sha256 "$a_manifest_sha" \
  --candidate "$GITHUB_WORKSPACE/candidate" \
  --graph "$a_asset/current-source/source-graph.json" \
  --graph-sha256 "$graph_sha" \
  --auditor-binary "$RUNNER_TEMP/bcd-auditor/.lake/build/bin/bcdTrustedAudit" \
  --auditor-source "$a_asset/current-audit/TrustedABCDAudit.lean" \
  --auditor-source-sha256 "$audit_sha" \
  --audit-owners "$a_asset/current-audit/owners.txt" \
  --audit-owners-sha256 "$owners_sha" \
  --audit-advertised "$a_asset/current-audit/advertised.txt" \
  --audit-advertised-sha256 "$advertised_sha" \
  --audit-main "$a_asset/current-audit/main-results.txt" \
  --audit-main-sha256 "$main_sha" \
  --frozen "$asset/comparator-certificates" \
  --c-universe-extension "$asset/c-universe-extension" \
  --c-universe-manifest-sha256 "$c_manifest_sha" \
  --c-universe-extension-sha256 "$c_extension_sha" \
  --c-universe-guard-sha256 "$c_guard_sha" \
  --c-universe-guard-result-sha256 "$c_guard_result_sha" \
  --pins "$asset/pins" \
  --changed-definition-fixture "$asset/changed-definition" \
  --cache-dotlake "$cache/.lake" \
  --work "$RUNNER_TEMP/bcd-run" \
  --landrun "$GITHUB_WORKSPACE/landrun/landrun" \
  --legacy-exporter "$GITHUB_WORKSPACE/lean4export-legacy/.lake/build/bin/lean4export" \
  --replay-binary "$replay/comparator/.lake/build/bin/local_comparator_replay" \
  --replay-lean-path "$replay/comparator/.lake/build/lib/lean:$replay/lean4checker/.lake/build/lib/lean" \
  --trusted-lean-path "$trusted_lean_path" \
  --source-revision "$BCD_SOURCE_REVISION" \
  --asset-sha256 "$asset_sha" \
  --lean-prefix "$(lean --print-prefix)" \
  --git-binary "$(command -v git)"

test -s "$RUNNER_TEMP/bcd-run/ci-candidate-result.json"
test -s "$RUNNER_TEMP/bcd-run/audit-all-owners.log"
test -s "$RUNNER_TEMP/bcd-run/audit-restored-owners.log"
echo GUEST_CURRENT_ABCD_SOURCE_CI_PASSED
