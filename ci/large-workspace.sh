#!/usr/bin/env bash
# Prepare a large import closure on a fresh standard GitHub-hosted Linux runner.
set -euo pipefail

[[ "${RUNNER_ENVIRONMENT:-}" == github-hosted && "${RUNNER_OS:-}" == Linux ]] || exit 0
target=.lake/build
mkdir -p "$target"
if [[ "$(findmnt -n -o FSTYPE -T "$target")" == btrfs ]]; then
  exit 0
fi

gib=$((1024 * 1024 * 1024))
free_gib() {
  local remaining
  remaining=$(df -B1 --output=avail "$1" | tail -1)
  echo $((remaining / gib))
}

# Larger runners can use the ordinary build directory.
if (( $(free_gib "$target") >= 128 )); then
  exit 0
fi
work=$(mktemp -d "$RUNNER_TEMP/lean-workspace.XXXXXX")
# The compressed .olean files are mapped by Lean. Keep swap outside the loop device.
if (( $(awk '/MemTotal:/ {print int($2/1024/1024)}' /proc/meminfo) < 32 && $(free_gib "$work") >= 65 )); then
  swap="$work/swap"
  install -m 600 /dev/null "$swap"
  fallocate -l 20G "$swap"
  sudo mkswap "$swap"
  sudo swapon "$swap"
fi
# Keep the checkout, dependency downloads, and temporary archives on the host volume.
capacity=$(( $(free_gib "$work") - 5 ))
(( capacity > 0 ))
image="$work/build.btrfs"
truncate -s "${capacity}G" "$image"
mkfs.btrfs -q "$image"
mkdir "$work/mount"
sudo mount -o loop,compress-force=zstd:3,noatime "$image" "$work/mount"
sudo chown "$(id -u):$(id -g)" "$work/mount"
cp -a "$target/." "$work/mount/"
sudo mount --bind "$work/mount" "$target"
df -hT "$target"
free -h
