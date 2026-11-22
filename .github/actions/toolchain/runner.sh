#!/usr/bin/env bash
set -euo pipefail

tools="$(dirname "$RUNNER_TEMP")/rh-tools"
mkdir -p "$tools"
config=$(mktemp -d "$RUNNER_TEMP/rh-gh.XXXXXX")
export GH_CONFIG_DIR="$config"
runner_cpus=$(nproc)
lake_threads=${LEAN_NUM_THREADS:-$runner_cpus}
printf 'Runner reports %s available CPUs. Lake uses %s task threads.\n' "$runner_cpus" "$lake_threads"
{
  echo "LEAN_NUM_THREADS=$lake_threads"
  echo "GH_CONFIG_DIR=$config"
  echo "XDG_CACHE_HOME=$tools/cache"
  echo "UV_PYTHON_BIN_DIR=$tools/bin"
  echo "UV_CACHE_DIR=$tools/uv-cache"
  echo "XDG_DATA_HOME=$tools/data"
} >> "$GITHUB_ENV"

if ! command -v zstd >/dev/null; then
  if [[ ! -x "$tools/zstd/usr/bin/zstd" ]]; then
    stage=$(mktemp -d "$RUNNER_TEMP/rh-zstd.XXXXXX")
    (cd "$stage" && apt-get download zstd && dpkg-deb -x ./*.deb tools)
    mv -T "$stage/tools" "$tools/zstd" || test -x "$tools/zstd/usr/bin/zstd"
  fi
  export PATH="$tools/zstd/usr/bin:$PATH"
  echo "$tools/zstd/usr/bin" >> "$GITHUB_PATH"
fi

# Publish verified tool directories atomically so later jobs can reuse them.
install_archive() {
  local dir=$1 executable=$2 url=$3 digest=$4 stage
  if [[ ! -x "$tools/$dir/bin/$executable" ]]; then
    stage=$(mktemp -d "$tools/.download.XXXXXX")
    (
      trap 'rm -rf "$stage"' EXIT
      curl -fsSL --retry 4 --retry-all-errors -o "$stage/archive" "$url"
      echo "$digest  $stage/archive" | sha256sum --check
      tar -xf "$stage/archive" -C "$stage"
      test -x "$stage/$dir/bin/$executable"
      mv -T "$stage/$dir" "$tools/$dir" || test -x "$tools/$dir/bin/$executable"
    )
  fi
  echo "$tools/$dir/bin" >> "$GITHUB_PATH"
}

if ! gh api --help | grep -- '--slurp' >/dev/null; then
  install_archive gh_2.83.0_linux_amd64 gh \
    https://github.com/cli/cli/releases/download/v2.83.0/gh_2.83.0_linux_amd64.tar.gz \
    a5cf6cdb40fc67751adf561126b3314044779cea81ba4f254fbe8e9a69f1676f
fi

if [[ "$(cat lean-toolchain)" == leanprover/lean4:v4.33.1 ]]; then
  install_archive lean-4.33.1-linux lean \
    https://github.com/leanprover/lean4/releases/download/v4.33.1/lean-4.33.1-linux.tar.zst \
    890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235
else
  export ELAN_HOME="$tools/elan"
  if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
    curl -fsSL --retry 4 --retry-all-errors https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --no-modify-path --default-toolchain none
  fi
  echo "ELAN_HOME=$ELAN_HOME" >> "$GITHUB_ENV"
  echo "$ELAN_HOME/bin" >> "$GITHUB_PATH"
fi
