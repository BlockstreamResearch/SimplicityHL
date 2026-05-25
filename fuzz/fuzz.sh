#!/usr/bin/env bash
# This script is used to briefly fuzz every target when no target is provided. Otherwise, it will briefly fuzz the
# provided target

set -euox pipefail

REPO_DIR=$(git rev-parse --show-toplevel)

# can't find the file because of the ENV var
# shellcheck source=/dev/null
source "$REPO_DIR/fuzz/fuzz-util.sh"

target=
max_total_time=100

for arg in "$@"; do
  case "$arg" in
    -max_total_time=*)
      max_total_time="${arg#-max_total_time=}"
      ;;
    -*)
      echo "Unknown option: $arg"
      exit 2
      ;;
    *)
      if [ -n "$target" ]; then
        echo "Unexpected argument: $arg"
        exit 2
      fi
      target="$arg"
      ;;
  esac
done

case "$max_total_time" in
  ''|*[!0-9]*)
    echo "-max_total_time must be a non-negative integer number of seconds"
    exit 2
    ;;
esac

# Check that input files are correct Windows file names
checkWindowsFiles

if [ -z "$target" ]; then
  targetFiles="$(listTargetFiles)"
else
  targetFiles=fuzz_targets/"$target".rs
fi

cargo --version
rustc --version

# Testing
cargo install --force --locked --version 0.12.0 cargo-fuzz
for targetFile in $targetFiles; do
  targetName=$(targetFileToName "$targetFile")
  echo "Fuzzing target $targetName ($targetFile) for $max_total_time seconds"
  # cargo-fuzz will check for the corpus at fuzz/corpus/<target>
  cargo +nightly fuzz run "$targetName" -- -max_total_time="$max_total_time"
  checkReport "$targetName"
done
