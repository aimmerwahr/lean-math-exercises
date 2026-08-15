#!/usr/bin/env bash
# Fixture tests for style-lint.sh.
set -euo pipefail

script_dir=$(cd -- "$(dirname -- "$0")" && pwd)
lint="$script_dir/style-lint.sh"
fixtures="$script_dir/testdata/style-lint"

prepare_fixture() {
  local fixture=$1
  local temporary_root
  local template

  temporary_root=$(mktemp -d "${TMPDIR:-/tmp}/style-lint.XXXXXX")
  cp -R "$fixtures/$fixture/." "$temporary_root"
  while IFS= read -r -d '' template; do
    mv "$template" "${template%.fixture}"
  done < <(find "$temporary_root" -type f -name '*.lean.fixture' -print0)
  printf '%s\n' "$temporary_root"
}

expect_pass() {
  local fixture=$1
  local temporary_root
  temporary_root=$(prepare_fixture "$fixture")
  if ! bash "$lint" "$temporary_root"; then
    rm -rf -- "$temporary_root"
    printf 'expected %s to pass style-lint.sh\n' "$fixture" >&2
    exit 1
  fi
  rm -rf -- "$temporary_root"
}

expect_failure() {
  local fixture=$1
  local expected=$2
  local output
  local temporary_root
  temporary_root=$(prepare_fixture "$fixture")
  if output=$(bash "$lint" "$temporary_root" 2>&1); then
    rm -rf -- "$temporary_root"
    printf 'expected %s to fail style-lint.sh\n' "$fixture" >&2
    exit 1
  fi
  if [[ $output != *$expected* ]]; then
    rm -rf -- "$temporary_root"
    printf 'expected %s to report %q, got:\n%s\n' "$fixture" "$expected" "$output" >&2
    exit 1
  fi
  rm -rf -- "$temporary_root"
}

expect_pass pass
expect_failure missing-at 'Every toolbox check must use the explicit @ form:'
expect_failure inline-sorry 'Exercise placeholders must put sorry on its own line:'
expect_failure exercise-import 'Solutions must not import their exercise sheet:'
expect_failure question-spacing 'question docstrings need one blank line after the heading'
expect_failure missing-end 'expected final line `end Solutions.Example.Sheet`'
