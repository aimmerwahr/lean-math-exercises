#!/usr/bin/env bash
# Mechanical style checks for the Lean exercise sheets.
set -euo pipefail

if (($# > 1)); then
  printf 'usage: %s [repository-root]\n' "$0" >&2
  exit 2
fi

cd "${1:-.}"

failed=0

report_matches() {
  local label=$1
  shift
  local matches
  matches=$(rg "$@" || true)
  if [[ -n $matches ]]; then
    printf '%s\n%s\n' "$label" "$matches" >&2
    failed=1
  fi
}

report_matches 'Every toolbox check must use the explicit @ form:' \
  --pcre2 -n '^#check (?!@)' Exercises -g '*.lean'
report_matches 'Exercise placeholders must put sorry on its own line:' \
  -n ':= by sorry$' Exercises -g '*.lean'
report_matches 'Solutions must not import their exercise sheet:' \
  -n '^import Exercises\.' Solutions -g '*.lean'

while IFS= read -r -d '' file; do
  if ! awk '
    /^\/-- \*\*Question [0-9]+\.\*\*$/ {
      if (previous != "" || previous2 != "") {
        printf "%s:%d: question docstrings need two blank lines before them\n", FILENAME, FNR
        bad = 1
      }
      if ((getline following) && following != "") {
        printf "%s:%d: question docstrings need one blank line after the heading\n", FILENAME, FNR
        bad = 1
      }
      previous2 = previous
      previous = following
      next
    }
    { previous2 = previous; previous = $0 }
    END { exit bad }
  ' "$file"; then
    failed=1
  fi
done < <(find Exercises -type f -name '*.lean' -print0)

while IFS= read -r -d '' file; do
  if ! awk '
    /^(private |noncomputable )?(theorem|def|structure|inductive) / {
      if (previous != "" || previous2 != "") {
        printf "%s:%d: top-level declarations need two blank lines before them\n", FILENAME, FNR
        bad = 1
      }
    }
    { previous2 = previous; previous = $0 }
    END { exit bad }
  ' "$file"; then
    failed=1
  fi

  namespace=$(sed -nE 's/^namespace (Solutions\..*)$/\1/p' "$file" | head -n 1)
  last=$(awk 'NF { last = $0 } END { print last }' "$file")
  if [[ -n $namespace && $last != "end $namespace" ]]; then
    printf '%s: expected final line `end %s`, found `%s`\n' "$file" "$namespace" "$last" >&2
    failed=1
  fi
done < <(find Solutions -type f -name '*.lean' -print0)

exit "$failed"
