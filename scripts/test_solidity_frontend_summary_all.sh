#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

smokes=(
  test_solidity_frontend_summary_smokes.sh
  test_solidity_frontend_optimized_summary_smoke.sh
)

printf 'frontend_summary_all_start=%s\n' "${#smokes[@]}"

count=0
for smoke in "${smokes[@]}"; do
  printf 'frontend_summary_all_smoke=%s\n' "$smoke"
  "$ROOT/scripts/$smoke"
  count=$((count + 1))
done

printf 'frontend_summary_all=pass\n'
printf 'frontend_summary_all_count=%s\n' "$count"
