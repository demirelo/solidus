#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

smokes=(
  test_solidity_bytecode_smoke.sh
  test_solidity_frontend_summary_all.sh
  test_solidity_frontend_decode_smokes.sh
  test_solidity_target_bytecode_smokes.sh
  test_solidity_forge_compare_all.sh
)

printf 'solidity_local_smokes_start=%s\n' "${#smokes[@]}"

count=0
for smoke in "${smokes[@]}"; do
  printf 'solidity_local_smoke=%s\n' "$smoke"
  "$ROOT/scripts/$smoke"
  count=$((count + 1))
done

printf 'solidity_local_smokes=pass\n'
printf 'solidity_local_smokes_count=%s\n' "$count"
