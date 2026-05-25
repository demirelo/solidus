#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

smokes=(
  test_solidity_forge_smoke.sh
  test_solidity_manifest_replay_smoke.sh
  test_solidity_contract_call_compare.sh
)

printf 'target_bytecode_smokes_start=%s\n' "${#smokes[@]}"

count=0
for smoke in "${smokes[@]}"; do
  printf 'target_bytecode_smoke=%s\n' "$smoke"
  "$ROOT/scripts/$smoke"
  count=$((count + 1))
done

printf 'target_bytecode_smokes=pass\n'
printf 'target_bytecode_smokes_count=%s\n' "$count"
