#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

COMPARES=(
  test_solidity_forge_compare.sh
  test_solidity_forge_compare_imports.sh
  test_solidity_forge_compare_libraries.sh
  test_solidity_forge_compare_inline_assembly.sh
  test_solidity_forge_compare_optimized.sh
)

printf 'forge_compare_smokes_start=%s\n' "${#COMPARES[@]}"
for compare in "${COMPARES[@]}"; do
  printf 'forge_compare_smoke=%s\n' "$compare"
  "$ROOT/scripts/$compare"
done
printf 'forge_compare_smokes=pass\n'
printf 'forge_compare_smokes_count=%s\n' "${#COMPARES[@]}"
