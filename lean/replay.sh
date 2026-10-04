#!/usr/bin/env bash
# replay.sh — clean build and audit of the supplementary development.
# Run from this directory (lean/). Requires elan (Lean toolchain from lean-toolchain), git, python3, network.
# Exit status is non-zero if the build or the audit gate fails (set -euo pipefail).
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
ulimit -n 65536 2>/dev/null || ulimit -n 10240 2>/dev/null || true
mkdir -p logs
echo "=== toolchain: $(cat lean-toolchain)"
if [ ! -f lake-manifest.json ]; then lake update 2>&1 | tee logs/lake_update.log; fi
echo "=== mathlib cache (upstream .olean files for mathlib d46bd45; everything else is built from source)"
lake exe cache get 2>&1 | tee logs/cache_get.log
echo "=== lake build"
lake build 2>&1 | tee logs/build.log
echo "LAKE_EXIT=0"
echo "=== audit gate (fails unless every required root has exactly one std-3 axiom report and every"
echo "    dependency-check root has exactly one DEPCHECK OK whose forbid list contains the registry)"
python3 scripts/audit_gate.py logs/build.log --required scripts/required_roots.json --depchecks-from 'SelectionS65/*.lean'
echo "GATE_EXIT=0"
