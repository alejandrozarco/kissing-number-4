#!/usr/bin/env bash
# Run leanprover/comparator on this package. It checks that the theorems listed in comparator.json, proved in
# Kissing/Solution.lean, have the same statements as the sorry'd ones in Kissing/Statement.lean, use only propext,
# Quot.sound and Classical.choice, and are accepted by the Lean kernel (replayed from a lean4export dump).
# Needs a workspace prepared by ./regen.sh and `lake exe cache get`, git and network for the first build of the tools,
# and about 10 GB of free RAM. Without COMPARATOR_BIN / COMPARATOR_LEAN4EXPORT, the tools are fetched and built at the
# pinned revisions by scripts/tools.sh (into .tools/). Comparator runs the solution under `landrun` (Linux Landlock); if
# COMPARATOR_LANDRUN is unset and `landrun` is not on PATH, Comparator's non-sandboxing shim scripts/fake-landrun.sh
# is used and a warning is printed.
# Adapted from ComparatorChallenges/run_comparator.sh of huwngtran/thomson-n7-lean.
# Usage: bash scripts/run_comparator.sh [config]   (default comparator.json; comparator4.json for dimension 4)
# Output: logs/comparator.log
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
source scripts/tools.sh
[ -n "${COMPARATOR_LEAN4EXPORT:-}" ] || need_lean4export
[ -n "${COMPARATOR_BIN:-}" ] || need_comparator
export COMPARATOR_LEAN4EXPORT LAKE_ARTIFACT_CACHE=false
if [ -z "${COMPARATOR_LANDRUN:-}" ]; then
  if command -v landrun >/dev/null 2>&1; then COMPARATOR_LANDRUN="$(command -v landrun)"
  else COMPARATOR_LANDRUN="$(dirname "$(dirname "$(dirname "$(dirname "$COMPARATOR_BIN")")")")/scripts/fake-landrun.sh"
       echo "WARNING: no landrun found, using the non-sandboxing shim $COMPARATOR_LANDRUN" >&2; fi
fi
export COMPARATOR_LANDRUN
mkdir -p logs
CFG="${1:-comparator.json}"
/usr/bin/time -p lake env "$COMPARATOR_BIN" "$CFG" 2>&1 | tee logs/comparator.log
echo "COMPARATOR EXIT: ${PIPESTATUS[0]}"
