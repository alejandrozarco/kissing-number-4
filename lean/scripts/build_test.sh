#!/usr/bin/env bash
# Clean build test: compile every module of the package one at a time, in dependency order, single-threaded, and
# record wall time and peak RSS per module. Run from a fresh checkout after ./regen.sh and `lake exe cache get`.
# Usage: bash scripts/build_test.sh [out.tsv] [roots]  (default: build_test.tsv; roots: the 3D statement, proof and
# axiom check, e.g. "Kissing4.Statement Kissing4.Solution Kissing4.Axioms" for dimension 4)
# Needs GNU time (/usr/bin/time) and python3. Optional: BT_WRAP, a command prefix for each module's compile (for
# example a lock on a shared machine).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
OUT="${1:-build_test.tsv}"
export BT_ROOTS="${2:-Kissing.Statement Kissing.Solution Kissing.Axioms}"
ORDER=$(python3 - <<'PY'
import os, re
mods = {}
for top in ("Kissing", "Kissing4", "ThomsonGen"):
    for d, _, fs in os.walk(top):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f); m = p[:-5].replace(os.sep, ".")
                mods[m] = [x for x in re.findall(r"^import\s+(\S+)", open(p, encoding="utf-8").read(), re.M)]
roots = os.environ["BT_ROOTS"].split()
seen, order = set(), []
def visit(m):
    if m in seen or m not in mods: return
    seen.add(m)
    for x in mods[m]: visit(x)
    order.append(m)
for r in roots: visit(r)
print("\n".join(order))
PY
)
printf "module\twall_s\tpeak_rss_kB\texit\n" > "$OUT"
for M in $ORDER; do
  F="${M//.//}.lean"; B=".lake/build/lib/lean/${M//.//}"; mkdir -p "$(dirname "$B")"
  set +e
  ${BT_WRAP:-} /usr/bin/time -f "%e %M" -o .bt.time lake env lean -j1 -DElab.async=false -o "$B.olean" -i "$B.ilean" "$F" \
    > ".bt.$M.out" 2>&1
  RC=$?
  set -e
  read W R < .bt.time
  printf "%s\t%s\t%s\t%s\n" "$M" "$W" "$R" "$RC" >> "$OUT"
  echo "$M wall=${W}s peak=${R}kB rc=$RC"
  grep -E "^[^ ]+:[0-9]+:[0-9]+: error" ".bt.$M.out" && { echo "STOP: errors in $M"; exit 1; }
  [ "$RC" = 0 ] || { echo "STOP: $M exited $RC"; exit 1; }
done
AX=$(echo "$BT_ROOTS" | tr " " "\n" | grep Axioms | tr . /).lean
lake env lean -j1 -DElab.async=false "$AX" > axioms.out 2>&1
echo "BUILD TEST OK"
