#!/bin/bash
# Regenerate the upstream-derived ThomsonGen modules (not stored here: upstream has no licence) from the Coulomb
# formalisation huwngtran/thomson-n7-lean at a pinned commit, and check the eight modules this package imports against
# ThomsonGen/scripts/generated.sha256. The splitter (ThomsonGen/scripts/split.py, depdump.tsv, gen_roots.txt) is taken
# unchanged from the logarithmic Thomson N = 7 formalisation (github.com/alejandrozarco/thomson-n7-log); it writes all
# split modules, of which only the eight listed are imported here.
set -euo pipefail
cd "$(dirname "$0")"
REPO=https://github.com/huwngtran/thomson-n7-lean.git
REV=25f2fa53119273458cfbb3c4230904bffdd61e53
SOL_SHA=6545e982abaeb4ca          # prefix of sha256(formal/lean/ThomsonN7/Solution.lean) at REV
U=.upstream
if [ ! -d $U ]; then git clone --quiet $REPO $U; fi
git -C $U checkout --quiet $REV
SOL=$U/formal/lean/ThomsonN7/Solution.lean
case "$(shasum -a 256 $SOL 2>/dev/null || sha256sum $SOL)" in
  $SOL_SHA*) ;; *) echo "unexpected Solution.lean" >&2; exit 1;;
esac
UPSTREAM_SOLUTION=$PWD/$SOL python3 ThomsonGen/scripts/split.py
shasum -a 256 -c ThomsonGen/scripts/generated.sha256 2>/dev/null || sha256sum -c ThomsonGen/scripts/generated.sha256
echo "regen OK"
