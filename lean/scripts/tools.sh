# Sourced by run_comparator.sh. Fetches and builds the pinned external checkers into $TOOLS (default: .tools/).
# Pins as in the verification record of huwngtran/thomson-n7-lean (adapted from alejandrozarco/thomson-n7-log,
# lean/scripts/tools.sh). The checks in verification/ used binaries built from exactly these revisions:
#   comparator   sha256 9c52a28d59016a453d9d5da3c1fe09240f6fc4946863bc60849c9b361310c499 (built with its own
#                lean-toolchain, leanprover/lean4:v4.35.0-rc3)
#   lean4export  sha256 8c5d64ba68f4d3a68b3bcb7e1c5f188e35ae573b29470b8d4530a62324c9ddd1 (built with this package's
#                lean-toolchain, leanprover/lean4:v4.34.1)
EXPORT_REV=076e8e57707e813375e8f9da8bf989799ace9680       # leanprover/lean4export, format 3.1.0
COMPARATOR_REV=fd5d5bcf14177b187f66d4502071268d877887c3   # leanprover/comparator; builds with its own toolchain
TOOLS="${TOOLS:-$ROOT/.tools}"; mkdir -p "$TOOLS"; TOOLS="$(cd "$TOOLS" && pwd)"

fetch() {  # fetch <dir> <url> <rev>
  if [ ! -d "$TOOLS/$1/.git" ]; then git clone --quiet "$2" "$TOOLS/$1"; fi
  git -C "$TOOLS/$1" checkout --quiet "$3"
  [ "$(git -C "$TOOLS/$1" rev-parse HEAD)" = "$3" ] || { echo "$1 is not at the pinned revision $3"; exit 1; }
}
need_lean4export() {
  fetch lean4export https://github.com/leanprover/lean4export "$EXPORT_REV"
  # lean4export must run on the Lean version that wrote the .olean files, so it is built with this package's
  # lean-toolchain (a one-line change in the tools checkout).
  if ! cmp -s "$ROOT/lean-toolchain" "$TOOLS/lean4export/lean-toolchain"; then
    cp "$ROOT/lean-toolchain" "$TOOLS/lean4export/lean-toolchain"; rm -rf "$TOOLS/lean4export/.lake/build"
  fi
  (cd "$TOOLS/lean4export" && lake build)
  COMPARATOR_LEAN4EXPORT="$TOOLS/lean4export/.lake/build/bin/lean4export"
}
need_comparator() {
  fetch comparator https://github.com/leanprover/comparator "$COMPARATOR_REV"
  (cd "$TOOLS/comparator" && lake build)
  COMPARATOR_BIN="$TOOLS/comparator/.lake/build/bin/comparator"
}
