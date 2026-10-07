# Verification records

Release check of `lean/` exactly as published (every `.lean` file and the Lake configuration byte-identical; sha256 in
`files.sha256`), 2026-10-06/07, Linux x86_64, Lean v4.34.1, in two fresh copies of the package, each prepared with
`regen.sh` (`regen.out`: the eight imported upstream-derived modules match `generated.sha256`) and
`lake exe cache get` (Mathlib from the cache).

| file | content |
|---|---|
| `build_test4.tsv` | first copy: `scripts/build_test.sh build_test4.tsv "Kissing4.Statement Kissing4.Solution Kissing4.Axioms"`, the 142 modules reachable from these roots (132 in `Kissing4/`, two in `Kissing/`, eight regenerated upstream modules), each compiled one at a time in dependency order (`lean -j1`), wall time and peak resident memory (KiB) per module, all exit 0; total 2.83 h, largest peak 9018080 KiB (8.60 GiB, `ThomsonGen.M2`) |
| `comparator4.out` | second copy: `scripts/run_comparator.sh comparator4.json`, a `lake build` of `Kissing4.Statement` and `Kissing4.Solution` from scratch, lean4export, "Lean default kernel accepts the solution", "Your solution is okay!", exit 0, for the six theorems of `lean/comparator4.json`; Comparator step 4.56 h wall |
| `axioms4.out` | `#print axioms`: `[propext, Classical.choice, Quot.sound]` for all six (the same output in both copies) |
| `files.sha256` | sha256 of the Lean files present in the checked copies and the Lake configuration (`regen.sh` writes all split modules; eight of them are imported); identical in both copies |
| `regen.out` | output of `regen.sh` |
| `scan_upstream.txt` | `lean/ThomsonGen/scripts/scan_upstream.py` (default selection: the 165 stored Lean files, 33 under `lean/Kissing/` and 132 under `lean/Kissing4/`): 0 verbatim, 46 near-copies, all attributed |
| `time.txt` | GNU time of the whole check (both copies, both dimensions, including waiting for the shared lock): peak resident memory of any single process 9277980 KiB (8.85 GiB) |
| `dim3/` | the same checks for the dimension-3 development in the same copies: `build_test.tsv` (41 modules, all exit 0), `comparator.out` (`lean/comparator.json`, exit 0), `axioms.out` |

Comparator ran with its non-sandboxing shim `fake-landrun.sh`, because `landrun` was not available on the machine.
Tool revisions and binary sha256: `lean/scripts/tools.sh`.
