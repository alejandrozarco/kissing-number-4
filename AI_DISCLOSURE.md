# AI disclosure

AI models produced the content of this repository: the certificate, the numerical and exact checkers, the Lean
formalisation, the figures and the text. The repository owner chose the problem, approved the Lean statement, directed
the work and decided on scope and publication. The owner did not check the mathematics or the Lean code line by line.

**Models**
- Claude Opus 5.5 (Anthropic, via Claude Code) did the work and wrote the positivity proof on $`S^3`$
  (`Kissing4/Positivity.lean`, `Kissing4/Addition.lean` via `lean/gen/gen_addition4.py`), the chunking lemmas
  (`Kissing4/Chunk.lean`), the numerics and the solution files.
- Claude Sonnet 5.5 (Anthropic), as sub-agents directed by Claude Opus 5.5, wrote `Kissing4/Kernel.lean`,
  `Kissing4/Bound.lean`, `Kissing4/CertK.lean`, `Kissing4/TwentyFour.lean` and the emitter `lean/gen/emit_k4.py`.
- Reviews were run as a separate read-only instance of gpt-6-astra (OpenAI, via the Codex CLI).
- The commits carry a `Co-Authored-By: Claude Opus 5.5` trailer.

**Review and errors found.** The review found no mathematical error. Independently of the
repository code it decoded the certificate data in the Lean files and compared it with the JSON, checked the
polynomial identity, the positive definiteness conditions and the eight addition identities in exact arithmetic, and
checked the 24 points. It asked for four documentation corrections, all made:
- the description of the kernel `Q4` (it is built from the Legendre kernel of the tangent sphere $`S^2`$, and the
  square-root formula holds only where $`(1-u^2)(1-v^2) \gt 0`$);
- the description of the sum-of-squares step in `Kissing4/Positivity.lean` (single products can be negative; the
  weighted double sum is a sum of squares);
- a reference to the dimension-3 Comparator configuration in `Kissing4/Solution.lean`;
- an outdated kernel formula in the docstring of `numerics/kissing4/check_cert_k4.py`.

Problems found and fixed during the work: a single kernel check of the 120-row block used far more memory than
intended (about 16 GB), because each entry access walks a list; the checks of the large blocks were therefore split
into one data definition per matrix row and modules of ten rows (`Kissing4/Chunk.lean` proves that the split checks
are the same Booleans and statistics). Exact rounding with denominator $`2^{24}`$ lost positive definiteness of the
largest block; $`2^{28}`$ kept it.

AI review is not peer review, and no human expert has checked this work. In the terminology of the Lean community
this is a *warrant*, not a human-readable proof.

**What is checked by software**
- `numerics/kissing4/check_cert_k4.py` checks the certificate in exact rational arithmetic, independently of the
  rounding code; `numerics/kissing4/check_controls_k4.py` checks that nine tampered certificates are rejected.
- `lean/gen/gen_addition4.py` checks every generated addition identity with sympy before writing it; the Lean kernel
  then checks it again.
- The Lean 4 kernel checks the formalisation in `lean/`. `#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
- Comparator checks that the proved theorems have the statements of `lean/Kissing4/Statement.lean`. It ran without the
  `landrun` sandbox (`verification/`).

What remains to be trusted:
- that `lean/Kissing4/Statement.lean` expresses the intended theorem (see `lean/STATEMENT4.md`);
- the Mathlib definitions used in `lean/Kissing4/Statement.lean`, which imports only Mathlib;
- the Lean kernel and toolchain;
- Comparator and lean4export (run without the `landrun` sandbox).

The code regenerated from the upstream formalisation,
[huwngtran/thomson-n7-lean](https://github.com/huwngtran/thomson-n7-lean) (itself produced with AI agents), is used only
inside the proof, which the kernel checks; it does not enter the statement.
