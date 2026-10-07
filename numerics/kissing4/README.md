# Certificate for 25 points (dimension 4)

Floating-point SDP, exact rounding and exact check of the three-point certificate used in `lean/Kissing4/Cert/`.
The code wraps the dimension-3 code in `numerics/kissing3/`, replacing the kernels of $`S^2`$ by those of $`S^3`$
(Bachoc–Vallentin matrices for $`n = 4`$).

| file | content |
|---|---|
| `k4.py` | SDP formulations for $`S^3`$ (Clarabel via cvxpy), on top of `../kissing3/k3.py`: `bv D` (classical three-point bound), `fixn D n` (fixed-$`n`$ form used here), `mu D n frac` (interior solution at a fraction of the optimal margin), `check tag` (floating-point check of a solution by dense sampling), `test` |
| `run.sh` | runs `k4.py` at low priority with one thread |
| `results.jsonl`, `checks.jsonl` | outputs of `k4.py` (all degrees tried) and of its check of the interior solution |
| `sol/fixn_D14_n25.npz`, `sol/fixn_D14_n25_mu0.5.npz` | the degree-14 solutions (maximal margin; interior, used for rounding) |
| `round_k4.py` | exact rounding, via `../kissing3/round_k3.py` with the kernels of $`S^3`$: blocks rounded to multiples of $`2^{-28}`$, margin $`e = 1/32`$, residual absorbed into the constant-multiplier block. Its log warns that the absorbed residual is not small compared with the interior margin; the exact positive-definiteness check that follows (and `check_cert_k4.py`) settles this |
| `pipeline_d14.sh` | float check, rounding with $`2^{-24}`$ then finer, exact check |
| `cert_D14.json` | the exact certificate (rationals as strings; `"dim": 4`). Its multipliers are $`1/2 - x`$; `lean/gen/emit_k4.py` rescales those blocks by 2 for the Lean multipliers $`1 - 2x`$ |
| `check_cert_k4.py` | independent exact check: input validation, degree bound computed from the data (here 14), the identity on a $`15^3`$ grid, positive definiteness by leading principal minors (python-flint) |
| `check_controls_k4.py` | negative controls: nine tampered certificates, all of which `check_cert_k4.py` must reject |
| `logs/` | output of the solver runs, `round_k4.py` (both rounding attempts), `check_cert_k4.py` and `check_controls_k4.py` |

Floating-point summary from `results.jsonl` (not certified): for $`n = 25`$ the fixed-$`n`$ problem has no positive
margin at degree 8 or 10, margin $`e \approx 0.0056`$ at degree 12 and $`e \approx 0.164`$ at degree 14
(normalisation $`\sum_k \mathrm{tr}\, F_k = 1`$). The interior solution at half the degree-14 margin has all blocks at
least $`5.7 \cdot 10^{-6} I`$; its sampled maximum of $`R`$ over 2389904 points of the region is
$`-3.19 \cdot 10^{-4}`$, below the value $`-2.73 \cdot 10^{-4}`$ implied by its margin.
