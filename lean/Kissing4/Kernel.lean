import ThomsonGen.ThreePoint
import Kissing.CertK  -- build order only: keeps `lake build` sequential on a shared machine

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):
-- `Q4` from `ThreePoint.Q3`, `Y4` from `ThreePoint.Y3`, `S4` from `ThreePoint.S3`,
-- `S4_swap12` from `ThreePoint.S3_swap12`, `S4_swap23` from `ThreePoint.S3_swap23`,
-- `inner_coords4` from `ThreePoint.inner_coords`, `normsq_coords4` from `ThreePoint.normsq_coords`,
-- `gram_det_nonneg4` from `ThreePoint.gram_det_nonneg`, `gramOK_inner4` from `ThreePoint.gramOK_inner`,
-- `Rk4` from `ThreePoint.Rk`, `matDot_Rk4` from `ThreePoint.matDot_Rk`,
-- `sum_matDot_Rk4` from `ThreePoint.sum_matDot_Rk`, `three_point_identity4` from `ThreePoint.three_point_identity`.

/-!
# Kernels of the sphere `S³` and the three-point identity in `ℝ⁴`

The upstream three-point development (`ThomsonN7.ThreePoint`) treats unit vectors of `ℝ³` and the kernels
`Q3`, `S3` of `S²`. This file supplies the `ℝ⁴` / `S³` counterparts of everything that depends on the
dimension or on the kernel: the Gegenbauer-type recursion `Q4`, its block matrices `Y4`, `S4`, the reduced
kernel `Rk4`, the Gram-determinant bound for three unit vectors of `ℝ⁴`, and the exact three-point identity.
All dimension-free combinatorics (`dsum`, `Rs`, `GramOK`, `matDot`, ...) is imported unchanged.
-/

open scoped RealInnerProductSpace

namespace Kissing4

open ThomsonN7 ThomsonN7.ThreePoint

/-- Four-dimensional Euclidean space. -/
abbrev R4 := EuclideanSpace ℝ (Fin 4)

/-- The kernel entering the three-point matrices of `S³`, built from the Legendre kernel of the tangent `S²`:
where `(1-u²)(1-v²) > 0`, `Q4 k u v t = k! · ((1-u²)(1-v²))^{k/2} P_k((t-uv)/√((1-u²)(1-v²)))` with `P_k` the
Legendre polynomial; in general it is the polynomial in `u, v, t` defined by `Q4 0 = 1`, `Q4 1 = t - uv` and the
three-term recursion coded below (`k!` times the homogenised Legendre polynomial). -/
noncomputable def Q4 : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _, _, _ => 1
  | 1, u, v, t => t - u * v
  | k + 2, u, v, t =>
      (2 * (k : ℝ) + 3) * (t - u * v) * Q4 (k + 1) u v t
        - ((k : ℝ) + 1) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2)) * Q4 k u v t

/-- Block matrix `(a, b) ↦ uᵃ vᵇ Q4 k u v t` of size `m × m`. -/
noncomputable def Y4 (m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => u ^ (a : ℕ) * v ^ (b : ℕ) * Q4 k u v t

/-- Average of `Y4` over the six orderings of its three arguments. -/
noncomputable def S4 (m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (1 / 6 : ℝ) •
    (Y4 m k u v t + Y4 m k u t v + Y4 m k v u t + Y4 m k v t u + Y4 m k t u v + Y4 m k t v u)

theorem S4_swap12 (m k : ℕ) (u v t : ℝ) : S4 m k u v t = S4 m k v u t := by
  ext i j
  simp only [S4, Y4, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring

theorem S4_swap23 (m k : ℕ) (u v t : ℝ) : S4 m k u v t = S4 m k u t v := by
  ext i j
  simp only [S4, Y4, Matrix.smul_apply, Matrix.add_apply, Matrix.of_apply, smul_eq_mul]
  ring

/-- The reduced matrix kernel for `n` points, built from `S4`. -/
noncomputable def Rk4 (n m k : ℕ) (u v t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  ((n : ℝ) - 2) • S4 m k u v t + (S4 m k u u 1 + S4 m k v v 1 + S4 m k t t 1)
    + (1 / ((n : ℝ) - 1)) • S4 m k 1 1 1

theorem matDot_Rk4 {m : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (n k : ℕ) (u v t : ℝ) :
    matDot F (Rk4 n m k u v t) = Rs (fun u v t => matDot F (S4 m k u v t)) n u v t := by
  simp only [Rk4, Rs, matDot_add, matDot_smul]
  ring

theorem sum_matDot_Rk4 (K n : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (u v t : ℝ) :
    ∑ k ∈ Finset.range K, matDot (F k) (Rk4 n (m k) k u v t)
      = Rs (fun u v t => ∑ k ∈ Finset.range K, matDot (F k) (S4 (m k) k u v t)) n u v t := by
  simp only [matDot_Rk4, Rs, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]

/-! ### Gram determinant in `ℝ⁴` -/

/-- The inner product of two vectors of `ℝ⁴` in coordinates. -/
theorem inner_coords4 (x y : R4) :
    ⟪x, y⟫ = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 := by
  simp [PiLp.inner_apply, Fin.sum_univ_four, mul_comm]

/-- A unit vector of `ℝ⁴` has coordinates of squared sum `1`. -/
theorem normsq_coords4 (x : R4) (hx : ‖x‖ = 1) :
    x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = 1 := by
  have := real_inner_self_eq_norm_sq x
  rw [hx, inner_coords4] at this
  nlinarith [this]

/-- Cauchy–Binet for a `3 × 4` matrix: the Gram determinant is the sum of the squares of the four
`3 × 3` minors. -/
theorem gram_det_eq_minors (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : ℝ) :
    (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2)
        * (z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2)
      + 2 * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) * (x0 * z0 + x1 * z1 + x2 * z2 + x3 * z3)
        * (y0 * z0 + y1 * z1 + y2 * z2 + y3 * z3)
      - (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2) * (y0 * z0 + y1 * z1 + y2 * z2 + y3 * z3) ^ 2
      - (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2) * (x0 * z0 + x1 * z1 + x2 * z2 + x3 * z3) ^ 2
      - (z0 ^ 2 + z1 ^ 2 + z2 ^ 2 + z3 ^ 2) * (x0 * y0 + x1 * y1 + x2 * y2 + x3 * y3) ^ 2
    = (x0 * (y1 * z2 - y2 * z1) - x1 * (y0 * z2 - y2 * z0) + x2 * (y0 * z1 - y1 * z0)) ^ 2
      + (x0 * (y1 * z3 - y3 * z1) - x1 * (y0 * z3 - y3 * z0) + x3 * (y0 * z1 - y1 * z0)) ^ 2
      + (x0 * (y2 * z3 - y3 * z2) - x2 * (y0 * z3 - y3 * z0) + x3 * (y0 * z2 - y2 * z0)) ^ 2
      + (x1 * (y2 * z3 - y3 * z2) - x2 * (y1 * z3 - y3 * z1) + x3 * (y1 * z2 - y2 * z1)) ^ 2 := by
  ring

/-- The Gram determinant of three unit vectors of `ℝ⁴` is nonnegative. -/
theorem gram_det_nonneg4 (x y z : R4) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    0 ≤ 1 + 2 * ⟪x, y⟫ * ⟪x, z⟫ * ⟪y, z⟫ - ⟪x, y⟫ ^ 2 - ⟪x, z⟫ ^ 2 - ⟪y, z⟫ ^ 2 := by
  have hx' := normsq_coords4 x hx
  have hy' := normsq_coords4 y hy
  have hz' := normsq_coords4 z hz
  have h := gram_det_eq_minors (x 0) (x 1) (x 2) (x 3) (y 0) (y 1) (y 2) (y 3) (z 0) (z 1) (z 2) (z 3)
  rw [hx', hy', hz'] at h
  rw [inner_coords4, inner_coords4, inner_coords4]
  have hsq : 0 ≤ (x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0)
        + x 2 * (y 0 * z 1 - y 1 * z 0)) ^ 2
      + (x 0 * (y 1 * z 3 - y 3 * z 1) - x 1 * (y 0 * z 3 - y 3 * z 0)
        + x 3 * (y 0 * z 1 - y 1 * z 0)) ^ 2
      + (x 0 * (y 2 * z 3 - y 3 * z 2) - x 2 * (y 0 * z 3 - y 3 * z 0)
        + x 3 * (y 0 * z 2 - y 2 * z 0)) ^ 2
      + (x 1 * (y 2 * z 3 - y 3 * z 2) - x 2 * (y 1 * z 3 - y 3 * z 1)
        + x 3 * (y 1 * z 2 - y 2 * z 1)) ^ 2 := by positivity
  linarith

/-- Three unit vectors of `ℝ⁴` have a Gram triple in the region `GramOK`. -/
theorem gramOK_inner4 (x y z : R4) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1) :
    GramOK ⟪x, y⟫ ⟪x, z⟫ ⟪y, z⟫ := by
  have h1 : ∀ a b : R4, ‖a‖ = 1 → ‖b‖ = 1 → ⟪a, b⟫ ^ 2 ≤ 1 := by
    intro a b ha hb
    have := abs_real_inner_le_norm a b
    rw [ha, hb, mul_one] at this
    exact (sq_le_one_iff_abs_le_one _).mpr this
  refine ⟨h1 x y hx hy, h1 x z hx hz, h1 y z hy hz, ?_⟩
  have := gram_det_nonneg4 x y z hx hy hz
  linarith

/-- The exact three-point identity for `n ≥ 3` unit vectors of `ℝ⁴`, for any symmetric kernel `s`. -/
theorem three_point_identity4 {n : ℕ} (hn : 3 ≤ n) (s : ℝ → ℝ → ℝ → ℝ)
    (hs12 : ∀ u v t, s u v t = s v u t) (hs23 : ∀ u v t, s u v t = s u t v)
    (H : ℝ → ℝ) (e : ℝ) (x : Fin n → R4) (hx : ∀ i, ‖x i‖ = 1) :
    dsum (fun i j l => ((H ⟪x i, x j⟫ + H ⟪x i, x l⟫ + H ⟪x j, x l⟫) / 3
        - e / (n.choose 2 : ℝ)) - Rs s n ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫)
      + ((n : ℝ) - 2) * ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫
    = 2 * ((n : ℝ) - 2) * (∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ - e) := by
  have hsymm : ∀ i j, ⟪x i, x j⟫ = ⟪x j, x i⟫ := fun i j => (real_inner_comm _ _).symm
  have hdiag : ∀ i, ⟪x i, x i⟫ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, hx i]; norm_num
  rw [dsum_sub, dsum_Rs hn s hs12 hs23 (fun i j => ⟪x i, x j⟫) hsymm hdiag,
    dsum_H hn H (e / (n.choose 2 : ℝ)) (fun i j => ⟪x i, x j⟫) hsymm]
  have hc : (n.choose 2 : ℝ) = n * (n - 1) / 2 := Nat.cast_choose_two ℝ n
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : ((n : ℝ) - 1) ≠ 0 := by intro h; linarith
  have hn0 : (n : ℝ) ≠ 0 := by intro h; linarith
  rw [hc]
  field_simp
  ring

end Kissing4
