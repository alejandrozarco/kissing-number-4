import Kissing4.Kernel
import Kissing4.Positivity  -- build order only: keeps `lake build` sequential on a shared machine

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):
-- `three_point_bound_of_forall4` from `ThreePoint.three_point_bound_cut` (the cut replaced by a predicate
-- and the positive-semidefiniteness hypothesis replaced by Bachoc–Vallentin positivity of the moment sum),
-- using `ThreePoint.three_point_identity` via `three_point_identity4`, `ThreePoint.gramOK_inner` via
-- `gramOK_inner4`, `ThreePoint.sum_matDot_Rk` via `sum_matDot_Rk4`.

/-!
# The three-point bound in `ℝ⁴` on a region of inner products

For `n` unit vectors of `ℝ⁴` whose pairwise inner products satisfy a predicate `P`, the certificate
inequality on `P`-Gram triples (for the `S³` block kernels `Rk4`) bounds the pair sum of `H`. Instead of
asking each block `F k` to be positive semidefinite, the Bachoc–Vallentin positivity of the moment sum
`∑ i j l, ⟨F k, S4 …⟩ ≥ 0` is taken as a hypothesis `hBV`; positivity on `S³` is proved elsewhere. The rest of
the argument combines the exact identity `three_point_identity4` with `dsum_nonneg`.
-/

open scoped RealInnerProductSpace

namespace Kissing4

open ThomsonN7 ThomsonN7.ThreePoint

/-- **Three-point bound on a region, `ℝ⁴` version.** If the certificate inequality holds on all Gram triples
satisfying `P`, and the moment sums of the blocks `F k` are nonnegative (`hBV`), then every configuration of
`n` unit vectors of `ℝ⁴` with pairwise inner products satisfying `P` has pair sum of `H` at least `e`. -/
theorem three_point_bound_of_forall4 {n : ℕ} (hn : 3 ≤ n) (P : ℝ → Prop) (K : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ)
    (H : ℝ → ℝ) (e : ℝ)
    (hpt : ∀ u v t : ℝ, GramOK u v t → P u → P v → P t →
      ∑ k ∈ Finset.range K, matDot (F k) (Rk4 n (m k) k u v t)
        ≤ (H u + H v + H t) / 3 - e / (n.choose 2 : ℝ))
    (x : Fin n → R4) (hx : ∀ i, ‖x i‖ = 1)
    (hBV : ∀ k, k < K → 0 ≤ ∑ i, ∑ j, ∑ l,
      matDot (F k) (S4 (m k) k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫))
    (hxP : ∀ i j, i ≠ j → P ⟪x i, x j⟫) :
    e ≤ ∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ := by
  -- the three-point function of the certificate and its symmetries
  set s : ℝ → ℝ → ℝ → ℝ := fun u v t => ∑ k ∈ Finset.range K, matDot (F k) (S4 (m k) k u v t)
    with hs
  have hs12 : ∀ u v t, s u v t = s v u t := fun u v t => by
    simp only [hs, S4_swap12 _ _ u v t]
  have hs23 : ∀ u v t, s u v t = s u t v := fun u v t => by
    simp only [hs, S4_swap23 _ _ u v t]
  -- positivity of the full triple sum, from the hypothesis on each block
  have hpos : 0 ≤ ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ := by
    simp only [hs]
    rw [sum4_swap]
    exact Finset.sum_nonneg fun k hk => hBV k (Finset.mem_range.mp hk)
  -- the pointwise inequality, on every triple of distinct points
  have hdist : 0 ≤ dsum (fun i j l => ((H ⟪x i, x j⟫ + H ⟪x i, x l⟫ + H ⟪x j, x l⟫) / 3
        - e / (n.choose 2 : ℝ)) - Rs s n ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) := by
    refine dsum_nonneg fun i j l hij hil hjl => ?_
    have h := hpt _ _ _ (gramOK_inner4 (x i) (x j) (x l) (hx i) (hx j) (hx l))
      (hxP i j hij) (hxP i l hil) (hxP j l hjl)
    rw [sum_matDot_Rk4] at h
    exact sub_nonneg.mpr h
  -- the identity turns both into `2 (n - 2) (∑ H - e) ≥ 0`
  have hid := three_point_identity4 hn s hs12 hs23 H e x hx
  have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hneg : 2 * ((n : ℝ) - 2) * (∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ - e) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) (by linarith)
  have hge : 0 ≤ ((n : ℝ) - 2) * ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ :=
    mul_nonneg hn2.le hpos
  linarith

end Kissing4
