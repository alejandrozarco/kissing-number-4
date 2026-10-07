import ThomsonGen.ThreePoint

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):
-- `three_point_bound_of_forall` from `ThreePoint.three_point_bound_cut` (the cut replaced by a predicate).

/-!
# The three-point bound on a region of inner products

Upstream's `ThomsonN7.ThreePoint.three_point_bound_cut` (huwngtran/thomson-n7-lean) requires the pointwise
inequality only on Gram triples whose entries are all `≥ a`. Kissing configurations need the opposite
restriction (all inner products `≤ 1/2`), so here the cut is replaced by an arbitrary predicate `P` that holds
for every off-diagonal inner product of the configuration. The proof combines upstream's exact three-point
identity (`three_point_identity`), Bachoc–Vallentin positivity (`matDot_moment_nonneg`) and the
nonnegativity of sums over distinct triples (`dsum_nonneg`); the argument is that of upstream's cut version.
-/

open Real
open scoped RealInnerProductSpace

namespace Kissing

open ThomsonN7 ThomsonN7.ThreePoint

/-- **Three-point bound on a region.** If the certificate inequality holds on all Gram triples whose entries
satisfy `P`, then it bounds every configuration of `n` unit vectors whose pairwise inner products satisfy `P`. -/
theorem three_point_bound_of_forall {n : ℕ} (hn : 3 ≤ n) (P : ℝ → Prop) (K : ℕ) (m : ℕ → ℕ)
    (F : (k : ℕ) → Matrix (Fin (m k)) (Fin (m k)) ℝ) (hF : ∀ k, k < K → (F k).PosSemidef)
    (H : ℝ → ℝ) (e : ℝ)
    (hpt : ∀ u v t : ℝ, GramOK u v t → P u → P v → P t →
      ∑ k ∈ Finset.range K, matDot (F k) (Rk n (m k) k u v t)
        ≤ (H u + H v + H t) / 3 - e / (n.choose 2 : ℝ))
    (x : Fin n → R3) (hx : ∀ i, ‖x i‖ = 1) (hxP : ∀ i j, i ≠ j → P ⟪x i, x j⟫) :
    e ≤ ∑ i, ∑ j ∈ Finset.Ioi i, H ⟪x i, x j⟫ := by
  -- the three-point function of the certificate and its symmetries
  set s : ℝ → ℝ → ℝ → ℝ := fun u v t => ∑ k ∈ Finset.range K, matDot (F k) (S3 (m k) k u v t)
    with hs
  have hs12 : ∀ u v t, s u v t = s v u t := fun u v t => by
    simp only [hs, S3_swap12 _ _ u v t]
  have hs23 : ∀ u v t, s u v t = s u t v := fun u v t => by
    simp only [hs, S3_swap23 _ _ u v t]
  -- Bachoc–Vallentin positivity of the full triple sum
  have hpos : 0 ≤ ∑ i, ∑ j, ∑ l, s ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫ := by
    simp only [hs]
    rw [sum4_swap]
    exact Finset.sum_nonneg fun k hk =>
      matDot_moment_nonneg (m k) k x hx (F k) (hF k (Finset.mem_range.mp hk))
  -- the pointwise inequality, on every triple of distinct points
  have hdist : 0 ≤ dsum (fun i j l => ((H ⟪x i, x j⟫ + H ⟪x i, x l⟫ + H ⟪x j, x l⟫) / 3
        - e / (n.choose 2 : ℝ)) - Rs s n ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) := by
    refine dsum_nonneg fun i j l hij hil hjl => ?_
    have h := hpt _ _ _ (gramOK_inner (x i) (x j) (x l) (hx i) (hx j) (hx l))
      (hxP i j hij) (hxP i l hil) (hxP j l hjl)
    rw [sum_matDot_Rk] at h
    exact sub_nonneg.mpr h
  -- the identity turns both into `2 (n - 2) (∑ H - e) ≥ 0`
  have hid := three_point_identity hn s hs12 hs23 H e x hx
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

end Kissing
