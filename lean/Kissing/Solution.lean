import Mathlib
import Kissing.Twelve
import Kissing.Cert.Check

/-!
# The kissing number in dimension 3 is 12: proofs

The definitions below repeat `Kissing/Statement.lean` verbatim; the theorems carry the same names and statements,
now with proofs (Comparator checks this: `comparator.json`).

* Lower bound: twelve explicit rational points (`Kissing.Twelve`).
* Upper bound: thirteen points of a kissing arrangement, scaled to unit vectors, would have pairwise inner products
  `≤ 1/2`; the exact three-point certificate `Kissing.Cert.cf` (checked by `decide +kernel`) rules that out
  (`Kissing.CertK.no_config`).
-/

namespace Kissing

/-- Points of `ℝ^d` with the usual (Euclidean) distance. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- `S` is a kissing arrangement in `ℝ^d`: `S` is a set of centres of unit balls, each touching the
central unit ball at the origin (`‖x‖ = 2`), with no two overlapping (`2 ≤ dist x y` for `x ≠ y`).
`S` may be infinite here; the theorems below rule that out in dimension 3. -/
def IsKissing {d : ℕ} (S : Set (E d)) : Prop :=
  (∀ x ∈ S, ‖x‖ = 2) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 2 ≤ dist x y

/-- The kissing number of `ℝ^d`: the supremum of the sizes of kissing arrangements. Sizes are counted
in `ℕ∞` (`Set.encard`), so an infinite arrangement would make it `⊤`; nothing is truncated. -/
noncomputable def kissingNumber (d : ℕ) : ℕ∞ :=
  ⨆ (S : Set (E d)) (_ : IsKissing S), S.encard

open scoped RealInnerProductSpace

/-! ## Main results -/

/-- **Lower bound.** There is a kissing arrangement of 12 balls in `ℝ³` (the vertices of a regular
icosahedron). -/
theorem exists_isKissing_encard_eq_twelve : ∃ S : Set (E 3), IsKissing S ∧ S.encard = 12 := by
  refine ⟨Set.range Twelve.pt, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact Twelve.norm_pt i
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    exact Twelve.dist_pt i j fun h => hij (h ▸ rfl)
  · rw [← Set.image_univ, Twelve.pt_injective.encard_image, Set.encard_univ]
    simp

/-- Thirteen points of a kissing arrangement in `ℝ³` cannot exist: halved, they would be unit vectors with
pairwise inner products `≤ 1/2`, which the certificate excludes. -/
lemma no_thirteen (S : Set (E 3)) (hS : IsKissing S) (x : Fin 13 → E 3) (hxS : ∀ i, x i ∈ S)
    (hxinj : Function.Injective x) : False := by
  set y : Fin 13 → E 3 := fun i => (1 / 2 : ℝ) • x i with hydef
  have hy : ∀ i, ‖y i‖ = 1 := by
    intro i
    simp only [hydef, norm_smul, hS.1 _ (hxS i)]
    norm_num
  have hyy : ∀ i j, i ≠ j → ⟪y i, y j⟫ ≤ 1 / 2 := by
    intro i j hij
    have hd := hS.2 _ (hxS i) _ (hxS j) fun h => hij (hxinj h)
    rw [dist_eq_norm] at hd
    have h1 := norm_sub_sq_real (x i) (x j)
    rw [hS.1 _ (hxS i), hS.1 _ (hxS j)] at h1
    have h2 : 4 ≤ ‖x i - x j‖ ^ 2 := by nlinarith [norm_nonneg (x i - x j)]
    simp only [hydef, real_inner_smul_left, real_inner_smul_right]
    nlinarith
  exact Cert.cf.no_config Cert.cf_ok Cert.cf_eps_pos (fun i => y (Fin.cast Cert.cf_n i))
    (fun i => hy _) fun i j hij => hyy _ _ fun h => hij (Fin.cast_injective _ h)

/-- **Upper bound.** Every kissing arrangement in `ℝ³` has at most 12 balls (in particular it is
finite). -/
theorem encard_le_twelve_of_isKissing (S : Set (E 3)) (hS : IsKissing S) : S.encard ≤ 12 := by
  by_contra hlt
  replace hlt := not_le.mp hlt
  have h13 : ((13 : ℕ) : ℕ∞) ≤ S.encard := by
    have := Order.add_one_le_of_lt hlt
    norm_num at this ⊢
    exact this
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq h13
  have htf : t.Finite := Set.finite_of_encard_eq_coe htc
  have hcard : htf.toFinset.card = 13 := by
    have h := htf.encard_eq_coe_toFinset_card
    rw [htc] at h
    exact_mod_cast h.symm
  set e := Finset.equivFinOfCardEq hcard
  exact no_thirteen S hS (fun i => ((e.symm i : htf.toFinset) : E 3))
    (fun i => hts ((Set.Finite.mem_toFinset htf).mp (e.symm i).2))
    fun i j h => e.symm.injective (Subtype.ext h)

/-- **The kissing number in dimension 3 is 12.** -/
theorem kissingNumber_three : kissingNumber 3 = 12 := by
  unfold kissingNumber
  apply le_antisymm
  · exact iSup₂_le fun S hS => encard_le_twelve_of_isKissing S hS
  · obtain ⟨S, hS, hc⟩ := exists_isKissing_encard_eq_twelve
    calc (12 : ℕ∞) = S.encard := hc.symm
      _ ≤ ⨆ (S : Set (E 3)) (_ : IsKissing S), S.encard :=
        le_iSup₂ (f := fun (S : Set (E 3)) (_ : IsKissing S) => S.encard) S hS

/-! ## Sanity checks of the definition (unit tests for the statement)

These are not used by the main results. They check that `IsKissing` is neither vacuous nor too weak:
the icosahedron above already shows it can hold for 12 points; the tests below show that it holds for
two opposite balls, fails for two overlapping ones, and fails for a ball that does not touch the central one. -/

/-- Two balls on opposite sides of the central ball form a kissing arrangement. -/
theorem isKissing_antipodal :
    IsKissing ({EuclideanSpace.single 0 2, EuclideanSpace.single 0 (-2)} : Set (E 3)) := by
  constructor
  · intro x hx
    rcases hx with rfl | rfl <;> apply Twelve.norm_eq_two <;> simp <;> norm_num
  · intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · apply Twelve.two_le_dist; simp; norm_num
    · apply Twelve.two_le_dist; simp; norm_num
    · exact absurd rfl hxy

/-- Two balls touching the central ball at 30° from each other overlap, so they do not form a kissing
arrangement: their centres `(2, 0, 0)` and `(√3, 1, 0)` are about `1.04 < 2` apart. -/
theorem not_isKissing_close :
    ¬ IsKissing ({!₂[2, 0, 0], !₂[√3, 1, 0]} : Set (E 3)) := by
  intro h
  have hne : (!₂[2, 0, 0] : E 3) ≠ !₂[√3, 1, 0] := by
    intro he
    have := congrArg (fun z : E 3 => z 1) he
    simp at this
  have hd := h.2 _ (Set.mem_insert _ _) _ (Set.mem_insert_of_mem _ rfl) hne
  rw [dist_eq_norm] at hd
  have hs : ‖(!₂[2, 0, 0] : E 3) - !₂[√3, 1, 0]‖ ^ 2 = (2 - √3) ^ 2 + 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simp
  have h3 : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3' : 1 < √3 := by
    rw [show (1 : ℝ) = √1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  nlinarith [norm_nonneg ((!₂[2, 0, 0] : E 3) - !₂[√3, 1, 0])]

/-- A ball whose centre is at distance `3` from the origin does not touch the central ball, so it does not
form a kissing arrangement. -/
theorem not_isKissing_far : ¬ IsKissing ({EuclideanSpace.single 0 3} : Set (E 3)) := by
  intro h
  have h1 := h.1 _ (Set.mem_singleton _)
  norm_num at h1

end Kissing
