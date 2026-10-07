import Mathlib

/-!
# The kissing number in dimension 3 is 12: statement

This file holds the claims only, with every proof replaced by `sorry`. It is the reference (challenge) file
for Comparator: the proof files must prove these exact statements. Everything is phrased in plain Mathlib
vocabulary (`EuclideanSpace`, `‖·‖`, `dist`, `Set.encard`), with no home-made notions beyond `IsKissing`
and `kissingNumber`, which are defined here.

Picture: a central ball of radius 1 at the origin, and other balls of radius 1 around it. Each one
touches the central ball, so its centre is at distance 2 from the origin. No two of them overlap, so
their centres are at least 2 apart (touching is allowed). The kissing number is the largest possible
number of such outer balls.
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

/-! ## Main results -/

/-- **Lower bound.** There is a kissing arrangement of 12 balls in `ℝ³` (the vertices of a regular
icosahedron). -/
theorem exists_isKissing_encard_eq_twelve : ∃ S : Set (E 3), IsKissing S ∧ S.encard = 12 := by
  sorry

/-- **Upper bound.** Every kissing arrangement in `ℝ³` has at most 12 balls (in particular it is
finite). -/
theorem encard_le_twelve_of_isKissing (S : Set (E 3)) (hS : IsKissing S) : S.encard ≤ 12 := by
  sorry

/-- **The kissing number in dimension 3 is 12.** -/
theorem kissingNumber_three : kissingNumber 3 = 12 := by
  sorry

/-! ## Sanity checks of the definition (unit tests for the statement)

These are not used by the main results. They check that `IsKissing` is neither vacuous nor too weak:
the icosahedron above already shows it can hold for 12 points; the tests below show that it holds for
two opposite balls, fails for two overlapping ones, and fails for a ball that does not touch the central one. -/

/-- Two balls on opposite sides of the central ball form a kissing arrangement. -/
theorem isKissing_antipodal :
    IsKissing ({EuclideanSpace.single 0 2, EuclideanSpace.single 0 (-2)} : Set (E 3)) := by
  sorry

/-- Two balls touching the central ball at 30° from each other overlap, so they do not form a kissing
arrangement: their centres `(2, 0, 0)` and `(√3, 1, 0)` are about `1.04 < 2` apart. -/
theorem not_isKissing_close :
    ¬ IsKissing ({!₂[2, 0, 0], !₂[√3, 1, 0]} : Set (E 3)) := by
  sorry

/-- A ball whose centre is at distance `3` from the origin does not touch the central ball, so it does not
form a kissing arrangement. -/
theorem not_isKissing_far : ¬ IsKissing ({EuclideanSpace.single 0 3} : Set (E 3)) := by
  sorry

end Kissing
