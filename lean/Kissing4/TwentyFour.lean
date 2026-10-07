import Mathlib
import Kissing4.Cert.Check  -- build order only: keeps `lake build` sequential on a shared machine

/-!
# Twenty-four kissing balls in `ℝ⁴`

Twenty-four points with integer coordinates, each at distance exactly `2` from the origin and at distance at
least `2` from each other. They are the vertices of the 24-cell scaled to radius `2`: the eight points
`±2 eᵢ` and the sixteen points `(±1, ±1, ±1, ±1)`. Everything is checked in integer arithmetic.
-/

namespace Kissing4
namespace TwentyFour

/-- The coordinates of the `i`-th point. -/
def P : Fin 24 → Fin 4 → ℤ :=
  ![![2, 0, 0, 0],
    ![-2, 0, 0, 0],
    ![0, 2, 0, 0],
    ![0, -2, 0, 0],
    ![0, 0, 2, 0],
    ![0, 0, -2, 0],
    ![0, 0, 0, 2],
    ![0, 0, 0, -2],
    ![1, 1, 1, 1],
    ![1, 1, 1, -1],
    ![1, 1, -1, 1],
    ![1, 1, -1, -1],
    ![1, -1, 1, 1],
    ![1, -1, 1, -1],
    ![1, -1, -1, 1],
    ![1, -1, -1, -1],
    ![-1, 1, 1, 1],
    ![-1, 1, 1, -1],
    ![-1, 1, -1, 1],
    ![-1, 1, -1, -1],
    ![-1, -1, 1, 1],
    ![-1, -1, 1, -1],
    ![-1, -1, -1, 1],
    ![-1, -1, -1, -1]]

theorem P_norm : ∀ i, P i 0 ^ 2 + P i 1 ^ 2 + P i 2 ^ 2 + P i 3 ^ 2 = 4 := by
  decide +kernel

theorem P_sep : ∀ i j, i ≠ j →
    4 ≤ (P i 0 - P j 0) ^ 2 + (P i 1 - P j 1) ^ 2 + (P i 2 - P j 2) ^ 2 + (P i 3 - P j 3) ^ 2 := by
  decide +kernel

/-- The `i`-th point. -/
noncomputable def pt (i : Fin 24) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 fun k => (P i k : ℝ)

/-- A point of `ℝ⁴` whose squared coordinates sum to `4` has norm `2`. -/
lemma norm_eq_two {x : EuclideanSpace ℝ (Fin 4)}
    (h : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = 4) : ‖x‖ = 2 := by
  have hs : ‖x‖ ^ 2 = 4 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    exact h
  nlinarith [norm_nonneg x]

/-- Two points of `ℝ⁴` whose squared coordinate differences sum to at least `4` are at least `2` apart. -/
lemma two_le_dist {x y : EuclideanSpace ℝ (Fin 4)}
    (h : 4 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2 + (x 3 - y 3) ^ 2) :
    2 ≤ dist x y := by
  rw [dist_eq_norm]
  have hs : 4 ≤ ‖x - y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four]
    simpa only [PiLp.sub_apply] using h
  nlinarith [norm_nonneg (x - y)]

theorem norm_pt (i : Fin 24) : ‖pt i‖ = 2 := by
  apply norm_eq_two
  simp only [pt, PiLp.toLp_apply]
  exact_mod_cast P_norm i

theorem dist_pt (i j : Fin 24) (hij : i ≠ j) : 2 ≤ dist (pt i) (pt j) := by
  apply two_le_dist
  simp only [pt, PiLp.toLp_apply]
  exact_mod_cast P_sep i j hij

theorem pt_injective : Function.Injective pt := by
  intro i j h
  by_contra hij
  have := dist_pt i j hij
  rw [h, dist_self] at this
  norm_num at this

end TwentyFour
end Kissing4
