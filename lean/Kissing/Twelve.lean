import Mathlib
import Kissing.Cert.Check  -- build order only: keeps `lake build` sequential on a shared machine

/-!
# Twelve kissing balls in `ℝ³`

Twelve points with rational coordinates, each at distance exactly `2` from the origin and at distance at least `2`
from each other. They are rational approximations of the vertices of a regular icosahedron, scaled to radius `2`
(two poles and two rings of five), chosen on the sphere via rational parametrisations so that the norms are exact.
The regular icosahedron has slack (its pairwise inner products, for unit vectors, are at most `1/√5 < 1/2`), and
the approximations keep the minimum squared distance at `≈ 4.16 > 4`. Everything is checked in integer arithmetic
over the common denominator `L`.
-/

open scoped RealInnerProductSpace

namespace Kissing
namespace Twelve

/-- The common denominator. -/
def L : ℤ := 53563671

/-- The numerators: point `i` is `P i / L`. -/
def P : Fin 12 → Fin 3 → ℤ :=
  ![![0, 0, 107127342],
    ![0, 0, -107127342],
    ![96294240, 0, 46943442],
    ![30607812, 91823436, 45911718],
    ![-77035392, 57776544, 46943442],
    ![-77035392, -57776544, 46943442],
    ![30607812, -91823436, 45911718],
    ![75482680, 58063600, -49063742],
    ![-30607812, 91823436, -45911718],
    ![-95632992, 0, -48276270],
    ![-30607812, -91823436, -45911718],
    ![75482680, -58063600, -49063742]]

theorem P_norm : ∀ i, P i 0 ^ 2 + P i 1 ^ 2 + P i 2 ^ 2 = 4 * L ^ 2 := by
  decide +kernel

theorem P_sep : ∀ i j, i ≠ j →
    4 * L ^ 2 ≤ (P i 0 - P j 0) ^ 2 + (P i 1 - P j 1) ^ 2 + (P i 2 - P j 2) ^ 2 := by
  decide +kernel

/-- The `i`-th point. -/
noncomputable def pt (i : Fin 12) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun k => (P i k : ℝ) / L

lemma L_pos : (0 : ℝ) < L := by
  unfold L
  norm_num

/-- A point of `ℝ³` whose squared coordinates sum to `4` has norm `2`. -/
lemma norm_eq_two {x : EuclideanSpace ℝ (Fin 3)} (h : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 4) : ‖x‖ = 2 := by
  have hs : ‖x‖ ^ 2 = 4 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    exact h
  nlinarith [norm_nonneg x]

/-- Two points of `ℝ³` whose squared coordinate differences sum to at least `4` are at least `2` apart. -/
lemma two_le_dist {x y : EuclideanSpace ℝ (Fin 3)}
    (h : 4 ≤ (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 + (x 2 - y 2) ^ 2) : 2 ≤ dist x y := by
  rw [dist_eq_norm]
  have hs : 4 ≤ ‖x - y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    simpa only [PiLp.sub_apply] using h
  nlinarith [norm_nonneg (x - y)]

theorem norm_pt (i : Fin 12) : ‖pt i‖ = 2 := by
  apply norm_eq_two
  simp only [pt, PiLp.toLp_apply]
  have h : ((P i 0 : ℝ)) ^ 2 + (P i 1 : ℝ) ^ 2 + (P i 2 : ℝ) ^ 2 = 4 * (L : ℝ) ^ 2 := by
    exact_mod_cast P_norm i
  have hL := L_pos
  rw [div_pow, div_pow, div_pow, ← add_div, ← add_div, h]
  field_simp

theorem dist_pt (i j : Fin 12) (hij : i ≠ j) : 2 ≤ dist (pt i) (pt j) := by
  apply two_le_dist
  simp only [pt, PiLp.toLp_apply]
  have h : 4 * (L : ℝ) ^ 2 ≤ ((P i 0 : ℝ) - P j 0) ^ 2 + ((P i 1 : ℝ) - P j 1) ^ 2
      + ((P i 2 : ℝ) - P j 2) ^ 2 := by
    exact_mod_cast P_sep i j hij
  have hL := L_pos
  rw [div_sub_div_same, div_sub_div_same, div_sub_div_same, div_pow, div_pow, div_pow, ← add_div,
    ← add_div, le_div_iff₀ (by positivity)]
  linarith

theorem pt_injective : Function.Injective pt := by
  intro i j h
  by_contra hij
  have := dist_pt i j hij
  rw [h, dist_self] at this
  norm_num at this

end Twelve
end Kissing
