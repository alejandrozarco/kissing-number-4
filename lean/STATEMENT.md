# What the Lean statement says, in plain English

File: `lean/Kissing/Statement.lean` (claims only; proofs are `sorry` there and are supplied by the proof files).
Compiles with Lean v4.34.1 and the pinned Mathlib; the only warnings are the `sorry`s.

| Lean | Plain English |
|---|---|
| `E d := EuclideanSpace ℝ (Fin d)` | Ordinary d-dimensional space with ordinary distance. |
| `IsKissing S`: `∀ x ∈ S, ‖x‖ = 2` | Every outer ball (radius 1, centre `x`) touches the central ball (radius 1, centre 0): the centres are 2 apart. |
| `IsKissing S`: `∀ x y ∈ S, x ≠ y → 2 ≤ dist x y` | No two outer balls overlap: their centres are at least 2 apart (touching is allowed). |
| `kissingNumber d := ⨆ (S : Set (E d)) (_ : IsKissing S), S.encard` | The kissing number is the largest number of outer balls that fit. Infinite counts are allowed, so nothing is cut off silently. |
| `exists_isKissing_encard_eq_twelve` | 12 balls fit around one in 3D (rational approximations of the icosahedron vertices). |
| `encard_le_twelve_of_isKissing` | Any arrangement in 3D has at most 12 balls. Infinite arrangements are covered and ruled out too. |
| `kissingNumber_three : kissingNumber 3 = 12` | The kissing number in 3D is exactly 12. |
| `isKissing_antipodal` (test) | Two balls on opposite sides do count as an arrangement, so the definition is not impossible to satisfy. |
| `not_isKissing_close` (test) | Two balls only $`30^\circ`$ apart overlap and do not count, so the distance rule really bites. |
| `not_isKissing_far` (test) | A ball whose centre is 3 away does not touch the central ball and does not count, so the touching rule bites too. |

Points worth a second look:
- The definition counts sets of centres. "Ball" and "sphere" do not matter here: touching unit balls and touching unit
  spheres give the same condition.
- The proof will use the equivalent form "unit vectors with pairwise inner products at most $`1/2`$" (divide the centres by 2).
  That conversion is proved in Lean; it is not assumed.
