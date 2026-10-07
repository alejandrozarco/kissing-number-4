import Kissing.CertK
import Kissing4.CertK  -- build order only: keeps `lake build` sequential on a shared machine

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):
-- `okRow` from `Cert.Blk.ok` (one row of it); `sqT`, `delR` from the summands of `Cert.sqfE`.

/-!
# Row chunks for the kernel checks of large blocks

A single `decide +kernel` of `Blk.ok` or of the Kronecker statistics of an SOS block of size `r` costs memory
roughly proportional to `r³` (every entry access walks a list). For the large blocks of the dimension-4
certificate these lemmas let the generated modules check the same Booleans and statistics in chunks of rows, one
kernel `decide` per chunk, with nothing changed in what is checked:

* `c1Sum_append`: the statistics of a concatenated list of pieces combine with `c1Add`;
* `c1Stat_kblkE`: the statistics of an SOS block are those of its multiplier times the sum over the rows `q` of
  the `L D Lᵀ` part and the rows `a` of the remainder `Δ`;
* `range_eq_range'_append`: splitting `List.range` into consecutive pieces;
* `okRow`, `ok_eq_all_okRow`: `Blk.ok` as a conjunction over rows.
-/

open ThomsonN7 ThomsonN7.Kron ThomsonN7.Kron.Ex ThomsonN7.Cert ThomsonN7.Case1

namespace Kissing4

theorem c1Add_c1C_zero (s : C1Stat) : c1Add (c1C 0) s = s := by
  obtain ⟨a, b, c, d, e⟩ := s
  simp [c1Add, c1C]

theorem c1Add_assoc (s t u : C1Stat) : c1Add (c1Add s t) u = c1Add s (c1Add t u) := by
  obtain ⟨a, b, c, d, e⟩ := s
  obtain ⟨a', b', c', d', e'⟩ := t
  obtain ⟨a'', b'', c'', d'', e''⟩ := u
  simp only [c1Add, Prod.mk.injEq]
  refine ⟨by ring, max_assoc _ _ _, max_assoc _ _ _, max_assoc _ _ _, by ring⟩

/-- The statistics of a concatenation. -/
theorem c1Sum_append (l₁ l₂ : List C1Stat) : c1Sum (l₁ ++ l₂) = c1Add (c1Sum l₁) (c1Sum l₂) := by
  induction l₁ with
  | nil => simp [c1Sum, c1Add_c1C_zero]
  | cons x l ih =>
    show c1Add x (c1Sum (l ++ l₂)) = c1Add (c1Add x (c1Sum l)) (c1Sum l₂)
    rw [ih, c1Add_assoc]

/-- The `q`-th square of the `L D Lᵀ` part of an SOS block, as it occurs in `Cert.sqfE`. -/
def sqT (b : Blk) (zs : List (ℕ × ℕ × ℕ)) (q : ℕ) : Ex :=
  smulNZ (b.dq q) (Ex.sq (sumRange zs.length fun a => smulNZ (b.lq q a) (zmon zs a)))

/-- The `a`-th row of the remainder part of an SOS block, as it occurs in `Cert.sqfE`. -/
def delR (b : Blk) (zs : List (ℕ × ℕ × ℕ)) (a : ℕ) : Ex :=
  sumRange zs.length fun c => smulNZ (b.del a c) (zzmon zs a c)

/-- The statistics of an SOS block, row by row. -/
theorem c1Stat_kblkE (w D : ℕ) (s : Kissing.KBlk) :
    c1Stat w D (Kissing.kblkE s) =
      c1Mul (c1Stat w D (Kissing.gKE s.g))
        (c1Add (c1Sum ((List.range s.z.length).map fun q => c1Stat w D (sqT s.B s.z q)))
          (c1Sum ((List.range s.z.length).map fun a => c1Stat w D (delR s.B s.z a)))) := by
  show c1Mul _ (c1Add (c1Stat w D (sumRange _ _)) (c1Stat w D (sumRange _ _))) = _
  rw [c1Stat_sumRange, c1Stat_sumRange]
  rfl

/-- `List.range` as consecutive pieces. -/
theorem range_eq_range'_append (a b : ℕ) : List.range (a + b) = List.range' 0 a ++ List.range' a b := by
  have h := (List.range'_append (s := 0) (m := a) (n := b) (step := 1)).symm
  simpa [List.range_eq_range'] using h

/-- The row-`i` part of `Cert.Blk.ok`. -/
def okRow (r : ℕ) (b : Blk) (i : ℕ) : Bool :=
  decide (0 ≤ b.dq i) &&
    (List.range r).all (fun j => decide (b.del i j = b.del j i)) &&
    decide (((List.range r).map fun j => if i = j then (0 : ℤ) else |b.del i j|).sum ≤ b.del i i)

/-- `Blk.ok` is the conjunction of its rows. -/
theorem ok_eq_all_okRow (r : ℕ) (b : Blk) : b.ok r = (List.range r).all (okRow r b) := rfl

end Kissing4
