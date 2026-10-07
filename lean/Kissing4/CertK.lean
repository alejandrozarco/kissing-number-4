import Kissing.CertK
import Kissing4.Positivity
import Kissing4.Bound

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):
-- `q4E` from `Cert.q3E`, `ev_q4E` from `Cert.ev_q3E`, `fk4E` from `Cert.fkE`, `ev_fk4E` from `Cert.ev_fkE`,
-- `matDot_fmat_Y4` from `Cert.matDot_fmat_Y3`, `matDot_S4` from `Cert.matDot_S3`, `key_F4` from `Cert.key_F`,
-- `CertK4` from `Cert.Cert3` (via `Kissing.CertK`), `CertK4.blk` from `Cert.Cert3.blk`,
-- `CertK4.m` from `Cert.Cert3.m`, `CertK4.K` from `Cert.Cert3.K`, `CertK4.Fm` from `Cert.Cert3.Fm`,
-- `CertK4.idE` from `Cert.Cert3.idE`, `CertK4.check` from `Cert.Cert3.check`,
-- `CertK4.check_parts` from `Cert.Cert3.check_parts`, `CertK4.hpt4` from `Cert.Cert3.hpt_gramCut`,
-- `kStat_idE4` from `Case1.c1Stat_idE`.

/-!
# An exact three-point certificate checker for kissing configurations in `ℝ⁴`

This is the four-dimensional counterpart of `Kissing.CertK`. The region `GramHalf`, the multiplier table
`codeK`, the SOS blocks `KBlk` and the data-independent machinery (`Kron.Ex`, `Cert.chk`, `Cert.Blk`, `Cert.sqfE`,
`Cert.ftotE`, `Case1.c1Stat`) are reused from there. What changes is the kernel: the `F`-part of the identity is
built from the `S³` kernel `Q4`, so this file adds its polynomial expression `q4E`, the block expressions `fk4E`,
and the link `key_F4` between `Rk4` and `ftotTerm`.

A certificate `cf : CertK4` has the same shape as in dimension 3, but its check additionally requires
`cf.K ≤ 8`: Bachoc–Vallentin positivity on `S³` is proved for degrees `k ≤ 7` only
(`Kissing4.matDot_moment_nonneg4`), and `no_config4` feeds it to `Kissing4.three_point_bound_of_forall4`.
A checked certificate with positive margin excludes `n` unit vectors of `ℝ⁴` with all pairwise inner products
at most `1/2`.
-/

open Real
open scoped RealInnerProductSpace

namespace Kissing4

open ThomsonN7 ThomsonN7.ThreePoint ThomsonN7.Kron ThomsonN7.Kron.Ex ThomsonN7.Cert
open Kissing

/-! ## The kernel `Q4` as a polynomial expression -/

/-- `Q4 k` as an expression with integer coefficients. -/
def q4E : ℕ → Ex
  | 0 => c 1
  | 1 => sub T (mul U V)
  | k + 2 => sub (smul (2 * (k : ℤ) + 3) (mul (sub T (mul U V)) (q4E (k + 1))))
      (smul (((k : ℤ) + 1) ^ 2) (mul (mul (sub (c 1) (Ex.sq U)) (sub (c 1) (Ex.sq V))) (q4E k)))

lemma ev_q4E (u v t : ℝ) : ∀ k, (q4E k).ev u v t = Q4 k u v t
  | 0 => by simp [q4E, Q4]
  | 1 => by simp [q4E, Q4]
  | k + 2 => by
    simp only [q4E, Q4, ev_sub, ev_mul, ev_smul, ev_T, ev_U, ev_V, ev_c, ev_sq,
      ev_q4E u v t (k + 1), ev_q4E u v t k]
    push_cast
    ring

/-! ## `F`-blocks against the kernel `Q4` -/

/-- `Λ · Fp_k(u,v,t)` for the `S³` kernel, where `Fp_k = ∑_{ab} F_{ab} uᵃ vᵇ Q4_k`. -/
def fk4E (r : ℕ) (b : Blk) (k : ℕ) : Ex := mul (fpE r b) (q4E k)

lemma ev_fk4E (r : ℕ) (b : Blk) (k : ℕ) (u v t : ℝ) :
    (fk4E r b k).ev u v t = ∑ a ∈ Finset.range r, ∑ c ∈ Finset.range r,
      (b.ent r a c : ℝ) * (u ^ a * v ^ c * Q4 k u v t) := by
  rw [fk4E, ev_mul, ev_fpE, ev_q4E, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma matDot_fmat_Y4 (r Lam : ℕ) (b : Blk) (k : ℕ) (u v t : ℝ) :
    matDot (fmat r Lam b) (Y4 r k u v t) = (fk4E r b k).ev u v t / Lam := by
  have h := sum_fin_eq_range r
    (fun a c => (b.ent r a c : ℝ) / Lam * (u ^ a * v ^ c * Q4 k u v t))
  simp only [matDot, fmat, Y4, Matrix.of_apply]
  refine h.trans ?_
  rw [ev_fk4E, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma matDot_S4 {m : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (k : ℕ) (x y z : ℝ) :
    matDot F (S4 m k x y z) = (1 / 6) * six (fun a b c => matDot F (Y4 m k a b c)) x y z := by
  simp only [S4, matDot_smul, matDot_add, six]

lemma key_F4 {r Lam : ℕ} (b : Blk) (k n : ℕ) (hL : (Lam : ℝ) ≠ 0) (hn : (n : ℝ) - 1 ≠ 0)
    (u v t : ℝ) :
    6 * ((n : ℝ) - 1) * Lam * matDot (fmat r Lam b) (Rk4 n r k u v t)
      = ftotTerm n (fun a b' c => (fk4E r b k).ev a b' c) u v t := by
  rw [matDot_Rk4]
  simp only [Rs, matDot_S4, matDot_fmat_Y4, six, ftotTerm]
  field_simp

/-! ## The certificate -/

/-- A kissing certificate for `n` points of `ℝ⁴`: margin `e = eps / Λ`, kernel blocks `F_k` (in the basis
`uᵃ vᵇ Q4_k`, `F_k = ent / Λ`) and SOS blocks, over the common denominator `Λ = Lam`. -/
structure CertK4 where
  n : ℕ
  Lam : ℕ
  eps : ℤ
  F : List Blk
  S : List Kissing.KBlk

namespace CertK4

/-- The `k`-th `F`-block. -/
def blk (cf : CertK4) (k : ℕ) : Blk := cf.F.getD k Blk.empty

/-- The size of the `k`-th `F`-block. -/
def m (cf : CertK4) (k : ℕ) : ℕ := (cf.blk k).Δ.length

/-- The number of `F`-blocks. -/
def K (cf : CertK4) : ℕ := cf.F.length

/-- The `k`-th `F`-matrix. -/
noncomputable def Fm (cf : CertK4) (k : ℕ) : Matrix (Fin (cf.m k)) (Fin (cf.m k)) ℝ :=
  fmat (cf.m k) cf.Lam (cf.blk k)

/-- The polynomial identity, scaled by `6 (n-1) C(n,2) Λ`, as an expression. -/
def idE (cf : CertK4) : Ex :=
  sub (sub (c (-(6 * ((cf.n : ℤ) - 1) * cf.eps)))
      (smul (cf.n.choose 2 : ℕ) (ftotE cf.n cf.K fun k => fk4E (cf.m k) (cf.blk k) k)))
    (smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ)) (sumE (cf.S.map kblkE)))

/-- The computable check; the bound `K ≤ 8` is the range of degrees for which positivity on `S³` is proved. -/
def check (cf : CertK4) : Bool :=
  decide (3 ≤ cf.n) && decide (0 < cf.Lam) && decide (cf.K ≤ 8) &&
  (List.range cf.K).all (fun k => (cf.blk k).ok (cf.m k)) &&
  cf.S.all (fun s => s.B.ok s.z.length) && chk cf.idE

lemma check_parts {cf : CertK4} (h : cf.check = true) :
    3 ≤ cf.n ∧ 0 < cf.Lam ∧ cf.K ≤ 8 ∧ (∀ k < cf.K, (cf.blk k).ok (cf.m k) = true) ∧
    (cf.S.all (fun s => s.B.ok s.z.length) = true) ∧ chk cf.idE = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, hK⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, hK, fun k hk => ?_, h4, h5⟩
  exact (List.all_eq_true.mp h3) k (List.mem_range.mpr hk)

/-- The pointwise inequality on `GramHalf`. -/
lemma hpt4 (cf : CertK4) (hc : cf.check = true) {u v t : ℝ} (hg : GramHalf u v t) :
    ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk4 cf.n (cf.m k) k u v t)
      ≤ ((0 : ℝ) + 0 + 0) / 3 - ((cf.eps : ℝ) / cf.Lam) / (cf.n.choose 2 : ℕ) := by
  obtain ⟨hn, hL, hK, hF, hS, hz⟩ := check_parts hc
  have hev := chk_sound hz u v t
  simp only [idE, ev_sub, ev_smul, ev_c, ev_ftotE, ev_sumE] at hev
  have hnr : (3 : ℝ) ≤ cf.n := by exact_mod_cast hn
  have hn1 : (cf.n : ℝ) - 1 ≠ 0 := by
    have : (0 : ℝ) < (cf.n : ℝ) - 1 := by linarith
    exact this.ne'
  have hLpos : (0 : ℝ) < cf.Lam := by exact_mod_cast hL
  have hC : (0 : ℝ) < (cf.n.choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hFp : ∑ k ∈ Finset.range cf.K,
        ftotTerm cf.n (fun a b c => (fk4E (cf.m k) (cf.blk k) k).ev a b c) u v t
      = 6 * ((cf.n : ℝ) - 1) * cf.Lam
        * ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk4 cf.n (cf.m k) k u v t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (key_F4 (cf.blk k) k cf.n hLpos.ne' hn1 u v t).symm
  rw [hFp] at hev
  push_cast at hev
  exact Kissing.CertK.final_le hnr hC hLpos (kblk_sum_nonneg cf.S hS hg) hev

/-- **Soundness.** A checked certificate with positive margin excludes every configuration of `n` unit vectors in
`ℝ⁴` with all pairwise inner products at most `1/2`. -/
theorem no_config4 (cf : CertK4) (hc : cf.check = true) (heps : 0 < cf.eps) (x : Fin cf.n → R4)
    (hx : ∀ i, ‖x i‖ = 1) (hhalf : ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 1 / 2) : False := by
  obtain ⟨hn, hL, hK, hF, hS, hz⟩ := check_parts hc
  have hb := three_point_bound_of_forall4 hn (fun s => 2 * s ≤ 1) cf.K cf.m cf.Fm
    (fun _ => 0) ((cf.eps : ℝ) / cf.Lam)
    (fun u v t hg hu hv ht => hpt4 cf hc ⟨hg, hu, hv, ht⟩) x hx
    (fun k hk => matDot_moment_nonneg4 (cf.m k) k (by omega) x hx (cf.Fm k)
      (fmat_psd cf.Lam (hF k hk)))
    (fun i j hij => by have := hhalf i j hij; linarith)
  simp only [Finset.sum_const_zero] at hb
  have hpos : (0 : ℝ) < (cf.eps : ℝ) / cf.Lam :=
    div_pos (by exact_mod_cast heps) (by exact_mod_cast hL)
  linarith

end CertK4

/-! ## Chunked statistics of the identity (for the Kronecker check) -/

open ThomsonN7.Case1 in
/-- The statistics of `cf.idE`, in terms of those of its pieces (cf. upstream `Case1.c1Stat_idE`). -/
lemma kStat_idE4 (cf : CertK4) (w D : ℕ) :
    c1Stat w D cf.idE =
      c1Sub (c1Sub (c1C (-(6 * ((cf.n : ℤ) - 1) * cf.eps)))
        (c1Smul (cf.n.choose 2 : ℕ) (c1Sum ((List.range cf.K).map fun k =>
          c1Stat w D (c1FtotK cf.n (fk4E (cf.m k) (cf.blk k) k))))))
        (c1Smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ))
          (c1Sum (cf.S.map fun s => c1Stat w D (kblkE s)))) := by
  simp only [CertK4.idE, c1Stat_sub, c1Stat_smul, c1Stat_c, c1_ftotE_eq, c1Stat_sumRange,
    c1Stat_sumE, List.map_map]
  rfl

end Kissing4
