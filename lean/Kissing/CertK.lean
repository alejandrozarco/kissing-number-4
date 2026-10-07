import ThomsonGen.Case1Stat
import ThomsonGen.CertF
import Kissing.Bound

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):
-- `codeK`, `codeK_nonneg` from `Cert.codeE`, `Cert.codeE_nonneg` (new multipliers for the region);
-- `gKE`, `gKE_nonneg` from `Cert.gE`, `Cert.gE_nonneg`; `KBlk`, `kblkE`, `kblkE_nonneg` from `Cert.SBlk`,
-- `Cert.sblkE`, `Cert.sblkE_nonneg` (no variable permutation); `kblk_sum_nonneg` from `Cert.sos_sum_nonneg`;
-- `CertK` from `Cert.Cert3` (no cut, no minorant); `CertK.blk` from `Cert.Cert3.blk`, `CertK.m` from `Cert.Cert3.m`,
-- `CertK.K` from `Cert.Cert3.K`, `CertK.Fm` from `Cert.Cert3.Fm`, `CertK.idE` from `Cert.Cert3.idE`,
-- `CertK.check` from `Cert.Cert3.check`, `CertK.check_parts` from `Cert.Cert3.check_parts`,
-- `CertK.final_le` from `Cert.final_ineq`, `CertK.hpt` from `Cert.Cert3.hpt_gramCut`; `kStat_idE` from
-- `Case1.c1Stat_idE`.

/-!
# An exact three-point certificate checker for kissing configurations

Upstream's `ThomsonN7.Cert.Cert3` (huwngtran/thomson-n7-lean) checks a three-point certificate on Gram
triples with a lower cut `a ≤ u, v, t`. A kissing configuration needs the region
`GramHalf = {GramOK, u, v, t ≤ 1/2}` instead, so this file defines its own multiplier table `codeK`, SOS
blocks `KBlk` and certificate `CertK`, and reuses upstream's data-independent machinery unchanged:
polynomial expressions `Kron.Ex` with the exact Kronecker test `Cert.chk`, the integer PSD blocks
`Cert.Blk` (an `L D Lᵀ` part and a diagonally dominant part), the `F`-part of the identity
(`Cert.fkE`, `Cert.ftotE`, `Cert.key_F`), the quadratic forms `Cert.sqfE`, and the chunked statistics
`Case1.c1Stat`.

A certificate `cf` encodes, over the common denominator `Λ = cf.Lam`, kernel blocks `F_k` and SOS blocks
`(g_r, z_r, M_r)` with the polynomial identity (in `ℤ[u, v, t]`, checked by `chk`)
`-6(n-1)·eps - C(n,2)·ftot - 6(n-1)·C(n,2)·∑_r g_r · z_rᵀ M_r z_r = 0`,
where `ftot = 6(n-1)Λ ∑_k ⟨F_k, R_k⟩`. On `GramHalf` every `g_r ≥ 0` and every `M_r` is PSD, hence
`∑_k ⟨F_k, R_k⟩ ≤ -(eps/Λ)/C(n,2)` there; with `eps > 0` the three-point bound then rules out `n` unit
vectors with pairwise inner products `≤ 1/2` (`CertK.no_config`).
-/

open Real
open scoped RealInnerProductSpace

namespace Kissing

open ThomsonN7 ThomsonN7.ThreePoint ThomsonN7.Kron ThomsonN7.Kron.Ex ThomsonN7.Cert

/-- Gram triples of three unit vectors of `ℝ³` whose inner products are all at most `1/2`. -/
def GramHalf (u v t : ℝ) : Prop :=
  GramOK u v t ∧ 2 * u ≤ 1 ∧ 2 * v ≤ 1 ∧ 2 * t ≤ 1

/-- The multiplier with code `j`: `1+u`, `1+v`, `1+t` (codes `0`–`2`), `1-2u`, `1-2v`, `1-2t`
(codes `3`–`5`), the Gram determinant `1 + 2uvt - u² - v² - t²` (code `6`); every other code is `1`. -/
def codeK : ℕ → Ex
  | 0 => add (c 1) U
  | 1 => add (c 1) V
  | 2 => add (c 1) T
  | 3 => sub (c 1) (smul 2 U)
  | 4 => sub (c 1) (smul 2 V)
  | 5 => sub (c 1) (smul 2 T)
  | 6 => sub (add (c 1) (smul 2 (mul U (mul V T)))) (add (Ex.sq U) (add (Ex.sq V) (Ex.sq T)))
  | _ => c 1

lemma codeK_nonneg (code : ℕ) {u v t : ℝ} (h : GramHalf u v t) : 0 ≤ (codeK code).ev u v t := by
  obtain ⟨⟨hu, hv, ht, hd⟩, hu2, hv2, ht2⟩ := h
  have hu' := abs_le.1 ((sq_le_one_iff_abs_le_one u).1 hu)
  have hv' := abs_le.1 ((sq_le_one_iff_abs_le_one v).1 hv)
  have ht' := abs_le.1 ((sq_le_one_iff_abs_le_one t).1 ht)
  match code with
  | 0 => simp only [codeK, ev_add, ev_c, ev_U]; push_cast; linarith [hu'.1]
  | 1 => simp only [codeK, ev_add, ev_c, ev_V]; push_cast; linarith [hv'.1]
  | 2 => simp only [codeK, ev_add, ev_c, ev_T]; push_cast; linarith [ht'.1]
  | 3 => simp only [codeK, ev_sub, ev_smul, ev_c, ev_U]; push_cast; linarith
  | 4 => simp only [codeK, ev_sub, ev_smul, ev_c, ev_V]; push_cast; linarith
  | 5 => simp only [codeK, ev_sub, ev_smul, ev_c, ev_T]; push_cast; linarith
  | 6 =>
    simp only [codeK, ev_sub, ev_add, ev_c, ev_smul, ev_mul, ev_sq, ev_U, ev_V, ev_T]
    push_cast
    linarith
  | j + 7 => simp only [codeK, ev_c]; norm_num

/-- The product of the multipliers with the given codes (`[]` is `1`). -/
def gKE (g : List ℕ) : Ex :=
  g.foldr (fun code acc => mul (codeK code) acc) (c 1)

lemma gKE_nonneg (g : List ℕ) {u v t : ℝ} (h : GramHalf u v t) : 0 ≤ (gKE g).ev u v t := by
  induction g with
  | nil => simp [gKE]
  | cons code g ih =>
    simp only [gKE, List.foldr_cons, ev_mul] at ih ⊢
    exact mul_nonneg (codeK_nonneg code h) ih

/-- An SOS block: multiplier codes `g`, monomial basis `z`, and the PSD Gram data `B`. -/
structure KBlk where
  g : List ℕ
  z : List (ℕ × ℕ × ℕ)
  B : Blk

/-- The polynomial `g · zᵀ B z` of an SOS block. -/
def kblkE (s : KBlk) : Ex := mul (gKE s.g) (sqfE s.B s.z)

lemma kblkE_nonneg {s : KBlk} (h : s.B.ok s.z.length = true) {u v t : ℝ} (hg : GramHalf u v t) :
    0 ≤ (kblkE s).ev u v t := by
  rw [kblkE, ev_mul]
  exact mul_nonneg (gKE_nonneg s.g hg) (sqfE_nonneg h _ _ _)

lemma kblk_sum_nonneg (S : List KBlk) (hS : S.all (fun s => s.B.ok s.z.length) = true) {u v t : ℝ}
    (hg : GramHalf u v t) : 0 ≤ ((S.map kblkE).map fun e => e.ev u v t).sum := by
  refine List.sum_nonneg fun x hx => ?_
  simp only [List.mem_map] at hx
  obtain ⟨e, ⟨s, hs, rfl⟩, rfl⟩ := hx
  exact kblkE_nonneg (List.all_eq_true.mp hS s hs) hg

/-- A kissing certificate for `n` points: margin `e = eps / Λ`, kernel blocks `F_k` (in the basis
`uᵃ vᵇ Q_k`, `F_k = ent / Λ`) and SOS blocks, over the common denominator `Λ = Lam`. -/
structure CertK where
  n : ℕ
  Lam : ℕ
  eps : ℤ
  F : List Blk
  S : List KBlk

namespace CertK

/-- The `k`-th `F`-block. -/
def blk (cf : CertK) (k : ℕ) : Blk := cf.F.getD k Blk.empty

/-- The size of the `k`-th `F`-block. -/
def m (cf : CertK) (k : ℕ) : ℕ := (cf.blk k).Δ.length

/-- The number of `F`-blocks. -/
def K (cf : CertK) : ℕ := cf.F.length

/-- The `k`-th `F`-matrix. -/
noncomputable def Fm (cf : CertK) (k : ℕ) : Matrix (Fin (cf.m k)) (Fin (cf.m k)) ℝ :=
  fmat (cf.m k) cf.Lam (cf.blk k)

/-- The polynomial identity, scaled by `6 (n-1) C(n,2) Λ`, as an expression. -/
def idE (cf : CertK) : Ex :=
  sub (sub (c (-(6 * ((cf.n : ℤ) - 1) * cf.eps)))
      (smul (cf.n.choose 2 : ℕ) (ftotE cf.n cf.K fun k => fkE (cf.m k) (cf.blk k) k)))
    (smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ)) (sumE (cf.S.map kblkE)))

/-- The computable check. -/
def check (cf : CertK) : Bool :=
  decide (3 ≤ cf.n) && decide (0 < cf.Lam) &&
  (List.range cf.K).all (fun k => (cf.blk k).ok (cf.m k)) &&
  cf.S.all (fun s => s.B.ok s.z.length) && chk cf.idE

lemma check_parts {cf : CertK} (h : cf.check = true) :
    3 ≤ cf.n ∧ 0 < cf.Lam ∧ (∀ k < cf.K, (cf.blk k).ok (cf.m k) = true) ∧
    (cf.S.all (fun s => s.B.ok s.z.length) = true) ∧ chk cf.idE = true := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun k hk => ?_, h4, h5⟩
  exact (List.all_eq_true.mp h3) k (List.mem_range.mpr hk)

/-- The real-number algebra of the soundness proof. -/
lemma final_le {n' C Λ eps A Ssum : ℝ} (hn : 3 ≤ n') (hC : 0 < C) (hΛ : 0 < Λ) (hS : 0 ≤ Ssum)
    (hev : -(6 * (n' - 1) * eps) - C * (6 * (n' - 1) * Λ * A) - 6 * (n' - 1) * C * Ssum = 0) :
    A ≤ ((0 : ℝ) + 0 + 0) / 3 - (eps / Λ) / C := by
  have h6 : (6 * (n' - 1)) ≠ 0 := by
    have : 0 < 6 * (n' - 1) := by linarith
    exact this.ne'
  have h1 : 6 * (n' - 1) * (eps + C * Λ * A + C * Ssum) = 0 := by linear_combination -hev
  have h2 : eps + C * Λ * A + C * Ssum = 0 := (mul_eq_zero.mp h1).resolve_left h6
  have hCΛ : 0 < C * Λ := mul_pos hC hΛ
  have e1 : C * Λ * ((eps / Λ) / C) = eps := by field_simp
  have e2 : C * Λ * (Ssum / Λ) = C * Ssum := by field_simp
  have key : C * Λ * (A + (eps / Λ) / C + Ssum / Λ) = 0 := by
    rw [mul_add, mul_add, e1, e2]
    linear_combination h2
  have h3 : A + (eps / Λ) / C + Ssum / Λ = 0 := (mul_eq_zero.mp key).resolve_left hCΛ.ne'
  have h4 : 0 ≤ Ssum / Λ := div_nonneg hS hΛ.le
  norm_num
  linarith

/-- The pointwise inequality on `GramHalf`. -/
lemma hpt (cf : CertK) (hc : cf.check = true) {u v t : ℝ} (hg : GramHalf u v t) :
    ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk cf.n (cf.m k) k u v t)
      ≤ ((0 : ℝ) + 0 + 0) / 3 - ((cf.eps : ℝ) / cf.Lam) / (cf.n.choose 2 : ℕ) := by
  obtain ⟨hn, hL, hF, hS, hz⟩ := check_parts hc
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
        ftotTerm cf.n (fun a b c => (fkE (cf.m k) (cf.blk k) k).ev a b c) u v t
      = 6 * ((cf.n : ℝ) - 1) * cf.Lam
        * ∑ k ∈ Finset.range cf.K, matDot (cf.Fm k) (Rk cf.n (cf.m k) k u v t) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (key_F (cf.blk k) k cf.n hLpos.ne' hn1 u v t).symm
  rw [hFp] at hev
  push_cast at hev
  exact final_le hnr hC hLpos (kblk_sum_nonneg cf.S hS hg) hev

/-- **Soundness.** A checked certificate with positive margin excludes every configuration of `n` unit vectors in
`ℝ³` with all pairwise inner products at most `1/2`. -/
theorem no_config (cf : CertK) (hc : cf.check = true) (heps : 0 < cf.eps) (x : Fin cf.n → R3)
    (hx : ∀ i, ‖x i‖ = 1) (hhalf : ∀ i j, i ≠ j → ⟪x i, x j⟫ ≤ 1 / 2) : False := by
  obtain ⟨hn, hL, hF, hS, hz⟩ := check_parts hc
  have hb := three_point_bound_of_forall hn (fun s => 2 * s ≤ 1) cf.K cf.m cf.Fm
    (fun k hk => fmat_psd cf.Lam (hF k hk)) (fun _ => 0) ((cf.eps : ℝ) / cf.Lam)
    (fun u v t hg hu hv ht => hpt cf hc ⟨hg, hu, hv, ht⟩) x hx
    (fun i j hij => by have := hhalf i j hij; linarith)
  simp only [Finset.sum_const_zero] at hb
  have hpos : (0 : ℝ) < (cf.eps : ℝ) / cf.Lam :=
    div_pos (by exact_mod_cast heps) (by exact_mod_cast hL)
  linarith

end CertK

/-! ## Chunked statistics of the identity (for the Kronecker check) -/

open ThomsonN7.Case1 in
/-- The statistics of `cf.idE`, in terms of those of its pieces (cf. upstream `Case1.c1Stat_idE`). -/
lemma kStat_idE (cf : CertK) (w D : ℕ) :
    c1Stat w D cf.idE =
      c1Sub (c1Sub (c1C (-(6 * ((cf.n : ℤ) - 1) * cf.eps)))
        (c1Smul (cf.n.choose 2 : ℕ) (c1Sum ((List.range cf.K).map fun k =>
          c1Stat w D (c1FtotK cf.n (fkE (cf.m k) (cf.blk k) k))))))
        (c1Smul (6 * ((cf.n : ℤ) - 1) * (cf.n.choose 2 : ℕ))
          (c1Sum (cf.S.map fun s => c1Stat w D (kblkE s)))) := by
  simp only [CertK.idE, c1Stat_sub, c1Stat_smul, c1Stat_c, c1_ftotE_eq, c1Stat_sumRange,
    c1Stat_sumE, List.map_map]
  rfl

end Kissing
