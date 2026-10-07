import Kissing4.Kernel
import Kissing4.Addition

-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):
-- `Rc_eq_re` from `ThreePoint.Q3_eq_re`; `quad_Y4_nonneg` from `ThreePoint.quad_Y3_nonneg`;
-- `sum_S4_eq_sum_Y4` from `ThreePoint.sum_S3_eq_sum_Y3`; `exists_tangent_frame4` from
-- `ThreePoint.exists_tangent_frame`; `bv_positivity4` from `ThreePoint.bv_positivity`;
-- `matDot_moment_nonneg4` from `ThreePoint.matDot_moment_nonneg`.

/-!
# Bachoc–Vallentin positivity on `S³` (degrees `k ≤ 7`)

For unit vectors `x i` of `ℝ⁴` and every `k ≤ 7`, the moment matrix `∑_{i,j,l} S4_k(⟨xᵢ,xⱼ⟩, ⟨xᵢ,x_l⟩, ⟨xⱼ,x_l⟩)`
is positive semidefinite. The argument follows the `S²` case: fix the first index `i`, write the other points in an
orthonormal frame of the orthogonal complement of `xᵢ` (now three-dimensional), and show that the inner double sum
is a sum of squares. In dimension 4 the kernel `Q4 k` becomes, in these coordinates, the `k!`-scaled solid Legendre
kernel `Zt k` on `ℝ³` (`Q4_eq_Zt`); the addition theorem (`Kissing4.Zt_addition`, generated and checked for `k ≤ 7`)
writes it as a nonnegative combination of the products `A(y) A(y') Re((a + i b)^m (a' - i b')^m)`. By `Rc_eq` each
product splits into two products of the form `f(y) f(y')`, so the weighted double sum over the points is a sum of
squares (`sum_coef_gram_nonneg`).
-/

open ThomsonN7 ThomsonN7.ThreePoint
open scoped RealInnerProductSpace

namespace Kissing4

/-! ## The kernel in tangent coordinates -/

/-- In coordinates `y = (a, b, c)`, `y' = (a', b', c')` of the tangent components, `Q4` is the solid kernel `Zt`. -/
theorem Q4_eq_Zt (u v t a b c a' b' c' : ℝ) (hu : 1 - u ^ 2 = a ^ 2 + b ^ 2 + c ^ 2)
    (hv : 1 - v ^ 2 = a' ^ 2 + b' ^ 2 + c' ^ 2) (ht : t - u * v = a * a' + b * b' + c * c') (k : ℕ) :
    Q4 k u v t = Zt a b c a' b' c' k := by
  have key : ∀ k, Q4 k u v t = Zt a b c a' b' c' k ∧ Q4 (k + 1) u v t = Zt a b c a' b' c' (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨rfl, by simp only [Q4, Zt, ht]⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      calc Q4 (k + 2) u v t
          = (2 * (k : ℝ) + 3) * (t - u * v) * Q4 (k + 1) u v t
            - ((k : ℝ) + 1) ^ 2 * ((1 - u ^ 2) * (1 - v ^ 2)) * Q4 k u v t := rfl
        _ = (2 * (k : ℝ) + 3) * (a * a' + b * b' + c * c') * Zt a b c a' b' c' (k + 1)
            - ((k : ℝ) + 1) ^ 2 * ((a ^ 2 + b ^ 2 + c ^ 2) * (a' ^ 2 + b' ^ 2 + c' ^ 2)) * Zt a b c a' b' c' k := by
          rw [ih.1, ih.2, ht, hu, hv]
        _ = Zt a b c a' b' c' (k + 2) := rfl
  exact (key k).1

/-- `Rc m` is the real part of `((a + i b) (a' - i b'))^m`. -/
theorem Rc_eq_re (a b a' b' : ℝ) (m : ℕ) :
    Rc a b a' b' m = (((⟨a, b⟩ : ℂ) * (starRingEnd ℂ) ⟨a', b'⟩) ^ m).re := by
  set w : ℂ := (⟨a, b⟩ : ℂ) * (starRingEnd ℂ) ⟨a', b'⟩ with hw
  have hre : w.re = a * a' + b * b' := by
    simp only [hw, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hns : Complex.normSq w = (a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2) := by
    rw [hw, map_mul, Complex.normSq_conj, Complex.normSq_apply, Complex.normSq_apply]
    ring
  have hrec : w * w = (2 * w.re : ℝ) * w - (Complex.normSq w : ℝ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply] <;> ring
  have key : ∀ m, Rc a b a' b' m = (w ^ m).re ∧ Rc a b a' b' (m + 1) = (w ^ (m + 1)).re := by
    intro m
    induction m with
    | zero => exact ⟨by simp [Rc], by simp [Rc, hre]⟩
    | succ m ih =>
      refine ⟨ih.2, ?_⟩
      have h2 : w ^ (m + 2) = ((2 * w.re : ℝ) : ℂ) * w ^ (m + 1) - (Complex.normSq w : ℝ) * w ^ m := by
        have : w ^ (m + 2) = w ^ m * (w * w) := by ring
        rw [this, hrec]
        ring
      calc Rc a b a' b' (m + 2)
          = 2 * (a * a' + b * b') * Rc a b a' b' (m + 1)
            - (a ^ 2 + b ^ 2) * (a' ^ 2 + b' ^ 2) * Rc a b a' b' m := rfl
        _ = 2 * w.re * (w ^ (m + 1)).re - Complex.normSq w * (w ^ m).re := by
          rw [ih.1, ih.2, hre, hns]
        _ = (w ^ (m + 2)).re := by
          rw [h2, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  exact (key m).1

/-- `Rc m` as a sum of two products: `Re(z^m) Re(z'^m) + Im(z^m) Im(z'^m)`. -/
theorem Rc_eq (a b a' b' : ℝ) (m : ℕ) :
    Rc a b a' b' m = ((⟨a, b⟩ : ℂ) ^ m).re * ((⟨a', b'⟩ : ℂ) ^ m).re
      + ((⟨a, b⟩ : ℂ) ^ m).im * ((⟨a', b'⟩ : ℂ) ^ m).im := by
  rw [Rc_eq_re, mul_pow, Complex.mul_re, ← map_pow, Complex.conj_re, Complex.conj_im]
  ring

/-! ## The quadratic form at a fixed centre -/

/-- A nonnegative combination of Gram forms of two families is nonnegative. -/
theorem sum_coef_gram_nonneg {N : ℕ} (s : Finset ℕ) (coef : ℕ → ℝ) (hc : ∀ q, 0 ≤ coef q)
    (f g : ℕ → Fin N → ℝ) :
    0 ≤ ∑ j, ∑ l, ∑ q ∈ s, coef q * (f q j * f q l + g q j * g q l) := by
  have hq : ∀ q, ∑ j, ∑ l, coef q * (f q j * f q l + g q j * g q l)
      = coef q * ((∑ j, f q j) ^ 2 + (∑ j, g q j) ^ 2) := by
    intro q
    rw [sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
  have hswap : ∑ j, ∑ l, ∑ q ∈ s, coef q * (f q j * f q l + g q j * g q l)
      = ∑ q ∈ s, coef q * ((∑ j, f q j) ^ 2 + (∑ j, g q j) ^ 2) := by
    calc ∑ j, ∑ l, ∑ q ∈ s, coef q * (f q j * f q l + g q j * g q l)
        = ∑ j, ∑ q ∈ s, ∑ l, coef q * (f q j * f q l + g q j * g q l) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ q ∈ s, ∑ j, ∑ l, coef q * (f q j * f q l + g q j * g q l) := Finset.sum_comm
      _ = ∑ q ∈ s, coef q * ((∑ j, f q j) ^ 2 + (∑ j, g q j) ^ 2) :=
          Finset.sum_congr rfl fun q _ => hq q
  rw [hswap]
  exact Finset.sum_nonneg fun q _ => mul_nonneg (hc q) (by positivity)

/-- **The quadratic form of `∑_{j,l} Y4_k` at a fixed centre is nonnegative** (`k ≤ 7`), given tangent coordinates
`(a, b, c)` of the other points. -/
theorem quad_Y4_nonneg (m k : ℕ) (hk : k ≤ 7) {N : ℕ} (u : Fin N → ℝ) (t : Fin N → Fin N → ℝ)
    (a b c : Fin N → ℝ) (hu : ∀ j, 1 - u j ^ 2 = a j ^ 2 + b j ^ 2 + c j ^ 2)
    (ht : ∀ j l, t j l - u j * u l = a j * a l + b j * b l + c j * c l) (w : Fin m → ℝ) :
    0 ≤ ∑ j, ∑ l, w ⬝ᵥ (Y4 m k (u j) (u l) (t j l)).mulVec w := by
  set p : Fin N → ℝ := fun j => ∑ q, w q * u j ^ (q : ℕ) with hp
  have key : ∀ j l, w ⬝ᵥ (Y4 m k (u j) (u l) (t j l)).mulVec w = p j * p l * Q4 k (u j) (u l) (t j l) := by
    intro j l
    simp only [hp, dotProduct, Matrix.mulVec, Y4, Matrix.of_apply]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  set z : Fin N → ℂ := fun j => ⟨a j, b j⟩ with hz
  have term : ∀ j l, p j * p l * Q4 k (u j) (u l) (t j l)
      = ∑ q ∈ Finset.range (k + 1), coefK k q *
          ((p j * Aa k q (a j) (b j) (c j) * ((z j) ^ q).re) * (p l * Aa k q (a l) (b l) (c l) * ((z l) ^ q).re)
          + (p j * Aa k q (a j) (b j) (c j) * ((z j) ^ q).im)
            * (p l * Aa k q (a l) (b l) (c l) * ((z l) ^ q).im)) := by
    intro j l
    rw [Q4_eq_Zt (u j) (u l) (t j l) (a j) (b j) (c j) (a l) (b l) (c l) (hu j) (hu l) (ht j l),
      Zt_addition hk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Rc_eq]
    simp only [hz]
    ring
  simp only [key, term]
  exact sum_coef_gram_nonneg _ (coefK k) (coefK_nonneg k)
    (fun q j => p j * Aa k q (a j) (b j) (c j) * ((z j) ^ q).re)
    (fun q j => p j * Aa k q (a j) (b j) (c j) * ((z j) ^ q).im)

/-! ## Symmetrisation, tangent frames and positivity -/

/-- The symmetrised triple sum equals the unsymmetrised one. -/
theorem sum_S4_eq_sum_Y4 (m k : ℕ) {n : ℕ} (t : Fin n → Fin n → ℝ) (hsym : ∀ i j, t j i = t i j)
    (w : Fin m → ℝ) :
    ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S4 m k (t i j) (t i l) (t j l)).mulVec w
      = ∑ i, ∑ j, ∑ l, w ⬝ᵥ (Y4 m k (t i j) (t i l) (t j l)).mulVec w := by
  set Φ : Fin n → Fin n → Fin n → ℝ :=
    fun i j l => w ⬝ᵥ (Y4 m k (t i j) (t i l) (t j l)).mulVec w with hΦ
  have expand : ∀ i j l, w ⬝ᵥ (S4 m k (t i j) (t i l) (t j l)).mulVec w
      = (1 / 6 : ℝ) * (Φ i j l + Φ j i l + Φ i l j + Φ l i j + Φ j l i + Φ l j i) := by
    intro i j l
    simp only [S4, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add,
      smul_eq_mul, hΦ, hsym]
  have e1 : ∑ i, ∑ j, ∑ l, Φ j i l = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap12 Φ).symm
  have e2 : ∑ i, ∑ j, ∑ l, Φ i l j = ∑ i, ∑ j, ∑ l, Φ i j l := (tsum_swap23 Φ).symm
  have e3 : ∑ i, ∑ j, ∑ l, Φ l i j = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap23 (fun i j l => Φ l i j)]; exact (tsum_swap12 Φ).symm
  have e4 : ∑ i, ∑ j, ∑ l, Φ j l i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ j l i)]; exact (tsum_swap23 Φ).symm
  have e5 : ∑ i, ∑ j, ∑ l, Φ l j i = ∑ i, ∑ j, ∑ l, Φ i j l := by
    rw [tsum_swap12 (fun i j l => Φ l j i), tsum_swap23 (fun i j l => Φ l i j)]
    exact (tsum_swap12 Φ).symm
  simp only [expand, ← Finset.mul_sum, Finset.sum_add_distrib, e1, e2, e3, e4, e5]
  ring

/-- Every unit vector of `ℝ⁴` has an orthonormal frame `e₁, e₂, e₃` of its orthogonal complement, with
Parseval's identity for the tangent components. -/
theorem exists_tangent_frame4 (x : R4) (hx : ‖x‖ = 1) :
    ∃ e₁ e₂ e₃ : R4, ∀ y z : R4, ‖y‖ = 1 → ‖z‖ = 1 →
      (1 - ⟪x, y⟫ ^ 2 = ⟪e₁, y⟫ ^ 2 + ⟪e₂, y⟫ ^ 2 + ⟪e₃, y⟫ ^ 2) ∧
      (⟪y, z⟫ - ⟪x, y⟫ * ⟪x, z⟫ = ⟪e₁, y⟫ * ⟪e₁, z⟫ + ⟪e₂, y⟫ * ⟪e₂, z⟫ + ⟪e₃, y⟫ * ⟪e₃, z⟫) := by
  have hcard : Module.finrank ℝ R4 = Fintype.card (Fin 4) := by simp
  let v : Fin 4 → R4 := fun _ => x
  have hv : Orthonormal ℝ (({0} : Set (Fin 4)).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subtype.ext (by
      have hi := i.2; have hj := j.2
      simp only [Set.mem_singleton_iff] at hi hj
      rw [hi, hj])
    subst hij
    simp [Set.domRestrict, v, hx]
  obtain ⟨B, hB⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard hv
  have hB0 : B 0 = x := hB 0 (Set.mem_singleton 0)
  refine ⟨B 1, B 2, B 3, fun y z hy hz => ?_⟩
  have P := B.sum_inner_mul_inner y z
  have Py := B.sum_inner_mul_inner y y
  rw [Fin.sum_univ_four, hB0] at P Py
  rw [real_inner_self_eq_norm_sq, hy] at Py
  have c1 : ⟪y, x⟫ = ⟪x, y⟫ := real_inner_comm _ _
  have c2 : ⟪y, B 1⟫ = ⟪B 1, y⟫ := real_inner_comm _ _
  have c3 : ⟪y, B 2⟫ = ⟪B 2, y⟫ := real_inner_comm _ _
  have c4 : ⟪y, B 3⟫ = ⟪B 3, y⟫ := real_inner_comm _ _
  rw [c1, c2, c3, c4] at P Py
  constructor
  · linear_combination -Py
  · linear_combination -P

/-- **Bachoc–Vallentin positivity for `S³`** (`k ≤ 7`). -/
theorem bv_positivity4 (m k : ℕ) (hk : k ≤ 7) {n : ℕ} (x : Fin n → R4) (hx : ∀ i, ‖x i‖ = 1)
    (w : Fin m → ℝ) :
    0 ≤ ∑ i, ∑ j, ∑ l, w ⬝ᵥ (S4 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫).mulVec w := by
  have hsym : ∀ i j, ⟪x j, x i⟫ = ⟪x i, x j⟫ := fun i j => real_inner_comm _ _
  have e := sum_S4_eq_sum_Y4 m k (fun i j => ⟪x i, x j⟫) hsym w
  beta_reduce at e
  rw [e]
  refine Finset.sum_nonneg fun i _ => ?_
  obtain ⟨e₁, e₂, e₃, hfr⟩ := exists_tangent_frame4 (x i) (hx i)
  exact quad_Y4_nonneg m k hk (fun j => ⟪x i, x j⟫) (fun j l => ⟪x j, x l⟫)
    (fun j => ⟪e₁, x j⟫) (fun j => ⟪e₂, x j⟫) (fun j => ⟪e₃, x j⟫)
    (fun j => (hfr (x j) (x j) (hx j) (hx j)).1)
    (fun j l => (hfr (x j) (x l) (hx j) (hx l)).2) w

/-- Pairing of a PSD matrix with the moment matrix is nonnegative (`k ≤ 7`). -/
theorem matDot_moment_nonneg4 (m k : ℕ) (hk : k ≤ 7) {n : ℕ} (x : Fin n → R4) (hx : ∀ i, ‖x i‖ = 1)
    (F : Matrix (Fin m) (Fin m) ℝ) (hF : F.PosSemidef) :
    0 ≤ ∑ i, ∑ j, ∑ l, matDot F (S4 m k ⟪x i, x j⟫ ⟪x i, x l⟫ ⟪x j, x l⟫) := by
  obtain ⟨r, v, hFv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hF
  have key3 : ∀ X : Fin m → Fin m → Fin r → ℝ,
      ∑ a, ∑ b, ∑ s, X a b s = ∑ s, ∑ a, ∑ b, X a b s := by
    intro X
    calc ∑ a, ∑ b, ∑ s, X a b s = ∑ a, ∑ s, ∑ b, X a b s :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ s, ∑ a, ∑ b, X a b s := Finset.sum_comm
  have hdot : ∀ M : Matrix (Fin m) (Fin m) ℝ, matDot F M = ∑ s, v s ⬝ᵥ M.mulVec (v s) := by
    intro M
    rw [hFv]
    simp only [matDot, Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [key3 (fun a b s => v s a * v s b * M a b)]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    ring
  have hswap : ∀ f : Fin n → Fin n → Fin n → Fin r → ℝ,
      ∑ i, ∑ j, ∑ l, ∑ s, f i j l s = ∑ s, ∑ i, ∑ j, ∑ l, f i j l s := by
    intro f
    calc ∑ i, ∑ j, ∑ l, ∑ s, f i j l s
        = ∑ i, ∑ j, ∑ s, ∑ l, f i j l s :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ i, ∑ s, ∑ j, ∑ l, f i j l s := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ s, ∑ i, ∑ j, ∑ l, f i j l s := Finset.sum_comm
  simp only [hdot]
  rw [hswap]
  exact Finset.sum_nonneg fun s _ => bv_positivity4 m k hk x hx (v s)

end Kissing4
