import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! Finite complex characters, normalized in the counting-measure L2 space.
This is a mathematical leaf; no inversion or AES definitions occur here.
The additive wrapper permits immediate application to a multiplicative group.
Constructive proof checking only; no cryptanalytic attacks. -/
noncomputable section
open scoped BigOperators ComplexConjugate
open WithLp Module
namespace AES8.PaperCharacterBasis
set_option autoImplicit false
variable {A : Type*} [AddCommGroup A] [Fintype A]

abbrev Character (A : Type*) [AddCommGroup A] := AddChar A ℂ

def vector (χ : Character A) : EuclideanSpace ℂ A := toLp 2 (fun a => χ a)

def scale (A : Type*) [Fintype A] : ℂ :=
  ((Real.sqrt (Fintype.card A : ℝ) : ℝ) : ℂ)⁻¹

def normalized (χ : Character A) : EuclideanSpace ℂ A := scale A • vector χ

theorem scale_ne_zero : scale A ≠ 0 := by
  unfold scale
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr
    (by exact_mod_cast Fintype.card_pos)))

theorem conj_scale : conj (scale A) = scale A := by simp [scale]

theorem scale_sq_card : scale A * scale A * (Fintype.card A : ℂ) = 1 := by
  have hp : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hz : ((Real.sqrt (Fintype.card A : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hp)
  have hs : ((Real.sqrt (Fintype.card A : ℝ) : ℝ) : ℂ) *
      ((Real.sqrt (Fintype.card A : ℝ) : ℝ) : ℂ) = (Fintype.card A : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (le_of_lt hp)
  unfold scale
  rw [← mul_inv, ← hs, inv_mul_cancel₀ (mul_ne_zero hz hz)]

theorem inner_vector (χ ψ : Character A) :
    inner ℂ (vector χ) (vector ψ) =
      if χ = ψ then (Fintype.card A : ℂ) else 0 := by
  classical
  change (∑ a : A, inner ℂ (χ a) (ψ a)) = _
  rw [← Fintype.card_mul_expect,
    ← RCLike.wInner_cWeight_eq_expect, AddChar.wInner_cWeight_eq_boole]
  split_ifs <;> simp

theorem normalized_orthonormal : Orthonormal ℂ (normalized (A := A)) := by
  classical
  rw [orthonormal_iff_ite]
  intro χ ψ
  rw [normalized, normalized, inner_smul_left, inner_smul_right,
    conj_scale, inner_vector]
  by_cases h : χ = ψ
  · simp only [h, if_true]
    simpa only [mul_assoc] using (scale_sq_card (A := A))
  · simp [h]

/-- The full, normalized character basis. Completeness is Mathlib's finite
Pontryagin duality theorem, rather than a premise about the chosen family. -/
def basis : OrthonormalBasis (Character A) ℂ (EuclideanSpace ℂ A) :=
  let b := basisOfLinearIndependentOfCardEqFinrank
    (normalized_orthonormal (A := A)).linearIndependent
    (by rw [AddChar.card_eq, finrank_euclideanSpace])
  b.toOrthonormalBasis (by
    dsimp only [b]
    simpa only [coe_basisOfLinearIndependentOfCardEqFinrank] using
      (normalized_orthonormal (A := A)))

@[simp] theorem basis_apply (χ : Character A) : basis χ = normalized χ := by
  simp only [basis, Module.Basis.coe_toOrthonormalBasis,
    coe_basisOfLinearIndependentOfCardEqFinrank]

theorem sum_nonconstant {χ : Character A} (hχ : χ ≠ 0) : (∑ a, χ a) = 0 :=
  AddChar.sum_eq_zero_iff_ne_zero.mpr hχ

theorem constant_coefficient_eq_zero (f : EuclideanSpace ℂ A)
    (hf : ∑ a, f a = 0) : inner ℂ (basis (0 : Character A)) f = 0 := by
  rw [basis_apply, normalized, inner_smul_left]
  change conj (scale A) * (∑ a : A, inner ℂ (1 : ℂ) (f a)) = 0
  simpa only [RCLike.inner_apply, map_one, mul_one, hf, mul_zero]

end AES8.PaperCharacterBasis
