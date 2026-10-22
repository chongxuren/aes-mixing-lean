import AES8.Math.PaperCharacterOperator
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-! The exact interface between the paper's multiplicative field characters
and Mathlib's finite abelian Fourier basis. Extension by zero is supplied by
`MulChar.ofUnitHom`; no extra character-existence assumption is introduced. -/
noncomputable section
open scoped BigOperators
open WithLp
namespace AES8.PaperMultiplicativeCharacters
open PaperCharacterBasis
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def unitsEquiv : Additive Fˣ ≃ Fˣ where
  toFun := Additive.toMul
  invFun := Additive.ofMul
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_additive {R : Type*} [AddCommMonoid R] (g : Fˣ → R) :
    (∑ a : Additive Fˣ, g a.toMul) = ∑ a : Fˣ, g a :=
  Equiv.sum_comp unitsEquiv g

def restrict (χ : MulChar F ℂ) : Character (Additive Fˣ) where
  toFun a := χ (a.toMul : F)
  map_zero_eq_one' := map_one χ
  map_add_eq_mul' a b := map_mul χ (a.toMul : F) (b.toMul : F)

def unitHom (ψ : Character (Additive Fˣ)) : Fˣ →* ℂ where
  toFun u := ψ (Additive.ofMul u)
  map_one' := ψ.map_zero_eq_one
  map_mul' u v := ψ.map_add_eq_mul (Additive.ofMul u) (Additive.ofMul v)

def extend (ψ : Character (Additive Fˣ)) : MulChar F ℂ :=
  MulChar.ofUnitHom (unitHom ψ).toHomUnits

@[simp] theorem restrict_apply (χ : MulChar F ℂ) (u : Fˣ) :
    restrict χ (Additive.ofMul u) = χ (u : F) := rfl

@[simp] theorem extend_apply (ψ : Character (Additive Fˣ)) (u : Fˣ) :
    extend ψ (u : F) = ψ (Additive.ofMul u) := by
  rw [extend, MulChar.ofUnitHom_coe]
  rfl

@[simp] theorem restrict_extend (ψ : Character (Additive Fˣ)) :
    restrict (extend ψ) = ψ := by
  ext a
  exact extend_apply ψ a.toMul

@[simp] theorem extend_restrict (χ : MulChar F ℂ) : extend (restrict χ) = χ := by
  ext u
  exact extend_apply (restrict χ) u

def characterEquiv : MulChar F ℂ ≃ Character (Additive Fˣ) where
  toFun := restrict
  invFun := extend
  left_inv := extend_restrict
  right_inv := restrict_extend

@[simp] theorem restrict_one : restrict (1 : MulChar F ℂ) = 0 := by
  ext a
  simp [restrict]

theorem extend_ne_one {ψ : Character (Additive Fˣ)} (hψ : ψ ≠ 0) :
    extend ψ ≠ 1 := by
  intro h
  apply hψ
  have h' := congrArg restrict h
  simpa only [restrict_extend, restrict_one] using h'

/-- Scalar bounds in the actual `MulChar F ℂ` interface suffice for the
complex L2 norm on the nonzero multiplicative group. -/
theorem norm_le (k : Fˣ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hμ : ∀ χ : MulChar F ℂ, χ ≠ 1 → ‖∑ u : Fˣ, k u * χ (u : F)‖ ≤ B)
    (f : EuclideanSpace ℂ (Additive Fˣ)) (hf : ∑ a, f a = 0) :
    ‖PaperCharacterOperator.operator (fun a : Additive Fˣ => k a.toMul) f‖ ≤ B * ‖f‖ := by
  apply PaperCharacterOperator.norm_le _ B hB _ f hf
  intro ψ hψ
  change ‖∑ a : Additive Fˣ, k a.toMul * ψ a‖ ≤ B
  have hs := sum_additive (fun u : Fˣ => k u * ψ (Additive.ofMul u))
  change (∑ a : Additive Fˣ, k a.toMul * ψ a) = _ at hs
  rw [hs]
  simpa only [extend_apply] using hμ (extend ψ) (extend_ne_one hψ)

theorem real_energy_le (k : Fˣ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hμ : ∀ χ : MulChar F ℂ, χ ≠ 1 →
      ‖∑ u : Fˣ, (k u : ℂ) * χ (u : F)‖ ≤ B)
    (f : Fˣ → ℝ) (hf : ∑ a, f a = 0) :
    (∑ b : Fˣ, (∑ a : Fˣ, k (b * a) * f a) ^ 2) ≤ B ^ 2 * ∑ a, f a ^ 2 := by
  let z : EuclideanSpace ℂ (Additive Fˣ) :=
    toLp 2 (fun a => (f a.toMul : ℂ))
  have hz : ∑ a, z a = 0 := by
    change (∑ a : Additive Fˣ, (f a.toMul : ℂ)) = 0
    rw [sum_additive (fun a : Fˣ => (f a : ℂ))]
    exact_mod_cast hf
  have hn := norm_le (fun u => (k u : ℂ)) B hB hμ z hz
  have hs := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hB (norm_nonneg _))).mpr hn
  have he (b : Additive Fˣ) :
      (∑ a : Additive Fˣ, k (b.toMul * a.toMul) * f a.toMul) =
        ∑ a : Fˣ, k (b.toMul * a) * f a :=
    sum_additive (fun a => k (b.toMul * a) * f a)
  have hs' :
      (∑ b : Additive Fˣ, (∑ a : Fˣ, k (b.toMul * a) * f a) ^ 2) ≤
        B ^ 2 * ∑ a : Additive Fˣ, f a.toMul ^ 2 := by
    simpa only [mul_pow, EuclideanSpace.norm_sq_eq,
      PaperCharacterOperator.operator_apply, z, PiLp.toLp_apply, toMul_add,
      ← Complex.ofReal_mul, ← Complex.ofReal_sum,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, he] using hs
  rw [sum_additive (fun b : Fˣ => (∑ a : Fˣ, k (b * a) * f a) ^ 2),
    sum_additive (fun a : Fˣ => f a ^ 2)] at hs'
  exact hs'

end AES8.PaperMultiplicativeCharacters
