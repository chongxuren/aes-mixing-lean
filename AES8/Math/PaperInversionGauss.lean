import AES8.Math.PaperInversionCounts
import Mathlib.NumberTheory.GaussSum

/-! The printed multiplicative-character calculation for inversion.
The additive character is the actual absolute trace character on arbitrary
finite fields of characteristic two. Full-field sums use MulChar's zero
extension; the explicit adapters below recover the paper's units sums.
Constructive proof checking only; no cryptanalytic attacks.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperInversionGauss
open AESMixing
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  [Algebra (ZMod 2) F]

/-- The paper's `(-1)^Tr(x)`, with the already constructed absolute trace. -/
def traceCharacter : AddChar F ℂ where
  toFun x := (PaperFieldTrace.character x : ℂ)
  map_zero_eq_one' := by simp [PaperFieldTrace.character_zero]
  map_add_eq_mul' x y := by
    exact_mod_cast PaperFieldTrace.character_add x y

@[simp] theorem traceCharacter_apply (x : F) :
    traceCharacter x = (PaperFieldTrace.character x : ℂ) := rfl

theorem traceCharacter_ne_one : (traceCharacter (F := F)) ≠ 1 := by
  obtain ⟨w, hw⟩ := PaperFieldTrace.character_witness (F := F)
  intro h
  have hh := congrArg (fun ψ : AddChar F ℂ => ψ w) h
  norm_num [hw] at hh

theorem traceCharacter_primitive : (traceCharacter (F := F)).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one traceCharacter_ne_one

theorem traceCharacter_inv : (traceCharacter (F := F))⁻¹ = traceCharacter := by
  ext x
  simp only [AddChar.inv_apply, CharTwo.neg_eq]

/-- Removing zero is exact whenever the summand vanishes there. -/
theorem sum_units_eq (f : F → ℂ) (hf : f 0 = 0) :
    (∑ u : Fˣ, f (u : F)) = ∑ x : F, f x := by
  have he := Equiv.sum_comp (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
    (fun x : {x : F // x ≠ 0} => f x.val)
  change (∑ u : Fˣ, f (u : F)) = ∑ x : {x : F // x ≠ 0}, f x.val at he
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0, hf, zero_add]
  exact he

/-- The units-indexed Gauss sum is Mathlib's zero-extended field sum. -/
theorem gaussSum_eq_units (χ : MulChar F ℂ) :
    gaussSum χ traceCharacter =
      ∑ u : Fˣ, χ (u : F) * traceCharacter (u : F) := by
  symm
  exact sum_units_eq (fun x : F => χ x*traceCharacter x)
    (by rw [MulChar.map_zero, zero_mul])

/-- Nonconstant multiplicative characters have zero sum on the units. -/
theorem character_units_sum {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    (∑ u : Fˣ, χ (u : F)) = 0 := by
  rw [sum_units_eq _ (MulChar.map_zero χ)]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- The two inner-sum values in the printed Gauss calculation. -/
theorem trace_units_inner (t : F) :
    (∑ v : Fˣ, traceCharacter ((t-1)*(v : F))) =
      if t=1 then (Fintype.card F : ℂ)-1 else -1 := by
  have he := Equiv.sum_comp (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
    (fun v : {x : F // x ≠ 0} => traceCharacter (v.val*(t-1)))
  change (∑ v : Fˣ, traceCharacter ((v : F)*(t-1))) =
    ∑ v : {x : F // x ≠ 0}, traceCharacter (v.val*(t-1)) at he
  have hs := Fintype.sum_eq_add_sum_subtype_ne
    (fun v : F => traceCharacter (v*(t-1))) 0
  rw [AddChar.sum_mulShift (t-1) traceCharacter_primitive] at hs
  simp only [zero_mul, AddChar.map_zero_eq_one] at hs
  rw [show (∑ v : Fˣ, traceCharacter ((t-1)*(v : F))) =
    ∑ v : Fˣ, traceCharacter ((v : F)*(t-1)) by simp_rw [mul_comm], he]
  by_cases ht : t=1
  · simp only [ht, sub_self, if_true] at hs ⊢
    exact (eq_sub_iff_add_eq).2 (by simpa only [add_comm] using hs.symm)
  · simp only [sub_eq_zero, ht, if_false] at hs ⊢
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [Nat.cast_zero, add_comm] using hs.symm

/-- Evaluation of the units double sum displayed in the paper. -/
theorem gauss_double_sum_eq_card {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    (∑ t : Fˣ, χ (t : F) *
      ∑ v : Fˣ, traceCharacter (((t : F)-1)*(v : F))) =
        (Fintype.card F : ℂ) := by
  simp_rw [trace_units_inner]
  have he (t : Fˣ) :
      χ (t : F)*(if (t : F)=1 then (Fintype.card F : ℂ)-1 else -1) =
        (if t=1 then (Fintype.card F : ℂ) else 0)-χ (t : F) := by
    by_cases ht : t=1
    · subst t
      simp
    · have ht' : (t : F) ≠ 1 := fun h => ht (Units.ext h)
      simp [ht, ht']
  simp_rw [he]
  rw [Finset.sum_sub_distrib, character_units_sum hχ, sub_zero]
  simp

/-- The Gauss product theorem applies to this actual, nontrivial trace. -/
theorem gauss_mul_conj {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    gaussSum χ traceCharacter * star (gaussSum χ traceCharacter) =
      (Fintype.card F : ℂ) := by
  rw [star_gaussSum_eq]
  exact gaussSum_mul_gaussSum_eq_card hχ traceCharacter_primitive

theorem gauss_norm_sq {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    ‖gaussSum χ traceCharacter‖^2 = (Fintype.card F : ℝ) := by
  have h := congrArg Complex.re (gauss_mul_conj hχ)
  simpa only [RCLike.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re,
    Complex.natCast_re] using h

/-- The literal displayed Gauss norm/double-sum identity. The upstream Gauss
product proof performs the same change of variables before this evaluation. -/
theorem gauss_norm_sq_eq_double_sum {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    ((‖gaussSum χ traceCharacter‖^2 : ℝ) : ℂ) =
      ∑ t : Fˣ, χ (t : F) *
        ∑ v : Fˣ, traceCharacter (((t : F)-1)*(v : F)) := by
  rw [gauss_norm_sq hχ, gauss_double_sum_eq_card hχ]
  norm_cast

theorem gauss_norm {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    ‖gaussSum χ traceCharacter‖ = Real.sqrt (Fintype.card F) := by
  rw [← gauss_norm_sq hχ, Real.sqrt_sq (norm_nonneg _)]

/-- The character multiplier of the literal inversion difference channel. -/
def multiplier (χ : MulChar F ℂ) : ℂ :=
  ∑ c : F, (differenceChannel invPermutation c 1 : ℂ)*χ c

theorem multiplier_eq_units (χ : MulChar F ℂ) :
    multiplier χ =
      ∑ c : Fˣ, (differenceChannel invPermutation (c : F) 1 : ℂ)*χ (c : F) := by
  symm
  exact sum_units_eq (fun c : F => (differenceChannel invPermutation c 1 : ℂ)*χ c)
    (by rw [MulChar.map_zero, mul_zero])

/-- Complex form of the exact Artin--Schreier inversion count. -/
theorem channel_one_complex (c : F) (hc : c ≠ 0) :
    (differenceChannel invPermutation c 1 : ℂ) =
      (1+traceCharacter c⁻¹+2*(if c=1 then (1 : ℂ) else 0))/(Fintype.card F : ℂ) := by
  rw [PaperInversionCounts.channel_one c hc]
  simp only [traceCharacter_apply, PaperFieldTrace.character]
  split_ifs <;> push_cast <;> ring

theorem channel_weight (χ : MulChar F ℂ) (c : F) :
    (differenceChannel invPermutation c 1 : ℂ)*χ c =
      (χ c+χ c*traceCharacter c⁻¹+2*(if c=1 then χ c else 0))/(Fintype.card F : ℂ) := by
  by_cases hc : c=0
  · subst c
    simp [MulChar.map_zero]
  · rw [channel_one_complex c hc]
    split_ifs <;> ring

/-- Inversion changes the multiplicative character into its inverse/conjugate. -/
theorem trace_inverse_weight (χ : MulChar F ℂ) :
    (∑ c : F, χ c*traceCharacter c⁻¹) = gaussSum χ⁻¹ traceCharacter := by
  have he := Equiv.sum_comp (invPermutation (F := F))
    (fun c : F => χ c*traceCharacter c⁻¹)
  change (∑ c : F, χ c⁻¹*traceCharacter c⁻¹⁻¹) = _ at he
  simpa only [inv_inv, gaussSum, MulChar.inv_apply'] using he.symm

/-- The paper's exact multiplier identity, with no field-cardinality restriction. -/
theorem multiplier_eq_gauss {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    multiplier χ = (gaussSum χ⁻¹ traceCharacter+2)/(Fintype.card F : ℂ) := by
  unfold multiplier
  simp_rw [channel_weight]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
    MulChar.sum_eq_zero_of_ne_one hχ, zero_add, trace_inverse_weight]
  simp

theorem multiplier_eq_gauss_conj {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    multiplier χ = (gaussSum (star χ) traceCharacter+2)/(Fintype.card F : ℂ) := by
  rw [MulChar.star_eq_inv]
  exact multiplier_eq_gauss hχ

/-- Scalar bound used by the printed character-basis operator-norm argument. -/
theorem multiplier_norm_le {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    ‖multiplier χ‖ ≤
      (Real.sqrt (Fintype.card F)+2)/(Fintype.card F : ℝ) := by
  rw [multiplier_eq_gauss hχ, norm_div]
  simp only [Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    ‖gaussSum χ⁻¹ traceCharacter+(2 : ℂ)‖ ≤
        ‖gaussSum χ⁻¹ traceCharacter‖+‖(2 : ℂ)‖ := norm_add_le _ _
    _ = _ := by rw [gauss_norm (inv_ne_one.mpr hχ)]; norm_num

end AES8.PaperInversionGauss
