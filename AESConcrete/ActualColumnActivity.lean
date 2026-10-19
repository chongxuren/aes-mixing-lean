import AESConcrete.ColumnSupportResponse
import AESConcrete.ActualZeroEventProbabilities

/-!
# Actual degree-zero column energy

The empty marked set leaves a single residual-response output, whose value
is the exact probability of the prescribed output support. The compiled
support-response identity therefore identifies every activity support
component's energy. Orthogonality then gives the exact weighted quadratic
in actual support probabilities, before its separately proved probability
bound is applied. No projected-energy estimate is assumed.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualColumnActivity
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.WordColumnGram (Byte Word tensorResponse)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.RestrictedSourcePushforward (fullWordSource fullOutputCoordinates)
open AESConcrete.ColumnSupportResponse (nonzeroOutside column_support_energy)
open AESConcrete.ActualZeroEventProbabilities
  (exactOutputZeros exactOutputZeros_iff exactMass exactMass_eq_indicator actual_activity_factor_bound)

/-- The support-response event and the exact probability event coincide. -/
theorem support_source_mass_eq_exactMass (right : Orientation) (inverse : Bool)
    (a : Word) (r : Fin 16) :
    (∑ x : Word, fullWordSource right inverse a r (nonzeroOutside inverse r) x) =
      exactMass right inverse a r := by
  rw [exactMass_eq_indicator]
  apply Finset.sum_congr rfl
  intro x _
  simp only [fullWordSource, nonzeroOutside, ← exactOutputZeros_iff]

/-- With no marked coordinate, the tensor column is the empty product one. -/
theorem empty_response_eq_exactMass (left right : Orientation) (inverse : Bool)
    (a : Word) (r : Fin 16) (u : MaskCoordinates (0 : Fin 16) → Byte) :
    tensorResponse (fun _ : MaskCoordinates (0 : Fin 16) => residualMatrix (channel left) 0)
      (fullOutputCoordinates inverse 0)
      (fullWordSource right inverse a r (nonzeroOutside inverse r)) u =
      exactMass right inverse a r := by
  unfold tensorResponse WordColumnGram.tensorColumn
  have he (x : Word) :
      (∏ i : MaskCoordinates (0 : Fin 16), residualMatrix (channel left) 0
        (u i) (fullOutputCoordinates inverse 0 x i)) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    exact (empty_mask_coordinate i).elim
  simp_rw [he, one_mul]
  exact support_source_mass_eq_exactMass right inverse a r

/-- Exact energy of one activity support component of the actual column. -/
theorem activity_support_energy (left right : Orientation) (inverse : Bool)
    (a : Word) (r : Fin 16) :
    (∑ y : Word, action (supportProduct (0 : Byte) (maskBit (0 : Fin 16)) (maskBit r))
      (fun v => wordKernel left right inverse v a) y ^ 2) =
      exactMass right inverse a r ^ 2 / (255 : ℝ) ^ (4-maskSize r) := by
  rw [column_support_energy left right inverse a r 0 (mask_disjoint_empty r)]
  simp_rw [empty_response_eq_exactMass left right inverse a r]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, maskCoordinates_card,
    show maskSize (0 : Fin 16) = 0 by decide, pow_zero, one_nsmul, add_zero]

/-- Fixed marked mask zero: orthogonal support decomposition for any word vector. -/
theorem degree_zero_support_energy (f : Word → ℝ) :
    (∑ y : Word, degreeComponent (0 : Byte) 0 f y ^ 2) =
      ∑ r : Fin 16, ∑ y : Word,
        action (supportProduct (0 : Byte) (maskBit (0 : Fin 16)) (maskBit r)) f y ^ 2 := by
  have hmask : maskBit (0 : Fin 16) = fun _ : Fin 4 => false := by
    funext i
    fin_cases i <;> decide
  rw [← degreeKernel_action, degreeKernel_zero, ← hmask]
  calc
    _ = ∑ inactive : Fin 4 → Bool, ∑ y : Word,
        action (supportProduct (0 : Byte) (maskBit (0 : Fin 16)) inactive) f y ^ 2 :=
      supportProduct_pythagoras 0 (by norm_num [BinaryWord.card]) (maskBit (0 : Fin 16)) f
    _ = _ := (maskBitsEquiv.sum_comp (fun inactive : Fin 4 → Bool =>
      ∑ y : Word, action (supportProduct (0 : Byte) (maskBit (0 : Fin 16)) inactive) f y ^ 2)).symm

private theorem support_power_normalization (r : Fin 16) (w : ℝ) :
    w / (255 : ℝ) ^ (4-maskSize r) = ((255 : ℝ) ^ maskSize r * w) / (255 : ℝ)^4 := by
  have hne : (255 : ℝ) ^ (4-maskSize r) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply (div_eq_div_iff hne (by norm_num : (255 : ℝ)^4 ≠ 0)).mpr
  have hsum : maskSize r + (4-maskSize r) = 4 := by
    have hle := maskSize_le_four r
    omega
  have hpow : (255 : ℝ)^4 = (255 : ℝ)^maskSize r * (255 : ℝ)^(4-maskSize r) := by
    rw [← pow_add, hsum]
  rw [hpow]
  ring

/-- The actual degree-zero energy is precisely the activity probability quadratic. -/
theorem column_activity_energy (left right : Orientation) (inverse : Bool) (a : Word) :
    (∑ y : Word, degreeComponent (0 : Byte) 0
      (fun v => wordKernel left right inverse v a) y ^ 2) =
      (∑ r : Fin 16, (255 : ℝ) ^ maskSize r * exactMass right inverse a r ^ 2) /
        (255 : ℝ)^4 := by
  rw [degree_zero_support_energy]
  simp_rw [activity_support_energy left right inverse a]
  calc
    _ = ∑ r : Fin 16, ((255 : ℝ) ^ maskSize r * exactMass right inverse a r ^ 2) /
        (255 : ℝ)^4 := Finset.sum_congr rfl
      (fun r _ => support_power_normalization r (exactMass right inverse a r ^ 2))
    _ = _ := (Finset.sum_div _ _ _).symm

/-- The reciprocal-factor form used by the activity comparison. -/
theorem column_activity_energy_factor (left right : Orientation) (inverse : Bool) (a : Word) :
    (∑ y : Word, degreeComponent (0 : Byte) 0
      (fun v => wordKernel left right inverse v a) y ^ 2) =
      (1 / (255 : ℝ)^4) *
        ∑ r : Fin 16, (255 : ℝ) ^ maskSize r * exactMass right inverse a r ^ 2 := by
  rw [column_activity_energy, div_eq_mul_inv, one_div, mul_comm]

/-- Concrete probability caps yield the actual activity energy bound. -/
theorem actual_column_activity_energy_le (left right : Orientation) (inverse : Bool)
    (a : Word) (z : Fin 16) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true) :
    (∑ y : Word, degreeComponent (0 : Byte) 0
      (fun v => wordKernel left right inverse v a) y ^ 2) ≤
      MultibyteColumnNumbers.activityFactor t / (255 : ℝ)^4 := by
  rw [column_activity_energy]
  exact div_le_div_of_nonneg_right
    (actual_activity_factor_bound right inverse a z t ht hcount ha) (by norm_num)

end AESConcrete.ActualColumnActivity
