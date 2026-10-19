import AESConcrete.RestrictedZeroEvents
import AESConcrete.RestrictedSourcePushforward
import AESConcrete.MultibyteColumnNumbers
import AESMixing.ActivitySpan

/-!
# Actual exact output-zero probabilities and the activity collision box

The sixteen events specify both the zero and nonzero output coordinates.
Their masses are those of the actual first-substitution source after actual
forward or inverse diffusion. The unique zero mask proves their partition;
the checked shortened-source table supplies the caps after an exact finite
sum identity. No source probability bound is a premise of the final theorem.

This module bounds the activity probability quadratic only. Identification
with projected output energy and aggregation with residual responses remain
separate obligations. Constructive mathematics only; no attacks or edits to
manuscript or historical sources.
-/

noncomputable section
open scoped BigOperators
set_option maxRecDepth 100000

namespace AESConcrete.ActualZeroEventProbabilities
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Byte Word inputColumn)
open AESConcrete.RestrictedSourcePushforward (fullWordSource outputZeros)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom)
open AESConcrete.ActualRestrictedDensity (restrictedSource)
open AESConcrete.MultibyteColumnNumbers (zeroCap activityFactor)

/-- Coordinates outside the mask are explicitly required to be nonzero. -/
def exactOutputZeros (inverse : Bool) (r : Fin 16) (x : Word) : Prop :=
  ∀ i : Fin 4, maskBit r i = true ↔ byteDiffusionOrientation inverse x i = 0

instance (inverse : Bool) (r : Fin 16) : DecidablePred (exactOutputZeros inverse r) := by
  intro x
  unfold exactOutputZeros
  infer_instance

theorem exactOutputZeros_iff (inverse : Bool) (r : Fin 16) (x : Word) :
    exactOutputZeros inverse r x ↔ outputZeros inverse r x ∧
      ∀ i : Fin 4, maskBit r i ≠ true → byteDiffusionOrientation inverse x i ≠ 0 := by
  constructor
  · intro h
    exact ⟨fun i hi => (h i).mp hi, fun i hi hz => hi ((h i).mpr hz)⟩
  · rintro ⟨hzero, hnonzero⟩ i
    constructor
    · exact hzero i
    · intro hz
      by_contra hi
      exact hnonzero i hi hz

def zeroMask (inverse : Bool) (x : Word) : Fin 16 :=
  maskBitsEquiv.symm (fun i => decide (byteDiffusionOrientation inverse x i = 0))

theorem zeroMask_bit (inverse : Bool) (x : Word) (i : Fin 4) :
    maskBit (zeroMask inverse x) i = true ↔ byteDiffusionOrientation inverse x i = 0 := by
  have h := congrFun (maskBitsEquiv.apply_symm_apply
    (fun i => decide (byteDiffusionOrientation inverse x i = 0))) i
  change maskBit (zeroMask inverse x) i =
    decide (byteDiffusionOrientation inverse x i = 0) at h
  simp only [h, decide_eq_true_eq]

theorem exactOutputZeros_iff_eq_mask (inverse : Bool) (r : Fin 16) (x : Word) :
    exactOutputZeros inverse r x ↔ r = zeroMask inverse x := by
  constructor
  · intro h
    apply maskBitsEquiv.injective
    funext i
    change maskBit r i = maskBit (zeroMask inverse x) i
    have hr := h i
    have hz := zeroMask_bit inverse x i
    cases he : maskBit r i <;> cases hf : maskBit (zeroMask inverse x) i <;> simp_all
  · rintro rfl
    exact zeroMask_bit inverse x

def exactMass (right : Orientation) (inverse : Bool) (a : Word) (r : Fin 16) : ℝ :=
  ∑ x : Word, fullWordSource right inverse a r (exactOutputZeros inverse r) x

theorem exactMass_nonneg (right : Orientation) (inverse : Bool) (a : Word) (r : Fin 16) :
    0 ≤ exactMass right inverse a r :=
  Finset.sum_nonneg (fun x _ => RestrictedSourcePushforward.fullWordSource_nonneg
    right inverse a r (exactOutputZeros inverse r) x)

theorem exactMass_eq_indicator (right : Orientation) (inverse : Bool) (a : Word) (r : Fin 16) :
    exactMass right inverse a r =
      ∑ x : Word, if exactOutputZeros inverse r x then inputColumn right a x else 0 := by
  unfold exactMass fullWordSource
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : exactOutputZeros inverse r x
  · have hz := (exactOutputZeros_iff inverse r x).mp he
    simp [he, hz.1]
  · simp [he]

theorem exactMass_sum_one (right : Orientation) (inverse : Bool) (a : Word) :
    (∑ r : Fin 16, exactMass right inverse a r) = 1 := by
  simp_rw [exactMass_eq_indicator]
  rw [Finset.sum_comm]
  have hp (x : Word) :
      (∑ r : Fin 16, if exactOutputZeros inverse r x then inputColumn right a x else 0) =
        inputColumn right a x := by
    simp only [exactOutputZeros_iff_eq_mask, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [hp]
  exact WordColumnGram.inputColumn_mass right a

theorem exactMass_eq_shortened (right : Orientation) (inverse : Bool) (a : Word)
    (r z : Fin 16) (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true) :
    exactMass right inverse a r =
      ∑ c : ShortenedGraph (byteDiffusionHom inverse) r z,
        restrictedSource right inverse a r z (fun c => exactOutputZeros inverse r c.val) c := by
  have h := RestrictedSourcePushforward.shortened_weighted_sum_eq_full
    right inverse a r z ha (exactOutputZeros inverse r) (fun _ => (1 : ℝ))
  simpa only [one_mul, exactMass] using h.symm

private theorem all_bits_size : ∀ z : Fin 16,
    (∀ i : Fin 4, maskBit z i = true) → maskSize z = 4 := by decide

private theorem mask_size_zero : ∀ r : Fin 16, maskSize r = 0 ↔ r = 0 := by decide

theorem input_nonzero_of_active_count (a : Word) (z : Fin 16)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true) (hz : maskSize z ≤ 2) : a ≠ 0 := by
  intro h
  have hall : ∀ i : Fin 4, maskBit z i = true := fun i => (ha i).mp (congrFun h i)
  have hfour := all_bits_size z hall
  omega

theorem exactMass_forbidden (right : Orientation) (inverse : Bool) (a : Word)
    (r z : Fin 16) (ha0 : a ≠ 0)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (hhigh : 4 ≤ maskSize r + maskSize z) :
    exactMass right inverse a r = 0 := by
  rw [exactMass_eq_shortened right inverse a r z ha]
  exact RestrictedZeroEvents.actual_restricted_mass_zero right inverse a ha0 r z hhigh _

/-- Every concrete cap follows from the actual shortened-source table.
The integer equation identifies t with four minus the input-zero count. -/
theorem exactMass_le_zeroCap (right : Orientation) (inverse : Bool) (a : Word)
    (r z : Fin 16) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (hr : 0 < maskSize r ∧ maskSize r < t) :
    exactMass right inverse a r ≤ zeroCap t (maskSize r) := by
  rw [exactMass_eq_shortened right inverse a r z ha]
  obtain ⟨ht0, ht1⟩ := ht
  interval_cases t
  · have hr1 : maskSize r = 1 := by omega
    have h := RestrictedZeroEvents.actual_one_zero_mass_le right inverse a r z hr1 (by omega)
      ha (fun c => exactOutputZeros inverse r c.val)
    simpa [zeroCap, hr1, MultibyteColumnNumbers.rho] using h
  · by_cases hr1 : maskSize r = 1
    · have h := RestrictedZeroEvents.actual_one_zero_mass_le right inverse a r z hr1 (by omega)
        ha (fun c => exactOutputZeros inverse r c.val)
      simpa [zeroCap, hr1, MultibyteColumnNumbers.rho] using h
    · have hr2 : maskSize r = 2 := by omega
      have h := RestrictedZeroEvents.actual_three_active_two_zero_mass_le right inverse a r z
        hr2 (by omega) ha (fun c => exactOutputZeros inverse r c.val)
      simpa [zeroCap, hr2, MultibyteColumnNumbers.rho, MultibyteColumnNumbers.atom] using h
  · by_cases hr1 : maskSize r = 1
    · have h := RestrictedZeroEvents.actual_one_zero_mass_le right inverse a r z hr1 (by omega)
        ha (fun c => exactOutputZeros inverse r c.val)
      simpa [zeroCap, hr1, MultibyteColumnNumbers.rho] using h
    · by_cases hr2 : maskSize r = 2
      · have h := RestrictedZeroEvents.actual_four_active_two_zero_mass_le right inverse a r z
          hr2 (by omega) ha (fun c => exactOutputZeros inverse r c.val)
        simpa [zeroCap, hr2, MultibyteColumnNumbers.rho, MultibyteColumnNumbers.atom] using h
      · have hr3 : maskSize r = 3 := by omega
        have h := RestrictedZeroEvents.actual_four_active_three_zero_mass_le right inverse a r z
          hr3 (by omega) ha (fun c => exactOutputZeros inverse r c.val)
        simpa [zeroCap, hr3, MultibyteColumnNumbers.rho, MultibyteColumnNumbers.atom] using h

abbrev SmallMask (t : ℕ) := {r : Fin 16 // 0 < maskSize r ∧ maskSize r < t}

theorem sum_empty_add_small (t : ℕ) (ht : 0 < t) (F : Fin 16 → ℝ)
    (hbig : ∀ r, t ≤ maskSize r → F r = 0) :
    (∑ r : Fin 16, F r) = F 0 + ∑ r : SmallMask t, F r.val := by
  have hs : (∑ r : SmallMask t, F r.val) =
      ∑ r : Fin 16, if 0 < maskSize r ∧ maskSize r < t then F r else 0 :=
    RestrictedSourcePushforward.sum_subtype_eq_restricted_sum _ F
  have hp (r : Fin 16) : F r = (if r = 0 then F 0 else 0) +
      (if 0 < maskSize r ∧ maskSize r < t then F r else 0) := by
    by_cases h0 : r = 0
    · subst r
      simp [show maskSize (0 : Fin 16) = 0 by decide]
    · by_cases hsmall : 0 < maskSize r ∧ maskSize r < t
      · simp [h0, hsmall]
      · have hpos : 0 < maskSize r := by
          have hne : maskSize r ≠ 0 := fun h => h0 ((mask_size_zero r).mp h)
          omega
        have hb : t ≤ maskSize r := by omega
        simp [h0, hsmall, hbig r hb]
  calc
    _ = ∑ r : Fin 16, ((if r = 0 then F 0 else 0) +
        (if 0 < maskSize r ∧ maskSize r < t then F r else 0)) :=
      Finset.sum_congr rfl (fun r _ => hp r)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← hs]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

private def fourBitCount (n : ℕ) : ℕ :=
  (if n % 2 = 1 then 1 else 0) + (if n / 2 % 2 = 1 then 1 else 0) +
    (if n / 4 % 2 = 1 then 1 else 0) + (if n / 8 % 2 = 1 then 1 else 0)

private theorem mask_size_numeric : ∀ r : Fin 16, maskSize r = fourBitCount r.val := by decide
private theorem sum_fin_zero (f : Fin 0 → ℝ) : (∑ i, f i) = 0 := by simp

private theorem sum_fin_sixteen (f : Fin 16 → ℝ) :
    (∑ r : Fin 16, f r) =
      f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 +
        (f 8 + (f 9 + (f 10 + (f 11 + (f 12 + (f 13 + (f 14 + (f 15 + 0))))))))))))))) := by
  simp only [Fin.sum_univ_succ, sum_fin_zero]
  rfl

/-- Symbolic subset-size counting, with arbitrary real data at each size.
No law or large alphabet is enumerated. -/
theorem sum_small_by_size (F : ℕ → ℝ) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) :
    (∑ r : SmallMask t, F (maskSize r.val)) =
      ∑ k ∈ Finset.range (t - 1), (Nat.choose 4 (k + 1) : ℝ) * F (k + 1) := by
  rw [RestrictedSourcePushforward.sum_subtype_eq_restricted_sum
    (fun r : Fin 16 => 0 < maskSize r ∧ maskSize r < t) (fun r => F (maskSize r))]
  rw [sum_fin_sixteen]
  simp_rw [mask_size_numeric]
  obtain ⟨ht0, ht1⟩ := ht
  interval_cases t <;>
    norm_num [fourBitCount, Finset.sum_range_succ, Nat.choose] <;> ring

theorem capped_objective_eq_activityFactor (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) :
    ActivityCollisionBox.collisionObjective
      (fun r : SmallMask t => (255 : ℝ) ^ maskSize r.val)
      (fun r : SmallMask t => zeroCap t (maskSize r.val)) = activityFactor t := by
  unfold ActivityCollisionBox.collisionObjective activityFactor
  rw [sum_small_by_size (fun k => zeroCap t k) t ht,
    sum_small_by_size (fun k => (255 : ℝ) ^ k * zeroCap t k ^ 2) t ht]
  simp only [mul_assoc]

/-- The actual exact-support probabilities satisfy the source's activity
collision cap. No zero-event probability cap is assumed. -/
theorem actual_activity_factor_bound (right : Orientation) (inverse : Bool) (a : Word)
    (z : Fin 16) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (hcount : t + maskSize z = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true) :
    (∑ r : Fin 16, (255 : ℝ) ^ maskSize r * exactMass right inverse a r ^ 2) ≤
      activityFactor t := by
  have ha0 := input_nonzero_of_active_count a z ha (by omega)
  have hbig (r : Fin 16) (hr : t ≤ maskSize r) : exactMass right inverse a r = 0 :=
    exactMass_forbidden right inverse a r z ha0 ha (by omega)
  have hm : exactMass right inverse a 0 +
      (∑ r : SmallMask t, exactMass right inverse a r.val) = 1 := by
    rw [← sum_empty_add_small t (by omega) _ hbig]
    exact exactMass_sum_one right inverse a
  have hw : (∑ r : Fin 16, (255 : ℝ) ^ maskSize r * exactMass right inverse a r ^ 2) =
      exactMass right inverse a 0 ^ 2 + ∑ r : SmallMask t,
        (255 : ℝ) ^ maskSize r.val * exactMass right inverse a r.val ^ 2 := by
    have he := sum_empty_add_small t (by omega)
      (fun r => (255 : ℝ) ^ maskSize r * exactMass right inverse a r ^ 2)
      (fun r hr => by rw [hbig r hr]; simp)
    simpa only [show maskSize (0 : Fin 16) = 0 by decide, pow_zero, one_mul] using he
  rw [hw]
  calc
    _ ≤ ActivityCollisionBox.collisionObjective
        (fun r : SmallMask t => (255 : ℝ) ^ maskSize r.val)
        (fun r : SmallMask t => zeroCap t (maskSize r.val)) := by
      apply ActivityCollisionBox.collision_with_complement_le _ _ _ _ hm
      · intro r
        positivity
      · intro r
        exact exactMass_nonneg right inverse a r.val
      · intro r
        exact exactMass_le_zeroCap right inverse a r.val z t ht hcount ha r.property
      · intro r
        exact MultibyteColumnNumbers.zeroCap_endpoint t (maskSize r.val) ht
          ⟨r.property.1, r.property.2⟩
    _ = _ := capped_objective_eq_activityFactor t ht

end AESConcrete.ActualZeroEventProbabilities
