import AES8.Recurrence.PaperComparisonCertificate
import AES8.Recurrence.PaperProfileAssembly
import AES8.Consequences.PaperCurrentBound

/-!
# From the current physical estimates to the exact current theorem

The rational matrices and all four parity tests are the frozen paper's current
ones. This leaf derives the starting comparison, alternating bounds and final
consequence on the actual AES profiles. Only physical step/return/first-source
caps and the four-round startup remain premises. They are displayed explicitly;
this file does not claim their concrete proof or hide them in a final bound.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperCurrentRecurrence
open AESMixing AESMixing.AES
open AESRound (matVec matVec_mono matVec_scale)
open PaperComparison

/-- Remaining physical input to the current proof, before profile assembly. -/
structure PhysicalEstimates : Prop where
  transfer : PaperProfileAssembly.PhysicalCaps realStep realReturn (realProfile firstReturn)
  initial : ∀ a : AES.State, a ≠ 0 → ∀ i : Fin 14,
    NormalizedProfile.factor 0 * SupportProfile.actual a 0 i ≤
      d i * (1000 * realProfile startup0 i)

theorem current_high_zero (i : Fin 14) (k : Fin 3) :
    realStep i (Fin.natAdd 11 k) = 0 := by
  unfold realStep
  have h := step_high_columns i k
  have he : (⟨k.val + 11, by omega⟩ : Fin 14) = Fin.natAdd 11 k := by
    apply Fin.ext
    change k.val + 11 = 11 + k.val
    omega
  rw [he] at h
  rw [h, Rat.cast_zero]

theorem actual_transfer (h : PhysicalEstimates) :
    PaperProfileAssembly.ActualTransfer realStep realReturn (realProfile firstReturn) :=
  PaperProfileAssembly.transferEstimates h.transfer current_high_zero

theorem actual_initial (h : PhysicalEstimates) (a : AES.State) (ha : a ≠ 0) :
    NormalizedProfile.actual a 0 ≤ AES8.scale 1000 (realProfile startup0) :=
  PaperProfileAssembly.normalized_initial _ a (h.initial a ha)

/-- Reusable positive two-map comparison, independent of AES or table values. -/
theorem scaled_update {B C : Fin 14 → Fin 14 → ℝ}
    (hB : AESRound.EntrywiseNonnegative B) (hC : AESRound.EntrywiseNonnegative C)
    {x y u v : AES8.Profile} (hx : x ≤ AES8.scale 1000 u)
    (hy : y ≤ AES8.scale 1000 v) (i : Fin 14) :
    matVec B x i + matVec C y i ≤
      1000 * (matVec B u i + matVec C v i) := by
  calc
    _ ≤ matVec B (AES8.scale 1000 u) i + matVec C (AES8.scale 1000 v) i :=
      add_le_add (matVec_mono hB hx i) (matVec_mono hC hy i)
    _ = _ := by
      change matVec B (fun k => 1000 * u k) i + matVec C (fun k => 1000 * v k) i = _
      rw [matVec_scale, matVec_scale]
      ring

theorem actual_first (h : PhysicalEstimates) (a : AES.State) (ha : a ≠ 0) :
    NormalizedProfile.actual a 1 ≤ AES8.scale 1000 (realProfile startup1) := by
  intro i
  have ht := (actual_transfer h).first a ha i
  have hm := matVec_mono realStep_nonneg (actual_initial h a ha) i
  calc
    _ ≤ matVec realStep (AES8.scale 1000 (realProfile startup0)) i +
        1000 * realProfile firstReturn i := ht.trans (add_le_add hm le_rfl)
    _ = _ := by
      rw [startup1_real]
      change matVec realStep (fun k => 1000 * realProfile startup0 k) i +
        1000 * realProfile firstReturn i =
        1000 * (matVec realStep (realProfile startup0) i + realProfile firstReturn i)
      rw [matVec_scale]
      ring

theorem actual_second (h : PhysicalEstimates) (a : AES.State) (ha : a ≠ 0) :
    NormalizedProfile.actual a 2 ≤ AES8.scale 1000 (realProfile startup2) := by
  intro i
  have hm := (actual_transfer h).step a ha 0 i
  have hs := scaled_update realStep_nonneg realReturn_nonneg
    (actual_first h a ha) (actual_initial h a ha) i
  apply hm.trans
  rw [startup2_real]
  exact hs

theorem actual_third (h : PhysicalEstimates) (a : AES.State) (ha : a ≠ 0) :
    NormalizedProfile.actual a 3 ≤ AES8.scale 1000 (realProfile startup3) := by
  intro i
  have hm := (actual_transfer h).step a ha 1 i
  have hs := scaled_update realStep_nonneg realReturn_nonneg
    (actual_second h a ha) (actual_first h a ha) i
  apply hm.trans
  rw [startup3_real]
  exact hs

/-- The current finite tests, instantiated in the actual normalized recurrence. -/
theorem actual_parity (h : PhysicalEstimates) (a : AES.State) (ha : a ≠ 0) :
    ∀ k, (NormalizedProfile.actual a (2 * k + 2) ≤
      AES8.scale 1000 PaperOutputEnvelopes.evenEnvelope) ∧
      (NormalizedProfile.actual a (2 * k + 3) ≤
        AES8.scale 1000 PaperOutputEnvelopes.oddEnvelope) := by
  apply PaperParityInduction.parity_bounds realStep_nonneg realReturn_nonneg
    ((actual_transfer h).step a ha)
    invariant_even_bound_real invariant_odd_bound_real
  · intro i
    exact (actual_second h a ha i).trans
      (mul_le_mul_of_nonneg_left (startup_even_bound_real i) (by norm_num))
  · intro i
    exact (actual_third h a ha i).trans
      (mul_le_mul_of_nonneg_left (startup_odd_bound_real i) (by norm_num))

theorem actual_boxes (h : PhysicalEstimates) : PaperCurrentBound.ActualBoxes :=
  fun a ha j hj => PaperParityInduction.box_of_parity (actual_parity h a ha) j hj

/-- The current paper constant follows from its four physical estimates;
all rational map tests and the profile-to-distance deduction are discharged. -/
theorem epsilon_eight_plus_two (h : PhysicalEstimates) (k : ℕ) :
    AES.epsilon (8 + 2 * k) < PaperCurrentBound.bound k :=
  PaperCurrentBound.epsilon_eight_plus_two (actual_boxes h) k

theorem round_corollaries (h : PhysicalEstimates) :
    AES.epsilon 10 < (1 : ℝ) / 2 ^ (128 : ℕ) ∧
    AES.epsilon 14 < (1 : ℝ) / 2 ^ (192 : ℕ) ∧
    AES.epsilon 16 < (1 : ℝ) / 2 ^ (256 : ℕ) :=
  ⟨PaperCurrentBound.ten_round_128 (actual_boxes h),
    PaperCurrentBound.fourteen_round_192 (actual_boxes h),
    PaperCurrentBound.sixteen_round_256 (actual_boxes h)⟩

end AES8.PaperCurrentRecurrence
