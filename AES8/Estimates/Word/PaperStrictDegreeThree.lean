import AES8.Math.PaperStrictGramMargin
import AESConcrete.DampedDegreeThree
import AESConcrete.ReverseDegreeThree

/-!
# Strict physical degree-three boundary from the retained Gram margins

The existing exact certificate supplies strictly positive weighted row
margins. This leaf retains that strictness, obtains a uniformly smaller
coefficient without selecting a new numerical constant, and composes the
existing frame reconstruction and actual transpose identity. All left/right
byte orientations and both physical diffusion directions are quantified.

This proves the endpoint by the inherited weighted-row route. The frozen
paper's parity-block derivation has separate correspondence obligations.
No manuscript, vendor, canonical source or live certificate run is edited.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperStrictDegreeThree
open AESMixing AESConcrete
open AESConcrete.ShortenedLineResponse (Byte)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ActivityEffectiveMetric
open AESConcrete.ActivityGramDominance
open AESConcrete.ActualDegreeThreeGram
open AESConcrete.DegreeThreeFrameEnergy
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The strict finite certificate gives a smaller Gram scalar; no new
fixed rational cap is searched for or asserted. -/
theorem exists_strict_gram_scalar (left right : Orientation) (inverse : Bool) :
    ∃ c : ℝ, 0 < c ∧ c < comparisonLambda ∧ ∀ u : Fin 16 → ℝ,
      qForm u (degreeThreeGram left right inverse) ≤ c * fullEnergy u := by
  let H : Interior → Interior → ℝ := fun A B => effectiveMetric A.val B.val
  let G : Interior → Interior → ℝ :=
    fun A B => degreeThreeGram left right inverse A.val B.val
  let M : Interior → Interior → ℝ := fun A B => comparisonLambda * H A B - G A B
  let w : Interior → ℝ := fun A => rowWeight A.val
  have hH (A B : Interior) : H A B = H B A :=
    DampedDegreeThree.effectiveMetric_symmetric A.val B.val
  have hM (A B : Interior) : M A B = M B A := by
    dsimp [M, G]
    rw [hH A B, degreeThreeGram_symmetric]
  have hrow (A : Interior) :
      0 < M A A * w A - PaperStrictGramMargin.offWeight M w A := by
    have h := weighted_row_dominance (degreeThreeGram left right inverse)
      (DampedDegreeThree.actual_entry_bounds left right inverse) A
    have he (B : Interior) :
        (if B.val = A.val then (0 : ℝ) else
          rowWeight B.val * |comparisonLambda * effectiveMetric A.val B.val -
            degreeThreeGram left right inverse A.val B.val|) =
        if A = B then 0 else |M A B| * w B := by
      by_cases hab : A = B
      · subst B
        simp
      · have hv : B.val ≠ A.val := fun hv => hab (Subtype.ext hv.symm)
        simp only [hv, hab, if_false, M, H, G, w]
        ring
    simp_rw [he] at h
    dsimp [PaperStrictGramMargin.offWeight, M, H, G, w] at *
    linarith
  obtain ⟨e, he, helimit, hpositive⟩ := PaperStrictGramMargin.exists_positive_shift
    M H w hM hH (fun A => rowWeight_pos A.val) hrow
    (comparisonLambda / 2) (by norm_num [comparisonLambda])
  have hc : 0 < comparisonLambda - e := by
    have hl : 0 < comparisonLambda := by norm_num [comparisonLambda]
    linarith
  refine ⟨comparisonLambda - e, hc, by linarith, ?_⟩
  intro u
  have hp := hpositive (fun A => u A.val)
  have heq : (∑ A : Interior, ∑ B : Interior,
      u A.val * u B.val * (M A B - e * H A B)) =
      (comparisonLambda - e) * effectiveEnergy u -
        qForm (fun A : Interior => u A.val) G := by
    calc
      _ = ∑ A : Interior, ∑ B : Interior,
          ((comparisonLambda - e) * (u A.val * u B.val * H A B) -
            u A.val * u B.val * G A B) := by
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        dsimp [M]
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
  rw [heq] at hp
  rw [degreeThreeGram_interior]
  calc
    _ ≤ (comparisonLambda - e) * effectiveEnergy u := by linarith
    _ ≤ (comparisonLambda - e) * fullEnergy u :=
      mul_le_mul_of_nonneg_left (effectiveEnergy_le_fullEnergy u) hc.le

/-- One uniform energy constant strictly below the printed boundary exists
for every physical orientation. This avoids an unjustified inference from
pointwise strict contraction to strict operator norm. -/
theorem exists_frame_energy_scalar (left right : Orientation) (inverse : Bool) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 33 / (10 * 65536) ∧ ∀ u : Fin 16 → ℝ,
      (∑ y, (outputSynthesis left right inverse u y)^2) ≤
        c^2 * ∑ x, (frameSynthesis u x)^2 := by
  obtain ⟨a, ha, halt, hgram⟩ := exists_strict_gram_scalar left right inverse
  let c : ℝ := Real.sqrt a / 65536
  have hc : 0 ≤ c := div_nonneg (Real.sqrt_nonneg a) (by norm_num)
  have hroot : Real.sqrt a < (33 / 10 : ℝ) := by
    have hs := Real.sq_sqrt ha.le
    have hn := Real.sqrt_nonneg a
    norm_num [comparisonLambda] at halt
    nlinarith
  have hcap : c < 33 / (10 * 65536) := by
    dsimp [c]
    have h := div_lt_div_of_pos_right hroot (by norm_num : (0 : ℝ) < 65536)
    norm_num at h ⊢
    exact h
  have hc2 : c^2 = a / 4294967296 := by
    dsimp [c]
    rw [div_pow, Real.sq_sqrt ha.le]
    norm_num
  refine ⟨c, hc, hcap, ?_⟩
  intro u
  have h := hgram u
  rw [← outputSynthesis_energy, ← frameSynthesis_energy] at h
  rw [hc2]
  nlinarith

theorem exists_forward_energy_scalar (left right : Orientation) (inverse : Bool) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 33 / (10 * 65536) ∧
      ∀ f : (Fin 4 → Byte) → ℝ,
      (∑ y, (action (DampedDegreeThree.forwardBlockKernel left right inverse) f y)^2) ≤
        c^2 * ∑ x, (f x)^2 := by
  obtain ⟨c, hc, hcap, hframe⟩ := exists_frame_energy_scalar left right inverse
  refine ⟨c, hc, hcap, ?_⟩
  intro f
  have h := hframe (normalizedCoefficients f)
  simp only [outputSynthesis_eq, ← normalized_reconstruction] at h
  simp only [DampedDegreeThree.forwardBlockKernel, kernelCompose_action, degreeKernel_action]
  exact h.trans (mul_le_mul_of_nonneg_left
    (degreeComponent_energy_le (0 : Byte) (by norm_num [BinaryWord.card]) 0 f)
    (sq_nonneg c))

theorem forward_operator_norm_lt (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (DampedDegreeThree.forwardBlockKernel left right inverse)‖ <
      (33 / (10 * 65536) : ℝ) := by
  obtain ⟨c, hc, hcap, henergy⟩ := exists_forward_energy_scalar left right inverse
  exact (kernelOperator_norm_le _ hc henergy).trans_lt hcap

theorem exists_reverse_energy_scalar (left right : Orientation) (inverse : Bool) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 33 / (10 * 65536) ∧
      ∀ f : (Fin 4 → Byte) → ℝ,
      (∑ y, (action (ReverseDegreeThree.reverseBlockKernel left right inverse) f y)^2) ≤
        c^2 * ∑ x, (f x)^2 := by
  obtain ⟨c, hc, hcap, henergy⟩ := exists_forward_energy_scalar
    (ReverseDegreeThree.transposeOrientation right)
    (ReverseDegreeThree.transposeOrientation left) (!inverse)
  exact ⟨c, hc, hcap, adjoint_energy_le _ _ c
    (ReverseDegreeThree.forward_reverse_adjoint left right inverse) henergy⟩

theorem reverse_operator_norm_lt (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (ReverseDegreeThree.reverseBlockKernel left right inverse)‖ <
      (33 / (10 * 65536) : ℝ) := by
  obtain ⟨c, hc, hcap, henergy⟩ := exists_reverse_energy_scalar left right inverse
  exact (kernelOperator_norm_le _ hc henergy).trans_lt hcap

end AES8.PaperStrictDegreeThree
