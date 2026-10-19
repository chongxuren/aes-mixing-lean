import AESMixing.Generated.GramTable_I
import AESMixing.CenteredDegree
import AESMixing.RationalGram

/-! Inverse MixColumns activity bounds for arbitrary input vectors. The
matrix entries here are connected to the concrete permutation by the
exhaustively checked rank table. No AES mixing estimate is a hypothesis. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem inverse_activity_certificate_two (a b : Fin 16) :
    (7/500 : ℝ)^2 * 256^AES.maskSize (maskIntersection a b) -
      gram (fun y a => degreeComponent 0 2
        (diffusedActivityColumn (byteDiffusionOrientation true) a) y) a b =
      ∑ k, (GramNumeric.I2.weights k : ℝ) *
        (GramNumeric.I2.rows k a : ℝ) * (GramNumeric.I2.rows k b : ℝ) := by
  rw [GramTable.I.numeric_entries_2]
  have h := congrArg (fun x : ℚ => (x : ℝ)) (GramNumeric.I2.factorization a b)
  simp only [GramNumeric.I2.bound, GramNumeric.I2.metric] at h
  push_cast at h
  exact h

theorem inverse_activity_certificate_three (a b : Fin 16) :
    (9/50 : ℝ)^2 * 256^AES.maskSize (maskIntersection a b) -
      gram (fun y a => degreeComponent 0 3
        (diffusedActivityColumn (byteDiffusionOrientation true) a) y) a b =
      ∑ k, (GramNumeric.I3.weights k : ℝ) *
        (GramNumeric.I3.rows k a : ℝ) * (GramNumeric.I3.rows k b : ℝ) := by
  rw [GramTable.I.numeric_entries_3]
  have h := congrArg (fun x : ℚ => (x : ℝ)) (GramNumeric.I3.factorization a b)
  simp only [GramNumeric.I3.bound, GramNumeric.I3.metric] at h
  push_cast at h
  exact h

theorem inverse_activity_certificate_zero (a b : Fin 16) :
    (1/10400 : ℝ)^2 * 256^AES.maskSize (maskIntersection a b) -
      gram (fun y a => centeredActivityResponse
        (byteDiffusionOrientation true) a y) a b =
      ∑ k, (GramNumeric.I0.weights k : ℝ) *
        (GramNumeric.I0.rows k a : ℝ) * (GramNumeric.I0.rows k b : ℝ) := by
  rw [centered_activity_gram (by norm_num [BinaryWord.card]) _
    (byteDiffusionOrientation_zero true), GramTable.I.numeric_entries_0]
  have h := congrArg (fun x : ℚ => (x : ℝ)) (GramNumeric.I0.factorization a b)
  simp only [GramNumeric.I0.bound, GramNumeric.I0.metric, GramNumeric.I0.fixed] at h
  push_cast at h
  norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
  unfold invariantActivityGram
  linarith [h]

theorem inverse_activity_degree_two_energy (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ y, degreeComponent 0 2 (fun x => degreeComponent 0 0 f
      ((byteDiffusionOrientation true).symm x)) y^2) ≤
      (7/500 : ℝ)^2 * ∑ y, degreeComponent 0 0 f y^2 := by
  apply activity_transfer_from_gram_certificate _ 2
    (fun k a => (GramNumeric.I2.rows k a : ℝ))
    (fun k => (GramNumeric.I2.weights k : ℝ)) (7/500) ?_ ?_ f
  · intro k
    exact_mod_cast le_of_lt (GramNumeric.I2.weights_positive k)
  · intro a b
    norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
    convert inverse_activity_certificate_two a b using 1; norm_num

theorem inverse_activity_degree_three_energy (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ y, degreeComponent 0 3 (fun x => degreeComponent 0 0 f
      ((byteDiffusionOrientation true).symm x)) y^2) ≤
      (9/50 : ℝ)^2 * ∑ y, degreeComponent 0 0 f y^2 := by
  apply activity_transfer_from_gram_certificate _ 3
    (fun k a => (GramNumeric.I3.rows k a : ℝ))
    (fun k => (GramNumeric.I3.weights k : ℝ)) (9/50) ?_ ?_ f
  · intro k
    exact_mod_cast le_of_lt (GramNumeric.I3.weights_positive k)
  · intro a b
    norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
    convert inverse_activity_certificate_three a b using 1; norm_num

theorem inverse_activity_degree_zero_energy (f : (Fin 4 → BinaryWord 8) → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ y, degreeComponent 0 0 (fun x => degreeComponent 0 0 f
      ((byteDiffusionOrientation true).symm x)) y^2) ≤
      (1/10400 : ℝ)^2 * ∑ y, degreeComponent 0 0 f y^2 := by
  have hn : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have h := centered_activity_transfer_from_gram_certificate
    (byteDiffusionOrientation true)
    (fun k a => (GramNumeric.I0.rows k a : ℝ))
    (fun k => (GramNumeric.I0.weights k : ℝ)) (1/10400)
    (fun k => by exact_mod_cast le_of_lt (GramNumeric.I0.weights_positive k))
    (fun a b => by
      norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
      convert inverse_activity_certificate_zero a b using 1; norm_num) f
  rw [degree_zero_diffusion_centered hn _ (byteDiffusionOrientation_zero true) f hz hs] at h
  exact h

theorem inverse_activity_gram_one (a b : Fin 16) :
    gram (fun y a => degreeComponent 0 1
      (diffusedActivityColumn (byteDiffusionOrientation true) a) y) a b = 0 := by
  have h := GramTable.I.gram_entries 1 a b
  rw [GramTable.I.degree_one_zero] at h
  simpa only [gram, Int.cast_zero, zero_div] using h

theorem inverse_activity_degree_one_energy (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ y, degreeComponent 0 1 (fun x => degreeComponent 0 0 f
      ((byteDiffusionOrientation true).symm x)) y^2) ≤ 0 := by
  have h := activity_transfer_from_gram_certificate
    (byteDiffusionOrientation true) 1 (fun _ : Fin 1 => fun _ : Fin 16 => (0 : ℝ))
    (fun _ => (0 : ℝ)) 0 (fun _ => le_refl 0)
    (fun a b => by simp [inverse_activity_gram_one]) f
  simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul] using h

#print axioms inverse_activity_degree_zero_energy
#print axioms inverse_activity_degree_one_energy
#print axioms inverse_activity_degree_two_energy
#print axioms inverse_activity_degree_three_energy
end AESMixing
