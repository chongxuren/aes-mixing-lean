import AESMixing.Generated.GramTable_F
import AESMixing.Generated.GramTable_I
import AESMixing.CenteredDegree
import AESMixing.RationalGram
import AESMixing.DegreeAdjoint
import AESConcrete.Generated.SharpGram_F0
import AESConcrete.Generated.SharpGram_I0

/-!
# Sharper concrete degree-zero activity transfer

Only the successful exact degree-zero Gram certificates are used here.
The theorem concerns actual forward/inverse MixColumns on the byte alphabet.
It does not establish the sharper damped degree-three word block or the
certificate-strength full word norm21/131072.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.SharpActivityZero
open AESMixing

theorem forward_activity_certificate_zero (a b : Fin 16) :
    (63/655360 : ℝ)^2 * 256^AES.maskSize (maskIntersection a b) -
      gram (fun y a => centeredActivityResponse
        (byteDiffusionOrientation false) a y) a b =
      ∑ k, (SharpGram.F0.weights k : ℝ) *
        (SharpGram.F0.rows k a : ℝ) * (SharpGram.F0.rows k b : ℝ) := by
  rw [centered_activity_gram (by norm_num [BinaryWord.card]) _
    (byteDiffusionOrientation_zero false), GramTable.F.numeric_entries_0]
  have h := congrArg (fun x : ℚ => (x : ℝ)) (SharpGram.F0.factorization a b)
  simp only [SharpGram.F0.bound, GramNumeric.F0.metric, GramNumeric.F0.fixed] at h
  push_cast at h
  norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
  unfold invariantActivityGram
  linarith [h]

theorem forward_activity_degree_zero_energy (f : (Fin 4 → BinaryWord 8) → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ y, degreeComponent 0 0 (fun x => degreeComponent 0 0 f
      ((byteDiffusionOrientation false).symm x)) y^2) ≤
      (63/655360 : ℝ)^2 * ∑ y, degreeComponent 0 0 f y^2 := by
  have hn : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have h := centered_activity_transfer_from_gram_certificate
    (byteDiffusionOrientation false)
    (fun k a => (SharpGram.F0.rows k a : ℝ))
    (fun k => (SharpGram.F0.weights k : ℝ)) (63/655360)
    (fun k => by exact_mod_cast le_of_lt (SharpGram.F0.weights_positive k))
    (fun a b => by
      norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
      convert forward_activity_certificate_zero a b using 1; norm_num) f
  rw [degree_zero_diffusion_centered hn _ (byteDiffusionOrientation_zero false) f hz hs] at h
  exact h

theorem inverse_activity_certificate_zero (a b : Fin 16) :
    (63/655360 : ℝ)^2 * 256^AES.maskSize (maskIntersection a b) -
      gram (fun y a => centeredActivityResponse
        (byteDiffusionOrientation true) a y) a b =
      ∑ k, (SharpGram.I0.weights k : ℝ) *
        (SharpGram.I0.rows k a : ℝ) * (SharpGram.I0.rows k b : ℝ) := by
  rw [centered_activity_gram (by norm_num [BinaryWord.card]) _
    (byteDiffusionOrientation_zero true), GramTable.I.numeric_entries_0]
  have h := congrArg (fun x : ℚ => (x : ℝ)) (SharpGram.I0.factorization a b)
  simp only [SharpGram.I0.bound, GramNumeric.I0.metric, GramNumeric.I0.fixed] at h
  push_cast at h
  norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
  unfold invariantActivityGram
  linarith [h]

theorem inverse_activity_degree_zero_energy (f : (Fin 4 → BinaryWord 8) → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ y, degreeComponent 0 0 (fun x => degreeComponent 0 0 f
      ((byteDiffusionOrientation true).symm x)) y^2) ≤
      (63/655360 : ℝ)^2 * ∑ y, degreeComponent 0 0 f y^2 := by
  have hn : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have h := centered_activity_transfer_from_gram_certificate
    (byteDiffusionOrientation true)
    (fun k a => (SharpGram.I0.rows k a : ℝ))
    (fun k => (SharpGram.I0.weights k : ℝ)) (63/655360)
    (fun k => by exact_mod_cast le_of_lt (SharpGram.I0.weights_positive k))
    (fun a b => by
      norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]
      convert inverse_activity_certificate_zero a b using 1; norm_num) f
  rw [degree_zero_diffusion_centered hn _ (byteDiffusionOrientation_zero true) f hz hs] at h
  exact h

theorem sharp_activity_zero_energy (inverse : Bool)
    (f : (Fin 4 → BinaryWord 8) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, degreeTransfer 0 0 0 (byteDiffusionOrientation inverse) f x ^ 2) ≤
      (63 / 655360 : ℝ) ^ 2 * ∑ x, degreeComponent 0 0 f x ^ 2 := by
  cases inverse
  · exact forward_activity_degree_zero_energy f hz hs
  · exact inverse_activity_degree_zero_energy f hz hs

end AESConcrete.SharpActivityZero
