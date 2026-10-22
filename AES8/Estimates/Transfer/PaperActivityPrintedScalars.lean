import AES8.Reductions.Return.PaperActivityPhysicalJoin

/-! Scalar substitutions from the frozen exact spectral and trace formulae.
All comparisons below reduce to the printed integer inequalities. No older
alternate activity cap is imported as evidence for these bounds. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityPrintedScalars
open AESMixing PaperKernelBounds PaperActivityFullCompression PaperActivityPhysicalJoin
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.ActivityTrace (activityBlock)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def wordQ : ℝ := 2^32

theorem byte_norm_integer :
    10*(256 : ℤ)^2*(6*256+54) < 63*255^3 := by norm_num

theorem word_norm_integer :
    100*(2^32 : ℤ)^2*(6*2^32+54) < 601*(2^32-1)^3 := by norm_num

theorem byte_trace_integer :
    (2^32 : ℤ)*(68*256^2+264*256+68) < 71*255^6 := by norm_num

theorem byte_radius_bound :
    (5*((256 : ℝ)+1)+Real.sqrt (256^2+98*256+1))/(256-1)^3 <
      (63/10 : ℝ)/256^2 := by
  have h := PaperActivitySpectrum.radius_paper_upper (256 : ℝ) (by norm_num)
  apply h.trans
  have hi : 10*(256 : ℝ)^2*(6*256+54) < 63*255^3 := by
    exact_mod_cast byte_norm_integer
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < (256-1)^3)
    (by norm_num : (0 : ℝ) < 256^2)).mpr
  nlinarith

theorem word_radius_bound :
    (5*(wordQ+1)+Real.sqrt (wordQ^2+98*wordQ+1))/(wordQ-1)^3 <
      (601/100 : ℝ)/wordQ^2 := by
  have h := PaperActivitySpectrum.radius_paper_upper wordQ (by norm_num [wordQ])
  apply h.trans
  have hi : 100*wordQ^2*(6*wordQ+54) < 601*(wordQ-1)^3 := by
    norm_num [wordQ]
  apply (div_lt_div_iff₀ (by norm_num [wordQ] : (0 : ℝ) < (wordQ-1)^3)
    (by norm_num [wordQ] : (0 : ℝ) < wordQ^2)).mpr
  nlinarith

theorem byte_hs_bound :
    wordQ*((68*(256 : ℝ)^2+264*256+68)/(256-1)^6) < 71 := by
  have hi : wordQ*(68*(256 : ℝ)^2+264*256+68) < 71*(256-1)^6 := by
    norm_num [wordQ]
  rw [← mul_div_assoc]
  exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < (256-1)^6)).mpr hi

theorem byte_R00_norm (left right : Orientation) (inverse : Bool) :
    ‖kernelOperator (activityBlock (wordKernel left right inverse))‖ <
      (63/10 : ℝ)/256^2 := by
  rw [byte_R00_eq, full_activity_norm (by norm_num [BinaryWord.card]) _
    (byteDiffusionOrientedAddEquiv_zeroMDS inverse)]
  simpa only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] using byte_radius_bound

theorem byte_R00_hs (left right : Orientation) (inverse : Bool) :
    wordQ*(∑ y : AES.Word, ∑ x : AES.Word,
      activityBlock (wordKernel left right inverse) y x ^ 2) < 71 := by
  rw [byte_R00_eq, full_activity_hs (by norm_num [BinaryWord.card]) _
    (byteDiffusionOrientedAddEquiv_zeroMDS inverse)]
  simpa only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] using byte_hs_bound

theorem word_full_norm :
    ‖kernelOperator (fullCenteredKernel AES.wordMix)‖ < (601/100 : ℝ)/wordQ^2 := by
  rw [full_activity_norm (by rw [AES.word_card]; norm_num) _ AES.wordMix_zeroMDS]
  simpa only [AES.word_card, Nat.cast_pow, Nat.cast_ofNat, wordQ] using word_radius_bound

theorem byte_R00_hs_named (left right : Orientation) (inverse : Bool) :
    wordQ*(AESConcrete.HilbertSchmidtEnergy.hs
      (activityBlock (wordKernel left right inverse)))^2 < 71 := by
  rw [AESConcrete.HilbertSchmidtEnergy.hs_sq]
  exact byte_R00_hs left right inverse

end AES8.PaperActivityPrintedScalars
