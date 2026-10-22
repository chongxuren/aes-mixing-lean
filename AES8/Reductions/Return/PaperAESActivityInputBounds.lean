import AES8.Reductions.Return.PaperAESActivityInputJoin

/-! Proper-branch support and moment bounds for the literal physical responses.
The Boolean support is derived from the actual shortening cardinality. No
activity-input norm or response norm is supplied as an assumption. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputBounds
open AESMixing PaperWordGraphCode PaperAESActivityIdentification
open PaperAESActivityInputResponse PaperAESActivityInputJoin
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

def totalWeight (O A B : Finset (Fin 4)) : ℕ := B.card + (A \ O).card

theorem outputMarked_card (O : Finset (Fin 4)) : (outputMarked O).card = O.card := by
  simp [outputMarked,marked]

theorem uniform_card (O A B : Finset (Fin 4)) :
    (uniform O ∅ A B).card = totalWeight O A B := by
  simp [uniform,totalWeight]

theorem zero_count (O A B : Finset (Fin 4)) :
    (zeroPositions (outputMarked O) (uniform O ∅ A B)).card +
      O.card + totalWeight O A B = 8 := by
  have h := signed_dimension (outputMarked O) (uniform O ∅ A B)
    (marked_uniform_disjoint O ∅ A B)
  rw [outputMarked_card,uniform_card] at h
  omega

theorem frameResponse_zero (O A B : Finset (Fin 4))
    (hO : 0 < O.card) (hz : 4 ≤ (zeroPositions (outputMarked O) (uniform O ∅ A B)).card)
    (adjoint : Bool) : frameResponse O A B adjoint = 0 := by
  have h := response_zero_branch (outputMarked O) (uniform O ∅ A B)
    (by simpa only [outputMarked_card] using hO) hz adjoint
  funext y
  rw [frameResponse_eq,h]
  rfl

theorem frameResponse_full (O A B : Finset (Fin 4))
    (hO : 0 < O.card)
    (hf : (zeroPositions (outputMarked O) (uniform O ∅ A B)).card + O.card ≤ 4)
    (adjoint : Bool) : frameResponse O A B adjoint = 0 := by
  have h := response_full_branch (outputMarked O) (uniform O ∅ A B)
    (by simpa only [outputMarked_card] using hO)
    (by simpa only [outputMarked_card] using hf) adjoint
  funext y
  rw [frameResponse_eq,h]
  rfl

/-- A nonzero response must have strict shortened dimension, expressed in
literal input and omitted-output frame weights. -/
theorem frameResponse_supported (O A B : Finset (Fin 4))
    (hO : 0 < O.card)
    (hbad : ¬ (4 < O.card + totalWeight O A B ∧ totalWeight O A B < 4))
    (adjoint : Bool) : frameResponse O A B adjoint = 0 := by
  have hz := zero_count O A B
  by_cases hsmall : O.card + totalWeight O A B ≤ 4
  · exact frameResponse_zero O A B hO (by omega) adjoint
  · exact frameResponse_full O A B hO (by omega) adjoint

theorem degree_one_response (O A B : Finset (Fin 4)) (hO : O.card = 1)
    (adjoint : Bool) : frameResponse O A B adjoint = 0 :=
  frameResponse_supported O A B (by omega) (by omega) adjoint

theorem degree_two_response_energy (O A B : Finset (Fin 4)) (hO : O.card = 2)
    (adjoint : Bool) :
    (∑ y : O → AES.Word, frameResponse O A B adjoint y ^ 2) ≤
      if totalWeight O A B = 3 then tau^2/wordQ^3 else 0 := by
  by_cases hw : totalWeight O A B = 3
  · rw [if_pos hw]
    have hz := zero_count O A B
    have h := frameResponse_energy O A B 1 (by omega) (by omega) (by omega) adjoint
    simpa [hO,responseMoment,div_pow,div_div,pow_succ,mul_comm,
      mul_left_comm,mul_assoc] using h
  · rw [if_neg hw,frameResponse_supported O A B (by omega) (by omega) adjoint]
    simp

theorem degree_three_response_energy (O A B : Finset (Fin 4)) (hO : O.card = 3)
    (adjoint : Bool) :
    (∑ y : O → AES.Word, frameResponse O A B adjoint y ^ 2) ≤
      if totalWeight O A B = 2 ∨ totalWeight O A B = 3
        then tau^2*beta/wordQ^2 else 0 := by
  by_cases hw : totalWeight O A B = 2 ∨ totalWeight O A B = 3
  · rw [if_pos hw]
    have hz := zero_count O A B
    rcases hw with hw | hw
    · have h := frameResponse_energy O A B 1 (by omega) (by omega) (by omega) adjoint
      apply h.trans_eq
      simp only [hO,responseMoment]
      norm_num
      ring
    · have h := frameResponse_energy O A B 2 (by omega) (by omega) (by omega) adjoint
      apply h.trans_eq
      simp only [hO,responseMoment]
      norm_num
      ring
  · rw [if_neg hw,frameResponse_supported O A B (by omega) (by omega) adjoint]
    simp

theorem degree_four_response_energy (O A B : Finset (Fin 4)) (hO : O.card = 4)
    (adjoint : Bool) :
    (∑ y : O → AES.Word, frameResponse O A B adjoint y ^ 2) ≤
      (if totalWeight O A B = 1 ∨ totalWeight O A B = 3
        then tau^2*beta^2/wordQ else 0) +
      (if totalWeight O A B = 2 then tau^4/wordQ^2 else 0) := by
  have hz := zero_count O A B
  by_cases hl : totalWeight O A B = 1 ∨ totalWeight O A B = 3
  · rw [if_pos hl,if_neg (by omega),add_zero]
    rcases hl with hw | hw
    · have h := frameResponse_energy O A B 1 (by omega) (by omega) (by omega) adjoint
      apply h.trans_eq
      simp only [hO,responseMoment]
      norm_num
      ring
    · have h := frameResponse_energy O A B 3 (by omega) (by omega) (by omega) adjoint
      apply h.trans_eq
      simp only [hO,responseMoment]
      norm_num
      ring
  · rw [if_neg hl,zero_add]
    by_cases hp : totalWeight O A B = 2
    · rw [if_pos hp]
      have h := frameResponse_energy O A B 2 (by omega) (by omega) (by omega) adjoint
      apply h.trans_eq
      simp only [hO,responseMoment]
      norm_num
      ring
    · rw [if_neg hp,frameResponse_supported O A B (by omega) (by omega) adjoint]
      simp

end AES8.PaperAESActivityInputBounds
