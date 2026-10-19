import AESMixing.CharacterSubgroup
import AESMixing.ByteCharacter

/-! The nondegenerate pairing used by code duality, on actual AES bytes and words. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def bytePairing : CharacterPairing (BinaryWord 8) where
  value x y := byteCharacter (x*y)
  zero_right x := by rw [mul_zero, byteCharacter_zero]
  add_right x y z := by rw [mul_add, byteCharacter_add]
  symmetric x y := by rw [mul_comm]
  nondegenerate x hx := by
    refine ⟨x⁻¹ * (⟨32⟩ : BinaryWord 8), ?_⟩
    rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul, byteCharacter_witness]
    norm_num

def CharacterPairing.product {V : Type*} [AddCommGroup V] (B : CharacterPairing V)
    (I : Type*) [Fintype I] [DecidableEq I] : CharacterPairing (I → V) where
  value x y := ∏ i, B.value (x i) (y i)
  zero_right x := by simp [B.zero_right]
  add_right x y z := by
    simp only [Pi.add_apply, B.add_right, Finset.prod_mul_distrib]
  symmetric x y := by
    apply Finset.prod_congr rfl
    intro i _
    exact B.symmetric (x i) (y i)
  nondegenerate x hx := by
    classical
    have hw : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    obtain ⟨i,hi⟩ := hw
    obtain ⟨v,hv⟩ := B.nondegenerate (x i) hi
    refine ⟨fun j => if j = i then v else 0, ?_⟩
    have he : (∏ j, B.value (x j) (if j = i then v else 0)) = B.value (x i) v := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hji
        simp [hji, B.zero_right]
      · simp
    rw [he]
    exact hv

def wordPairing : CharacterPairing (Fin 4 → BinaryWord 8) := bytePairing.product (Fin 4)

theorem word_add_self (x : Fin 4 → BinaryWord 8) : x+x = 0 := by
  funext i
  exact BinaryWord.add_self (x i)

end AESMixing
