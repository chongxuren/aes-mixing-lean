import AESMixing.FourierChannel
import AESMixing.AESByteNorm

/-! Every additive equivalence permutes the byte characters. The dual map is
obtained from orthogonality, without an assumed transpose table. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem byteCharacter_sq (x : BinaryWord 8) : byteCharacter x ^ 2 = 1 := by
  have h := byteCharacter_add x x
  rw [BinaryWord.add_self, byteCharacter_zero] at h
  nlinarith

theorem exists_byte_character_index (f : BinaryWord 8 → ℝ) (hf0 : f 0 = 1)
    (hfadd : ∀ x y, f (x + y) = f x * f y) :
    ∃ v : BinaryWord 8, ∀ x, f x = byteCharacter (v * x) := by
  have hs (x : BinaryWord 8) : (∑ v, byteCharacter (v * x)) =
      if x = 0 then 256 else 0 := by
    have h := real_character_scaled_sum byteCharacter byteCharacter_zero byteCharacter_sum x
    norm_num only [BinaryWord.card] at h
    exact h
  have htotal : (∑ v : BinaryWord 8, ∑ x, f x * byteCharacter (v * x)) = 256 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hs, mul_ite, mul_zero]
    simp [hf0]
  obtain ⟨v, hv⟩ : ∃ v : BinaryWord 8, (∑ x, f x * byteCharacter (v * x)) ≠ 0 := by
    by_contra h
    push Not at h
    simp_rw [h] at htotal
    norm_num at htotal
  refine ⟨v, ?_⟩
  let g : BinaryWord 8 → ℝ := fun x => f x * byteCharacter (v * x)
  have hgadd (x y : BinaryWord 8) : g (x + y) = g x * g y := by
    dsimp only [g]
    rw [hfadd, mul_add, byteCharacter_add]
    ring
  have hg (w : BinaryWord 8) : g w = 1 := by
    have he := Equiv.sum_comp (Equiv.addLeft w) g
    change (∑ x, g (w + x)) = ∑ x, g x at he
    simp_rw [hgadd, ← Finset.mul_sum] at he
    apply mul_right_cancel₀ hv
    simpa only [one_mul] using he
  intro x
  calc
    f x = f x * byteCharacter (v * x)^2 := by rw [byteCharacter_sq, mul_one]
    _ = g x * byteCharacter (v * x) := by dsimp only [g]; ring
    _ = byteCharacter (v * x) := by rw [hg, one_mul]

theorem byte_character_index_unique (a b : BinaryWord 8)
    (h : ∀ x, byteCharacter (a * x) = byteCharacter (b * x)) : a = b := by
  have hg := character_matrix_gram byteCharacter byteCharacter_zero byteCharacter_add
    byteCharacter_sum BinaryWord.add_self a b
  have hp (x : BinaryWord 8) : byteCharacter (x * a) * byteCharacter (x * b) = 1 := by
    rw [mul_comm x a, mul_comm x b, h]
    simpa only [pow_two] using byteCharacter_sq (b * x)
  simp only [gram, characterMatrix, hp, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, BinaryWord.card] at hg
  by_contra hab
  norm_num [hab] at hg

def byteCharacterDual (A : BinaryWord 8 ≃+ BinaryWord 8) (v : BinaryWord 8) : BinaryWord 8 :=
  Classical.choose (exists_byte_character_index (fun x => byteCharacter (v * A x))
    (by rw [map_zero, mul_zero, byteCharacter_zero])
    (fun x y => by rw [map_add, mul_add, byteCharacter_add]))

theorem byteCharacterDual_spec (A : BinaryWord 8 ≃+ BinaryWord 8) (v x : BinaryWord 8) :
    byteCharacter (v * A x) = byteCharacter (byteCharacterDual A v * x) :=
  Classical.choose_spec (exists_byte_character_index (fun x => byteCharacter (v * A x))
    (by rw [map_zero, mul_zero, byteCharacter_zero])
    (fun x y => by rw [map_add, mul_add, byteCharacter_add])) x

theorem byteCharacterDual_injective (A : BinaryWord 8 ≃+ BinaryWord 8) :
    Function.Injective (byteCharacterDual A) := by
  intro v w h
  apply byte_character_index_unique
  intro x
  calc
    byteCharacter (v * x) = byteCharacter (v * A (A.symm x)) := by rw [A.apply_symm_apply]
    _ = byteCharacter (byteCharacterDual A v * A.symm x) := byteCharacterDual_spec A v _
    _ = byteCharacter (byteCharacterDual A w * A.symm x) := by rw [h]
    _ = byteCharacter (w * A (A.symm x)) := (byteCharacterDual_spec A w _).symm
    _ = byteCharacter (w * x) := by rw [A.apply_symm_apply]

def byteDualEquiv (A : BinaryWord 8 ≃+ BinaryWord 8) : Equiv.Perm (BinaryWord 8) :=
  Equiv.ofBijective (byteCharacterDual A)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨byteCharacterDual_injective A, rfl⟩)

theorem byteDualEquiv_zero (A : BinaryWord 8 ≃+ BinaryWord 8) : byteDualEquiv A 0 = 0 := by
  apply byte_character_index_unique
  intro x
  change byteCharacter (byteCharacterDual A 0 * x) = _
  rw [← byteCharacterDual_spec, zero_mul, zero_mul]

theorem byteDualEquiv_ne_zero (A : BinaryWord 8 ≃+ BinaryWord 8) (v : BinaryWord 8)
    (hv : v ≠ 0) : byteDualEquiv A v ≠ 0 := by
  intro h
  exact hv ((byteDualEquiv A).injective (h.trans (byteDualEquiv_zero A).symm))

theorem aes_walsh_affine (u v : BinaryWord 8) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm u v =
      byteCharacter (v * (⟨0x63⟩ : BinaryWord 8)) *
        fieldWalsh byteCharacter (fun x => x⁻¹) u (byteDualEquiv AES.affineLinearEquiv v) := by
  unfold fieldWalsh
  have hp (x : BinaryWord 8) :
      byteCharacter (u * x + v * BinaryWord.sboxPerm x) =
        byteCharacter (v * (⟨0x63⟩ : BinaryWord 8)) *
          byteCharacter (u * x + byteDualEquiv AES.affineLinearEquiv v * x⁻¹) := by
    rw [AES.sbox_affine, mul_add, byteCharacter_add, byteCharacter_add,
      byteCharacterDual_spec]
    change byteCharacter (u * x) *
        (byteCharacter (byteDualEquiv AES.affineLinearEquiv v * x⁻¹) *
          byteCharacter (v * (⟨0x63⟩ : BinaryWord 8))) = _
    rw [byteCharacter_add]
    ring
  simp_rw [hp]
  rw [Finset.mul_sum]

end AESMixing
