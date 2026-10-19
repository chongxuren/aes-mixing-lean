import AESMixing.IntegerGram
import AESMixing.GramCases

/-! Both numerical certificate orientations refer to the actual AES
MixColumns permutation and its inverse. The exact counts give their actual
degree-response Gram entries; no operator estimate is assumed here. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def byteDiffusionOrientation (inverse : Bool) :
    (Fin 4 → BinaryWord 8) ≃ (Fin 4 → BinaryWord 8) :=
  if inverse then byteDiffusionEquiv.symm else byteDiffusionEquiv

theorem byteDiffusionEquiv_inverse (x : Fin 4 → BinaryWord 8) :
    byteDiffusionEquiv.symm x = AES.columnMatrix (AES.minorInverse 15 15) x := by
  have h := AES.mixColumn_left_inverse (byteDiffusionEquiv.symm x)
  change AES.columnMatrix (AES.minorInverse 15 15)
    (byteDiffusionEquiv (byteDiffusionEquiv.symm x)) = byteDiffusionEquiv.symm x at h
  rw [byteDiffusionEquiv.apply_symm_apply] at h
  exact h.symm

theorem byteDiffusionOrientation_apply (inverse : Bool) (x : Fin 4 → BinaryWord 8) :
    byteDiffusionOrientation inverse x = fieldMatrix (gramMixing inverse) x := by
  cases inverse
  · change AES.columnMatrix AES.mixEntry x = _
    rw [columnMatrix_eq_fieldMatrix]
    rfl
  · change byteDiffusionEquiv.symm x = _
    rw [byteDiffusionEquiv_inverse, columnMatrix_eq_fieldMatrix]
    rfl

theorem gram_case_constraint_card (inverse : Bool) (a b : Fin 16) (m : Fin 4 → Fin 5) :
    Nat.card {x : (MaskCoordinates a → BinaryWord 8) ×
        (MaskCoordinates b → BinaryWord 8) // ∀ i,
      atomCondition (m i) (fieldMatrix (gramMixing inverse) (extendCoordinates a x.1) i)
        (fieldMatrix (gramMixing inverse) (extendCoordinates b x.2) i)} =
      gramCaseCount inverse a b (finFunctionFinEquiv m) := by
  have h := Nat.card_congr (constraintSolutionsEquiv (gramMixing inverse) a b m)
  simpa only [gramCaseCount, gramCaseMatrix, gramModes,
    finFunctionFinEquiv.symm_apply_apply] using h

theorem oriented_activity_gram_from_ranks (inverse : Bool) (j : Fin 5) (a b : Fin 16)
    (rank : Fin 625 → ℕ)
    (hcount : ∀ i, gramCaseCount inverse a b i = 256^(8-rank i)) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation inverse) a) y *
      degreeComponent 0 j (diffusedActivityColumn (byteDiffusionOrientation inverse) b) y) =
      (rankGramNumerator (fun m => rank (finFunctionFinEquiv m)) j : ℝ)/255^4 := by
  have hn : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have h := activity_degree_gram hn (byteDiffusionOrientation inverse) j a b
  norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] at h
  simp only [byteDiffusionOrientation_apply, ← Nat.card_eq_fintype_card] at h
  simp_rw [gram_case_constraint_card, hcount, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h.trans (rankGramNumerator_formula (fun m => rank (finFunctionFinEquiv m)) j)

end AESMixing
