import AESMixing.ConstraintMatrix
import AESMixing.RankCertificate

/-! The matrix kernel and the Gram-entry constraint set are in explicit
bijection. This closes the semantic gap between a rank certificate and a
single term of the activity Gram expansion. -/
namespace AESMixing
open scoped BigOperators

variable {F : Type*} [Ring F]

def firstWord (z : Fin 8 → F) : Fin 4 → F := fun i => z (Fin.castAdd 4 i)
def secondWord (z : Fin 8 → F) : Fin 4 → F := fun i => z (Fin.natAdd 4 i)

omit [Ring F] in
theorem append_words (z : Fin 8 → F) : Fin.append (firstWord z) (secondWord z) = z :=
  Fin.append_castAdd_natAdd

theorem constraint_kernel_properties (A : Fin 4 → Fin 4 → F)
    (a b : Fin 16) (m : Fin 4 → Fin 5)
    (z : (fieldMatrix (constraintMatrix A a b m)).ker) :
    maskProjection a (firstWord z.val) = firstWord z.val ∧
    maskProjection b (secondWord z.val) = secondWord z.val ∧
      ∀ i, atomCondition (m i) (fieldMatrix A (firstWord z.val) i)
        (fieldMatrix A (secondWord z.val) i) := by
  apply (constraintMatrix_zero_iff A a b m _ _).mp
  rw [append_words]
  exact z.property

def constraintSolutionsEquiv (A : Fin 4 → Fin 4 → F)
    (a b : Fin 16) (m : Fin 4 → Fin 5) :
    {x : (MaskCoordinates a → F) × (MaskCoordinates b → F) // ∀ i,
      atomCondition (m i) (fieldMatrix A (extendCoordinates a x.1) i)
        (fieldMatrix A (extendCoordinates b x.2) i)} ≃
    (fieldMatrix (constraintMatrix A a b m)).ker where
  toFun x := ⟨Fin.append (extendCoordinates a x.val.1) (extendCoordinates b x.val.2),
    (constraintMatrix_zero_iff A a b m _ _).mpr
      ⟨extend_supported a x.val.1, extend_supported b x.val.2, x.property⟩⟩
  invFun z := ⟨(restrictCoordinates a (firstWord z.val), restrictCoordinates b (secondWord z.val)), by
    have hz := constraint_kernel_properties A a b m z
    simpa only [extend_restrict, hz.1, hz.2.1] using hz.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change Fin.append (extendCoordinates a x.val.1) (extendCoordinates b x.val.2)
        (Fin.castAdd 4 i.val) = x.val.1 i
      rw [Fin.append_left]
      simp [extendCoordinates, i.property]
    · funext i
      change Fin.append (extendCoordinates a x.val.1) (extendCoordinates b x.val.2)
        (Fin.natAdd 4 i.val) = x.val.2 i
      rw [Fin.append_right]
      simp [extendCoordinates, i.property]
  right_inv z := by
    apply Subtype.ext
    have hz := constraint_kernel_properties A a b m z
    change Fin.append (extendCoordinates a (restrictCoordinates a (firstWord z.val)))
      (extendCoordinates b (restrictCoordinates b (secondWord z.val))) = z.val
    rw [extend_restrict, extend_restrict, hz.1, hz.2.1, append_words]

theorem constraint_count_from_certificate
    (A : Fin 4 → Fin 4 → BinaryWord 8) (a b : Fin 16) (m : Fin 4 → Fin 5)
    (c : RankCertificate (BinaryWord 8) 16 8)
    (h : c.Valid (constraintMatrix A a b m)) :
    Nat.card {x : (MaskCoordinates a → BinaryWord 8) ×
        (MaskCoordinates b → BinaryWord 8) // ∀ i,
      atomCondition (m i) (fieldMatrix A (extendCoordinates a x.1) i)
        (fieldMatrix A (extendCoordinates b x.2) i)} = 256^(8-c.rank.val) := by
  rw [Nat.card_congr (constraintSolutionsEquiv A a b m)]
  exact byte_rank_certificate_card c _ h

end AESMixing
