import AESMixing.Difference

/-! Affine output maps only relabel output differences. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

def affineOutput (s : Equiv.Perm V) (A : V ≃+ V) (c : V) : Equiv.Perm V :=
  (s.trans A.toEquiv).trans (Equiv.addRight c)

omit [Fintype V] [DecidableEq V] in
theorem affineOutput_difference (s : Equiv.Perm V) (A : V ≃+ V) (c a x : V) :
    difference (affineOutput s A c) a x = A (difference s a x) := by
  simp [difference, affineOutput, map_sub]

theorem affineOutput_channel (s : Equiv.Perm V) (A : V ≃+ V) (c a b : V) :
    differenceChannel (affineOutput s A c) b a =
      differenceChannel s (A.symm b) a := by
  have he (z : V) : A z = b ↔ z = A.symm b := by
    constructor
    · intro h
      have hh := congrArg A.symm h
      simpa only [A.symm_apply_apply] using hh
    · rintro rfl; exact A.apply_symm_apply b
  unfold differenceChannel
  simp only [affineOutput_difference, he]

def nonzeroAddEquiv (A : V ≃+ V) : Equiv.Perm {x : V // x ≠ 0} where
  toFun x := ⟨A x.val, fun h => x.property (A.injective (h.trans (map_zero A).symm))⟩
  invFun x := ⟨A.symm x.val, fun h => x.property (A.symm.injective (h.trans (map_zero A.symm).symm))⟩
  left_inv x := Subtype.ext (A.symm_apply_apply x.val)
  right_inv x := Subtype.ext (A.apply_symm_apply x.val)

end AESMixing
