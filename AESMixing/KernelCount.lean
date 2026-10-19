import AESMixing.ShortenedMDS
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Exact solution counts from checked factorization and section certificates.
No numerical rank oracle is assumed. The application supplies explicit additive
maps, an injective first factor, and a right inverse of the second factor. -/
noncomputable section
namespace AESMixing
attribute [local instance] Classical.propDecidable

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

def splitKernelEquiv (C : X →+ Y) (R : Y →+ X) (hR : ∀ y, C (R y) = y) :
    X ≃ (C.ker × Y) where
  toFun x := (⟨x - R (C x), by simp [map_sub, hR]⟩, C x)
  invFun p := p.1.val + R p.2
  left_inv x := sub_add_cancel _ _
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      have hk : C p.1.val = 0 := p.1.property
      simp [map_add, hR, hk]
    · have hk : C p.1.val = 0 := p.1.property
      simp [map_add, hR, hk]

def factorKernelEquiv (A : X →+ Z) (B : Y →+ Z) (C : X →+ Y)
    (hA : A = B.comp C) (hB : Function.Injective B) : A.ker ≃ C.ker where
  toFun x := ⟨x.val, by
    apply hB
    have hx : A x.val = 0 := x.property
    have he := DFunLike.congr_fun hA x.val
    change A x.val = B (C x.val) at he
    exact he.symm.trans (hx.trans (map_zero B).symm)⟩
  invFun x := ⟨x.val, by
    have hx : C x.val = 0 := x.property
    change A x.val = 0
    rw [hA]
    simp [hx]⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem split_kernel_card [Fintype X] [Fintype Y]
    (C : X →+ Y) (R : Y →+ X) (hR : ∀ y, C (R y) = y) :
    Fintype.card C.ker * Fintype.card Y = Fintype.card X := by
  have h := Fintype.card_congr (splitKernelEquiv C R hR)
  simpa only [Fintype.card_prod] using h.symm

theorem factor_kernel_card [Fintype X] [Fintype Y]
    (A : X →+ Z) (B : Y →+ Z) (C : X →+ Y) (R : Y →+ X)
    (hA : A = B.comp C) (hB : Function.Injective B) (hR : ∀ y, C (R y) = y) :
    Fintype.card A.ker * Fintype.card Y = Fintype.card X := by
  rw [Fintype.card_congr (factorKernelEquiv A B C hA hB)]
  exact split_kernel_card C R hR

theorem coordinate_factor_kernel_card {V : Type*} [AddCommGroup V] [Fintype V]
    {n r : ℕ} (hr : r ≤ n) (A : (Fin n → V) →+ Z)
    (B : (Fin r → V) →+ Z) (C : (Fin n → V) →+ (Fin r → V))
    (R : (Fin r → V) →+ (Fin n → V))
    (hA : A = B.comp C) (hB : Function.Injective B) (hR : ∀ y, C (R y) = y) :
    Fintype.card A.ker = Fintype.card V ^ (n-r) := by
  have h := factor_kernel_card A B C R hA hB hR
  simp only [Fintype.card_fun, Fintype.card_fin] at h
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fintype.card_pos (α := V)) r)
  rw [h, ← pow_add, Nat.sub_add_cancel hr]

end AESMixing
