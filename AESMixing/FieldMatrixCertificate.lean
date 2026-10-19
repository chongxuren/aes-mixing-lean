import AESMixing.KernelCount
import AESMixing.ByteField
import Mathlib.SetTheory.Cardinal.Finite

/-! Entrywise field-matrix certificates avoid enumerating binary basis vectors.
The AES field laws have already been proved for the actual polynomial bytes. -/
noncomputable section
namespace AESMixing
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Ring F]

def fieldMatrix {m n : ℕ} (A : Fin m → Fin n → F) : (Fin n → F) →+ (Fin m → F) where
  toFun x i := ∑ j, A i j * x j
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [mul_add, Finset.sum_add_distrib]

theorem fieldMatrix_comp {m n r : ℕ}
    (A : Fin m → Fin r → F) (B : Fin r → Fin n → F) :
    (fieldMatrix A).comp (fieldMatrix B) = fieldMatrix (fun i j => ∑ k, A i k * B k j) := by
  apply DFunLike.ext
  intro x
  funext i
  simp only [fieldMatrix, AddMonoidHom.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem fieldMatrix_identity (n : ℕ) :
    fieldMatrix (fun i j : Fin n => if i = j then (1 : F) else 0) = AddMonoidHom.id (Fin n → F) := by
  apply DFunLike.ext
  intro x
  funext i
  simp [fieldMatrix]

theorem fieldMatrix_factor {m n r : ℕ}
    (A : Fin m → Fin n → F) (B : Fin m → Fin r → F) (C : Fin r → Fin n → F)
    (h : ∀ i j, A i j = ∑ k, B i k * C k j) :
    fieldMatrix A = (fieldMatrix B).comp (fieldMatrix C) := by
  rw [fieldMatrix_comp]
  congr 1
  funext i j
  exact h i j

theorem fieldMatrix_section {n r : ℕ}
    (A : Fin r → Fin n → F) (B : Fin n → Fin r → F)
    (h : ∀ i j, (∑ k, A i k * B k j) = if i = j then 1 else 0) :
    ∀ x, fieldMatrix A (fieldMatrix B x) = x := by
  have he : (fieldMatrix A).comp (fieldMatrix B) = AddMonoidHom.id (Fin r → F) := by
    rw [fieldMatrix_comp, ← fieldMatrix_identity]
    congr 1
    funext i j
    exact h i j
  exact DFunLike.congr_fun he

theorem fieldMatrix_kernel_card [Fintype F] {m n r : ℕ} (hr : r ≤ n)
    (A : Fin m → Fin n → F) (B : Fin m → Fin r → F) (C : Fin r → Fin n → F)
    (L : Fin r → Fin m → F) (R : Fin n → Fin r → F)
    (hA : ∀ i j, A i j = ∑ k, B i k * C k j)
    (hB : ∀ i j, (∑ k, L i k * B k j) = if i = j then 1 else 0)
    (hC : ∀ i j, (∑ k, C i k * R k j) = if i = j then 1 else 0) :
    Fintype.card (fieldMatrix A).ker = Fintype.card F ^ (n-r) := by
  classical
  have hleft : Function.LeftInverse (fieldMatrix L) (fieldMatrix B) := fieldMatrix_section L B hB
  have he := coordinate_factor_kernel_card hr (fieldMatrix A) (fieldMatrix B) (fieldMatrix C)
    (fieldMatrix R) (fieldMatrix_factor A B C hA) hleft.injective (fieldMatrix_section C R hC)
  simpa only [← Nat.card_eq_fintype_card] using he

theorem columnMatrix_eq_fieldMatrix {m n : ℕ} (A : Fin m → Fin n → AES.Byte) :
    AES.columnMatrix A = fieldMatrix (fun i j => (⟨A i j⟩ : BinaryWord 8)) := by
  apply DFunLike.ext
  intro x
  funext i
  change (∑ j, AES.scale (A i j) (x j)) = ∑ j, (⟨A i j⟩ : BinaryWord 8) * x j
  apply Finset.sum_congr rfl
  intro j _
  change x j * (⟨A i j⟩ : BinaryWord 8) = (⟨A i j⟩ : BinaryWord 8) * x j
  exact mul_comm _ _

end AESMixing
