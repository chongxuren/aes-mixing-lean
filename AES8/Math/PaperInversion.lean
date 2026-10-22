import AES8.Math.PaperInversionResidual
import AES8.Math.PaperInversionHistogram
import AES8.Math.PaperInversionCharacterNorm

/-! Public arbitrary-field endpoint for the frozen inversion lemma.
The norm endpoint follows the paper's character/Gauss-sum argument. The older
residual module is used only for its affine-output reindexing identity.
The prime-field algebra is constructed canonically from characteristic two,
so the caller supplies only a finite field of characteristic two. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperInversion
open AESMixing
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

def degree (F : Type*) [Field F] [CharP F 2] : ℕ :=
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  Module.finrank (ZMod 2) F

theorem degree_positive : 1 ≤ degree F := Module.finrank_pos

theorem field_card : Fintype.card F=2^degree F := PaperInversionHistogram.field_card

theorem residual_contraction (f : F → ℝ) :
    l2 (action (residualMatrix (differenceChannel invPermutation) 0) f) ≤
      ((Real.sqrt (Fintype.card F)+2)/(Fintype.card F : ℝ))*l2 f :=
  PaperInversionCharacterNorm.residual_l2 f

theorem affine_residual_contraction (A : F ≃+ F) (c : F) (f : F → ℝ) :
    l2 (action (residualMatrix (differenceChannel (affineOutput invPermutation A c)) 0) f) ≤
      ((Real.sqrt (Fintype.card F)+2)/(Fintype.card F : ℝ))*l2 f := by
  have he : l2 (action (residualMatrix
      (differenceChannel (affineOutput invPermutation A c)) 0) f) =
      l2 (action (residualMatrix (differenceChannel invPermutation) 0) f) := by
    unfold l2 action
    simp_rw [PaperInversionResidual.affine_residual]
    congr 1
    exact Equiv.sum_comp A.symm.toEquiv (fun y : F =>
      (∑ x, residualMatrix (differenceChannel invPermutation) 0 y x*f x)^2)
  rw [he]
  exact residual_contraction f

theorem column_histogram (he : Even (degree F)) (a : F) (ha : a ≠ 0) :
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel invPermutation b a=4/(Fintype.card F : ℝ))).card=1 ∧
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel invPermutation b a=2/(Fintype.card F : ℝ))).card=Fintype.card F/2-2 ∧
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel invPermutation b a=0)).card=Fintype.card F/2 :=
  PaperInversionHistogram.column he a ha

theorem row_histogram (he : Even (degree F)) (b : F) (hb : b ≠ 0) :
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel invPermutation b a=4/(Fintype.card F : ℝ))).card=1 ∧
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel invPermutation b a=2/(Fintype.card F : ℝ))).card=Fintype.card F/2-2 ∧
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel invPermutation b a=0)).card=Fintype.card F/2 :=
  PaperInversionHistogram.row he b hb

theorem affine_column_histogram (he : Even (degree F))
    (A : F ≃+ F) (c a : F) (ha : a ≠ 0) :
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=4/(Fintype.card F : ℝ))).card=1 ∧
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=2/(Fintype.card F : ℝ))).card=Fintype.card F/2-2 ∧
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=0)).card=Fintype.card F/2 :=
  PaperInversionHistogram.affine_column he A c a ha

theorem affine_row_histogram (he : Even (degree F))
    (A : F ≃+ F) (c b : F) (hb : b ≠ 0) :
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=4/(Fintype.card F : ℝ))).card=1 ∧
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=2/(Fintype.card F : ℝ))).card=Fintype.card F/2-2 ∧
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=0)).card=Fintype.card F/2 :=
  PaperInversionHistogram.affine_row he A c b hb

end AES8.PaperInversion
