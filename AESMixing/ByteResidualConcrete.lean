import AESMixing.ByteResidualBounds
import AESMixing.MDSInverse
import AESMixing.AESGramOrientation
import AESMixing.DegreeComposition

/-! Specialize the residual block bounds to both actual AES MixColumns
orientations. Adjoint transfer also gives the transposed (2,1) block. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem degreeTransfer_input_projection {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (i j : Fin 5)
    (e : Equiv.Perm (Fin 4 → V)) (f : (Fin 4 → V) → ℝ) :
    degreeTransfer z i j e (degreeComponent z j f) = degreeTransfer z i j e f := by
  unfold degreeTransfer
  rw [degreeComponent_compose z hn,if_pos rfl]

theorem degreeTransfer_reverse_projected_bound {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (i j : Fin 5)
    (e : Equiv.Perm (Fin 4 → V)) (c : ℝ)
    (hbound : ∀ f, (∑ y, degreeTransfer z i j e f y^2) ≤
      c^2*∑ x, degreeComponent z j f x^2) (g : (Fin 4 → V) → ℝ) :
    (∑ x, degreeTransfer z j i e.symm g x^2) ≤ c^2*∑ y, degreeComponent z i g y^2 := by
  have h := degreeTransfer_reverse_bound z i j e c
    (fun f => (hbound f).trans (mul_le_mul_of_nonneg_left
      (degreeComponent_energy_le z hn j f) (sq_nonneg c))) (degreeComponent z i g)
  rw [degreeTransfer_input_projection z hn] at h
  exact h

def byteDiffusionOrientedAddEquiv (inverse : Bool) :
    (Fin 4 → BinaryWord 8) ≃+ (Fin 4 → BinaryWord 8) :=
  if inverse then byteDiffusionAddEquiv.symm else byteDiffusionAddEquiv

theorem byteDiffusionOrientedAddEquiv_toEquiv (inverse : Bool) :
    (byteDiffusionOrientedAddEquiv inverse).toEquiv = byteDiffusionOrientation inverse := by
  cases inverse <;> rfl

theorem byteDiffusionOrientedAddEquiv_zeroMDS (inverse : Bool) :
    ZeroMDS (byteDiffusionOrientedAddEquiv inverse) := by
  cases inverse
  · exact byteDiffusionAddEquiv_zeroMDS
  · exact byteDiffusionAddEquiv_inverse_zeroMDS

theorem byteDiffusionOrientation_symm (inverse : Bool) :
    (byteDiffusionOrientation (!inverse)).symm = byteDiffusionOrientation inverse := by
  cases inverse <;> rfl

theorem aes_residual_11_energy (inverse : Bool) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 1 1 (byteDiffusionOrientation inverse) f x^2) ≤
      (27/8000 : ℝ)^2*∑ x, degreeComponent 0 1 f x^2 := by
  have h := byte_residual_11_energy (byteDiffusionOrientedAddEquiv inverse)
    (byteDiffusionOrientedAddEquiv_zeroMDS inverse) f
  simpa only [byteDiffusionOrientedAddEquiv_toEquiv] using h

theorem aes_residual_12_energy (inverse : Bool) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 1 2 (byteDiffusionOrientation inverse) f x^2) ≤
      (43/500 : ℝ)^2*∑ x, degreeComponent 0 2 f x^2 := by
  have h := byte_residual_12_energy (byteDiffusionOrientedAddEquiv inverse)
    (byteDiffusionOrientedAddEquiv_zeroMDS inverse) f
  simpa only [byteDiffusionOrientedAddEquiv_toEquiv] using h

theorem aes_residual_21_energy (inverse : Bool) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 2 1 (byteDiffusionOrientation inverse) f x^2) ≤
      (43/500 : ℝ)^2*∑ x, degreeComponent 0 1 f x^2 := by
  have h := degreeTransfer_reverse_projected_bound 0 (by norm_num [BinaryWord.card])
    1 2 (byteDiffusionOrientation (!inverse)) (43/500) (aes_residual_12_energy (!inverse)) f
  simpa only [byteDiffusionOrientation_symm] using h

theorem aes_residual_22_energy (inverse : Bool) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ x, degreeTransfer 0 2 2 (byteDiffusionOrientation inverse) f x^2) ≤
      (9/10 : ℝ)^2*∑ x, degreeComponent 0 2 f x^2 := by
  have h := byte_residual_22_energy (byteDiffusionOrientedAddEquiv inverse)
    (byteDiffusionOrientedAddEquiv_zeroMDS inverse) f
  simpa only [byteDiffusionOrientedAddEquiv_toEquiv] using h

end AESMixing
