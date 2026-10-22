import AES8.Reductions.Support.PaperDegreeFourier
import AESConcrete.WordFourierDiffusion

/-! Fourier, coordinate reversal and adjoints identify opposite boundary norms
for every represented four-byte circulant linear permutation. No norm bound or
slope-class statement is assumed by the transport. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperCirculantReverse
open AESMixing AESConcrete.WordFourierCore AESConcrete.WordFourierDiffusion
open AESConcrete.DegreeHilbertSchmidt PaperKernelBounds PaperFiberKernel
set_option autoImplicit false
set_option maxRecDepth 100000

def reverseInverse (e : Equiv.Perm Word) : Equiv.Perm Word :=
  wordReverse.trans (e.symm.trans wordReverse)

theorem conjugate_permutation (e d : Equiv.Perm Word)
    (hpair : ∀ y x, AESConcrete.WordFourierCore.wordPairing.value y (e x) = AESConcrete.WordFourierCore.wordPairing.value (d.symm y) x) :
    wordConjugate (permutationKernel e) = permutationKernel d := by
  have hp (y x : Word) : wordFourier y (e x) = wordFourier (d.symm y) x := by
    simp only [wordFourier_coefficient, hpair]
  funext y x
  change (∑ z, wordFourier y z * kernelCompose (permutationKernel e) wordFourier z x) = _
  simp_rw [kernelCompose_permutation_left]
  rw [← Equiv.sum_comp e (fun z => wordFourier y z * wordFourier (e.symm z) x)]
  simp only [Equiv.symm_apply_apply, hp]
  change kernelCompose wordFourier wordFourier (d.symm y) x = _
  rw [wordFourier_comp_self]
  have he : d.symm y = x ↔ y = d x := by
    constructor
    · intro h; rw [← h, d.apply_symm_apply]
    · intro h; rw [h, d.symm_apply_apply]
  simp only [identityKernel, permutationKernel, he]

theorem reverseInverse_kernel (e : Equiv.Perm Word) :
    permutationKernel (reverseInverse e) = reindexKernel wordReverse (permutationKernel e.symm) := by
  funext y x
  have he : y = wordReverse (e.symm (wordReverse x)) ↔ wordReverse y = e.symm (wordReverse x) := by
    constructor
    · intro h; rw [h, wordReverse_self]
    · intro h; rw [← h, wordReverse_self]
  change (if y = wordReverse (e.symm (wordReverse x)) then (1:ℝ) else 0) =
    if wordReverse y = e.symm (wordReverse x) then 1 else 0
  simp only [he]

theorem reverse_pairing (M : Fin 4 → Fin 4 → Byte) (e : Equiv.Perm Word)
    (he : ∀ x, e x = fieldMatrix M x)
    (hrev : ∀ i j, M (byteReverse i) (byteReverse j) = M j i) (y x : Word) :
    AESConcrete.WordFourierCore.wordPairing.value y (e x) = AESConcrete.WordFourierCore.wordPairing.value ((reverseInverse e).symm y) x := by
  rw [he, wordPairing_fieldMatrix_dual]
  congr 1
  change fieldMatrix (fun i j => M j i) y = wordReverse (e (wordReverse y))
  rw [he]
  funext i
  have hs := Equiv.sum_comp byteReverse (fun j => M (byteReverse i) j * y (byteReverse j))
  simpa only [fieldMatrix, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    hrev, byteReverse_self, wordReverse_apply] using hs

theorem inverse_block_norm (M : Fin 4 → Fin 4 → Byte) (e : Equiv.Perm Word)
    (he : ∀ x, e x = fieldMatrix M x)
    (hrev : ∀ i j, M (byteReverse i) (byteReverse j) = M j i) (i j : Fin 5) :
    ‖kernelOperator (block 0 (permutationKernel e.symm) i j)‖ =
      ‖kernelOperator (block 0 (permutationKernel e) i j)‖ := by
  have hf := PaperDegreeFourier.block_conjugate_norm (permutationKernel e) i j
  rw [conjugate_permutation e (reverseInverse e) (reverse_pairing M e he hrev),
    reverseInverse_kernel, PaperDegreeReverse.block_reverse] at hf
  change ‖kernelOperator (fun y x => block 0 (permutationKernel e.symm) i j (wordReverse y) (wordReverse x))‖ = _ at hf
  rw [PaperKernelReindex.kernelOperator_reindex wordReverse wordReverse] at hf
  exact hf

theorem block_transpose (e : Equiv.Perm Word) (i j : Fin 5) :
    Matrix.conjTranspose (block 0 (permutationKernel e) i j) =
      block 0 (permutationKernel e.symm) j i := by
  funext y x
  have he (a b : Word) : permutationKernel e b a = permutationKernel e.symm a b := by
    have hh : b = e a ↔ a = e.symm b := by
      constructor
      · intro h; rw [h, e.symm_apply_apply]
      · intro h; rw [h, e.apply_symm_apply]
    simp only [permutationKernel, hh ]
  change block 0 (permutationKernel e) i j x y = _
  unfold block kernelCompose
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [degreeKernel_symmetric 0 i x b, degreeKernel_symmetric 0 j a y, he]
  ring

theorem swapped_inverse_block_norm (e : Equiv.Perm Word) (i j : Fin 5) :
    ‖kernelOperator (block 0 (permutationKernel e.symm) j i)‖ =
      ‖kernelOperator (block 0 (permutationKernel e) i j)‖ := by
  rw [← block_transpose, ← kernelOperator_adjoint]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem boundary_norm_eq (M : Fin 4 → Fin 4 → Byte) (e : Equiv.Perm Word)
    (he : ∀ x, e x = fieldMatrix M x)
    (hrev : ∀ i j, M (byteReverse i) (byteReverse j) = M j i) (i j : Fin 5) :
    ‖kernelOperator (block 0 (permutationKernel e) j i)‖ =
      ‖kernelOperator (block 0 (permutationKernel e) i j)‖ := by
  rw [← inverse_block_norm M e he hrev j i, swapped_inverse_block_norm]

/-- Circulants are indexed by cyclic column minus row. -/
def circulant (c : Fin 4 → Byte) (i j : Fin 4) : Byte := c (j-i)

theorem circulant_reverse (c : Fin 4 → Byte) (i j : Fin 4) :
    circulant c (byteReverse i) (byteReverse j) = circulant c j i := by
  unfold circulant
  congr 1
  exact (by decide : ∀ i j : Fin 4, byteReverse j-byteReverse i=i-j) i j

theorem circulant_boundary_norm_eq (c : Fin 4 → Byte) (e : Equiv.Perm Word)
    (he : ∀ x, e x = fieldMatrix (circulant c) x) (i j : Fin 5) :
    ‖kernelOperator (block 0 (permutationKernel e) j i)‖ =
      ‖kernelOperator (block 0 (permutationKernel e) i j)‖ :=
  boundary_norm_eq (circulant c) e he (circulant_reverse c) i j

end AES8.PaperCirculantReverse
