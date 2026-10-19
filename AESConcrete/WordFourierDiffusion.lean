import AESConcrete.WordFourierCore
import AESMixing.MixColumnsTranspose
import AESMixing.ByteResidualConcrete

/-!
# Exact Fourier transport of actual AES word diffusion

The product trace pairing sends a field matrix to its actual transpose.
The historical MixColumns transpose identity identifies that transpose
with simultaneous coordinate reversal. The normalized Fourier conjugate
of the permutation kernel is therefore the inverse-transpose permutation,
with no norm or abstract dual-map resource assumed.

Constructive mathematics only; no attacks, manuscript changes, numerical
workloads or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WordFourierDiffusion
open AESMixing
open AESConcrete.WordFourierCore (wordFourier wordConjugate)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

section PermutationKernel
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Rows are outputs, so this kernel acts by pullback along the inverse. -/
def permutationKernel (e : Equiv.Perm X) (y x : X) : ℝ := if y = e x then 1 else 0

theorem permutationKernel_action (e : Equiv.Perm X) (f : X → ℝ) :
    action (permutationKernel e) f = fun y => f (e.symm y) := by
  funext y
  have hcond (x : X) : y = e x ↔ x = e.symm y := by
    constructor
    · intro h
      calc
        x = e.symm (e x) := (e.symm_apply_apply x).symm
        _ = e.symm y := congrArg e.symm h.symm
    · intro h
      rw [h, e.apply_symm_apply]
  simp [action, permutationKernel, hcond]

theorem kernelCompose_permutation_left (e : Equiv.Perm X) (K : X → X → ℝ) (y x : X) :
    kernelCompose (permutationKernel e) K y x = K (e.symm y) x :=
  congrFun (permutationKernel_action e (fun z => K z x)) y

theorem kernelCompose_permutation_right (K : X → X → ℝ) (e : Equiv.Perm X) (y x : X) :
    kernelCompose K (permutationKernel e) y x = K y (e x) := by
  simp [kernelCompose, permutationKernel]

end PermutationKernel

def wordReverse : Equiv.Perm AES.Word where
  toFun x i := x (byteReverse i)
  invFun x i := x (byteReverse i)
  left_inv x := by funext i; exact congrArg x (byteReverse_self i)
  right_inv x := by funext i; exact congrArg x (byteReverse_self i)

theorem wordReverse_apply (x : AES.Word) (i : Fin 4) :
    wordReverse x i = x (byteReverse i) := rfl

theorem wordReverse_self (x : AES.Word) : wordReverse (wordReverse x) = x :=
  wordReverse.left_inv x

theorem wordReverse_symm : wordReverse.symm = wordReverse := by
  apply Equiv.ext
  intro x
  rfl

theorem wordReverse_zero : wordReverse (0 : AES.Word) = 0 := rfl

/-- The actual inverse transpose, written with the actual opposite diffusion. -/
def dualDiffusion (inverse : Bool) : Equiv.Perm AES.Word :=
  wordReverse.trans ((byteDiffusionOrientation inverse).symm.trans wordReverse)

theorem dualDiffusion_apply (inverse : Bool) (x : AES.Word) :
    dualDiffusion inverse x =
      wordReverse ((byteDiffusionOrientation inverse).symm (wordReverse x)) := rfl

theorem dualDiffusion_symm_apply (inverse : Bool) (x : AES.Word) :
    (dualDiffusion inverse).symm x =
      wordReverse (byteDiffusionOrientation inverse (wordReverse x)) := rfl

theorem dualDiffusion_opposite_apply (inverse : Bool) (x : AES.Word) :
    dualDiffusion inverse x =
      wordReverse (byteDiffusionOrientation (!inverse) (wordReverse x)) := by
  cases inverse <;> rfl

theorem byteCharacter_finset_sum {I : Type*} (s : Finset I) (f : I → BinaryWord 8) :
    byteCharacter (∑ i ∈ s, f i) = ∏ i ∈ s, byteCharacter (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [byteCharacter_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, byteCharacter_add, ih]

/-- This is an exact trace-pairing transpose identity for field matrices,
not a hypothesized dual action. -/
theorem wordPairing_fieldMatrix_dual (M : Fin 4 → Fin 4 → BinaryWord 8) (y x : AES.Word) :
    WordFourierCore.wordPairing.value y (fieldMatrix M x) =
      WordFourierCore.wordPairing.value (fieldMatrix (fun i j => M j i) y) x := by
  change (∏ i : Fin 4, byteCharacter (y i * ∑ j : Fin 4, M i j * x j)) =
    ∏ j : Fin 4, byteCharacter ((∑ i : Fin 4, M i j * y i) * x j)
  simp_rw [Finset.mul_sum, Finset.sum_mul, byteCharacter_finset_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ac_rfl

theorem diffusion_transpose_action (inverse : Bool) (y : AES.Word) :
    fieldMatrix (fun i j => gramMixing inverse j i) y = (dualDiffusion inverse).symm y := by
  rw [gramMixing_transpose_action, dualDiffusion_symm_apply, byteDiffusionOrientation_apply]
  rfl

/-- Both actual diffusion directions have this concrete product-pairing dual. -/
theorem actual_diffusion_pairing (inverse : Bool) (y x : AES.Word) :
    WordFourierCore.wordPairing.value y (byteDiffusionOrientation inverse x) =
      WordFourierCore.wordPairing.value ((dualDiffusion inverse).symm y) x := by
  rw [byteDiffusionOrientation_apply]
  rw [wordPairing_fieldMatrix_dual, diffusion_transpose_action]

theorem wordFourier_diffusion_pairing (inverse : Bool) (y x : AES.Word) :
    wordFourier y (byteDiffusionOrientation inverse x) =
      wordFourier ((dualDiffusion inverse).symm y) x := by
  change WordFourierCore.wordPairing.value y (byteDiffusionOrientation inverse x) /
      Real.sqrt (Fintype.card AES.Word) =
    WordFourierCore.wordPairing.value ((dualDiffusion inverse).symm y) x /
      Real.sqrt (Fintype.card AES.Word)
  rw [actual_diffusion_pairing]

/-- Normalized Fourier conjugation transports the actual permutation into
its inverse transpose. All pairing and diffusion identifications are proved above. -/
theorem wordConjugate_diffusion (inverse : Bool) :
    wordConjugate (permutationKernel (byteDiffusionOrientation inverse)) =
      permutationKernel (dualDiffusion inverse) := by
  funext y x
  change (∑ z : AES.Word, wordFourier y z *
    kernelCompose (permutationKernel (byteDiffusionOrientation inverse)) wordFourier z x) = _
  simp_rw [kernelCompose_permutation_left]
  have hreindex := (byteDiffusionOrientation inverse).sum_comp
    (fun z : AES.Word => wordFourier y z *
      wordFourier ((byteDiffusionOrientation inverse).symm z) x)
  calc
    _ = ∑ w : AES.Word, wordFourier y (byteDiffusionOrientation inverse w) * wordFourier w x := by
      simpa only [Equiv.symm_apply_apply] using hreindex.symm
    _ = kernelCompose wordFourier wordFourier ((dualDiffusion inverse).symm y) x := by
      simp only [kernelCompose, wordFourier_diffusion_pairing]
    _ = identityKernel ((dualDiffusion inverse).symm y) x :=
      congrFun (congrFun WordFourierCore.wordFourier_comp_self ((dualDiffusion inverse).symm y)) x
    _ = permutationKernel (dualDiffusion inverse) y x := by
      have hcond : (dualDiffusion inverse).symm y = x ↔ y = dualDiffusion inverse x := by
        constructor
        · intro h
          calc
            y = dualDiffusion inverse ((dualDiffusion inverse).symm y) :=
              ((dualDiffusion inverse).apply_symm_apply y).symm
            _ = dualDiffusion inverse x := congrArg (dualDiffusion inverse) h
        · intro h
          rw [h, (dualDiffusion inverse).symm_apply_apply]
      simp only [identityKernel, permutationKernel, hcond]

theorem wordConjugate_diffusion_reversal (inverse : Bool) (y x : AES.Word) :
    wordConjugate (permutationKernel (byteDiffusionOrientation inverse)) y x =
      permutationKernel (byteDiffusionOrientation (!inverse)) (wordReverse y) (wordReverse x) := by
  rw [wordConjugate_diffusion]
  have hcond : y = dualDiffusion inverse x ↔
      wordReverse y = byteDiffusionOrientation (!inverse) (wordReverse x) := by
    rw [dualDiffusion_opposite_apply]
    constructor
    · intro h
      rw [h, wordReverse_self]
    · intro h
      calc
        y = wordReverse (wordReverse y) := (wordReverse_self y).symm
        _ = _ := congrArg wordReverse h
  simp only [permutationKernel, hcond]

end AESConcrete.WordFourierDiffusion
