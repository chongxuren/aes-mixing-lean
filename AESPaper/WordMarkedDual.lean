import AESPaper.WordMarkedCode

/-!
# High-dimensional moments of the actual marked word image

WordMarkedCode supplies the actual image and its MDS-derived complementary
information sets. Here the product of the four byte trace pairings supplies
the word Fourier transform, with counting normalization 1/65536. Conjugation
toggles each actual Fourier flag and leaves its actual transpose flag fixed.
The normalized source is identified with the actual unit subgroup indicator
before Fourier energy is transported to its annihilator. No global dual
boundary formula or desired energy bound is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordMarkedDual
open AESMixing AESConcrete
open AESMixing.AES (maskSize)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros)
open AESConcrete.WordFourierVariants (variant)
open AESConcrete.WordFourierCore (wordConjugate wordConjugate_twice)
open AESPaper.WordMarkedMoment
  (q tau delta word_card_real variant_gram_moment_le variant_gram_diagonal_le)
open AESPaper.WordMarkedCode
  (markedCode normalized_source_eq_code actual_dual_projection_bijective)
attribute [local instance] Classical.propDecidable

/-- Whole-word Fourier conjugation toggles only the Fourier flag. In
particular, this does not assume Fourier invariance of an AES residual. -/
theorem variant_conjugate (adjoint fourier : Bool) :
    fourierConjugate WordFourierCore.wordPairing (variant adjoint fourier) =
      variant adjoint (!fourier) := by
  change wordConjugate (variant adjoint fourier) = variant adjoint (!fourier)
  cases fourier <;> simp [variant, wordConjugate_twice]

theorem variant_conjugate_diagonal_le (adjoint fourier : Bool) (a : AES.Word) :
    gram (fourierConjugate WordFourierCore.wordPairing (variant adjoint fourier)) a a ≤ delta := by
  rw [variant_conjugate]
  exact variant_gram_diagonal_le adjoint (!fourier) a

section GenericWordCode
variable {K I J : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Word specialization of generic dual energy. The information sets refer
to the actual word trace-character annihilator of the supplied subgroup. -/
theorem actual_subgroup_energy_dual_le
    (adjoint fourier : K → Bool) (C : AddSubgroup (K → AES.Word)) [Fintype C]
    (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : (WordFourierCore.wordPairing.product K).annihilator C =>
      fun i : I => c.val (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : (WordFourierCore.wordPairing.product K).annihilator C =>
      fun i : I => c.val (idx (Sum.inr (Sum.inl i))))) :
    (∑ y : K → AES.Word,
      action (coordinateKernel (fun k => variant (adjoint k) (fourier k)))
        (unitSubgroupIndicator C) y ^ 2) ≤
      (tau ^ 2 / q) ^ Fintype.card I * delta ^ Fintype.card J := by
  have h := MixedCodeMoment.subgroup_energy_dual_le WordFourierCore.wordPairing word_add_self
    (fun k => variant (adjoint k) (fourier k)) C idx he hf (tau ^ 2) delta
    (sq_nonneg tau) (by norm_num [delta, q])
    (fun k => variant_gram_moment_le (adjoint k) (fourier k))
    (fun k a => variant_conjugate_diagonal_le (adjoint k) (fourier k) a)
  simpa only [word_card_real] using h

end GenericWordCode

section ActualSource
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Both actual dual physical information sets follow from the primal MDS
complements. The two maps use one common dual code, not independent labels. -/
theorem actual_dual_information_sets_bijective
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (idx : CodePosition I J ≃ Marked m)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      (Fintype.card (Marked m)-Fintype.card I) = 4) :
    Function.Bijective
        (fun c : (WordFourierCore.wordPairing.product (Marked m)).annihilator (markedCode m s) =>
          fun i : I => c.val (idx (Sum.inl i))) ∧
      Function.Bijective
        (fun c : (WordFourierCore.wordPairing.product (Marked m)).annihilator (markedCode m s) =>
          fun i : I => c.val (idx (Sum.inr (Sum.inl i)))) := by
  constructor
  · apply actual_dual_projection_bijective m s (fun i : I => idx (Sum.inl i)) _ hsize
    intro i j h
    exact Sum.inl.inj (idx.injective h)
  · apply actual_dual_projection_bijective m s
      (fun i : I => idx (Sum.inr (Sum.inl i))) _ hsize
    intro i j h
    exact Sum.inl.inj (Sum.inr.inj (idx.injective h))

/-- Actual high-dimensional shortened-source moment. The physical source
and source/image normalization are proved before invoking dual energy. -/
theorem actual_normalized_high_energy_le
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (adjoint fourier : Marked m → Bool) (idx : CodePosition I J ≃ Marked m)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      (Fintype.card (Marked m)-Fintype.card I) = 4) :
    (∑ y : Marked m → AES.Word,
      MixedCodeMoment.normalizedResponse
        (fun p => variant (adjoint p) (fourier p))
        (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y ^ 2) ≤
      (tau ^ 2 / q) ^ Fintype.card I * delta ^ Fintype.card J := by
  have hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m) := by omega
  rw [normalized_source_eq_code m s hhigh]
  obtain ⟨he, hf⟩ := actual_dual_information_sets_bijective m s idx hsize
  exact actual_subgroup_energy_dual_le adjoint fourier (markedCode m s) idx he hf

end ActualSource
end AESPaper.WordMarkedDual
