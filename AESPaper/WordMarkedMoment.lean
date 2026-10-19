import AESPaper.LocalAES
import AESPaper.ActivityKernel
import AESConcrete.ActualMarkedCodeMoment

/-!
# Low-dimensional moments for actual marked word codes

Each physical leg independently fixes its transpose and whole-word Fourier
flags. The generic mixed-moment theorem is used with V = AES.Word and with
the actual two coordinate restrictions of one common shortened source.
These two bijections are proved by the actual boundary's ZeroMDS theorem;
they are not a joint-independence premise.

This module uses only the alphabet-generic part of ActualMarkedCodeMoment
and MixedCodeMoment. None of their byte constants or actual-byte wrappers
is used. The nested local Gram moment is explicitly reindexed to Word x Word.
The response normalization is sqrt(card Source), in counting measure.
This is the primal low-dimensional branch only: no concrete dual, activity
choice-array bound, or complete four-round operator bound is asserted.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordMarkedMoment
open AESMixing AESConcrete
open AESMixing.AES (maskSize)
open AESConcrete.WordFourierVariants (variant)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros)
attribute [local instance] Classical.propDecidable

/-- Exact word alphabet size. -/
def q : ℝ := 2^32

/-- Square root of the local Gram-moment upper bound. -/
def tau : ℝ := 300 / q

/-- Uniform upper bound on each word residual Gram diagonal. -/
def delta : ℝ := 2 / (15 * q)

theorem word_card_real : (Fintype.card AES.Word : ℝ) = q := by
  rw [AESConcrete.AES.word_card_exact]
  norm_num [q]

/-- Reindex the two nested word sums to the product alphabet required by
the generic code-moment theorem, preserving the same Gram convention. -/
theorem variant_gram_moment_le (adjoint fourier : Bool) :
    (∑ ab : AES.Word × AES.Word, gram (variant adjoint fourier) ab.1 ab.2 ^ 2) ≤
      tau ^ 2 := by
  simpa only [Fintype.sum_prod_type, gram, tau, q] using
    LocalAES.local_gram_moment adjoint fourier

theorem variant_gram_diagonal_le (adjoint fourier : Bool) (a : AES.Word) :
    gram (variant adjoint fourier) a a ≤ delta := by
  rw [gram_diagonal]
  exact (LocalAES.local_column_energy adjoint fourier a).le

section GenericWordResponse
variable {C K I J : Type*} [Fintype C] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Independently selected actual word variants on every leg. Only the two
bijective physical coordinate restrictions remain as hypotheses. -/
theorem normalizedResponse_energy_le_of_bijective
    (adjoint fourier : K → Bool) (coord : C → K → AES.Word)
    (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : I => coord c (idx (Sum.inl i))))
    (hf : Function.Bijective
      (fun c : C => fun i : I => coord c (idx (Sum.inr (Sum.inl i))))) :
    (∑ y : K → AES.Word,
      MixedCodeMoment.normalizedResponse
        (fun k => variant (adjoint k) (fourier k)) coord y ^ 2) ≤
      (tau ^ 2 / q) ^ Fintype.card I * delta ^ Fintype.card J := by
  have h := MixedCodeMoment.normalizedResponse_energy_le_of_bijective
    (fun k => variant (adjoint k) (fourier k)) coord idx he hf (tau ^ 2) delta
    (sq_nonneg tau) (by norm_num [delta, q])
    (fun k => variant_gram_moment_le (adjoint k) (fourier k))
    (fun k => variant_gram_diagonal_le (adjoint k) (fourier k))
  simpa only [word_card_real] using h

end GenericWordResponse

section ActualPhysicalSource
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The source shortened from the graph of the actual forward AES boundary. -/
abbrev Source (m : GraphPosition → Bool) (s : Activity m → Bool) :=
  ShortenedGraph GroupedRecurrence.boundary.toAddMonoidHom
    (outputZeros m s) (inputZeros m s)

/-- `sourceCoordinates` selects the actual graph pair (boundary x,x).
In particular, input graph positions are never replaced by new source labels. -/
theorem sourceCoordinates_physical (m : GraphPosition → Bool)
    (s : Activity m → Bool) (c : Source m s) (p : Marked m) :
    sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c p =
      Sum.elim (GroupedRecurrence.boundary c.val) c.val p.val := rfl

/-- Every injected marked selection of the source dimension is an actual
physical information set of this same shortened graph. -/
theorem actual_selected_projection_bijective
    (m : GraphPosition → Bool) (s : Activity m → Bool) (p : I → Marked m)
    (hp : Function.Injective p)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card I = 4) :
    Function.Bijective (fun c : Source m s => fun i : I =>
      Sum.elim (GroupedRecurrence.boundary c.val) c.val (p i).val) := by
  exact ActualMarkedCodeMoment.marked_projection_bijective
    GroupedRecurrence.boundary.toAddMonoidHom ActivityKernel.aesBoundary_zeroMDS
    m s p hp hsize

/-- Both physical restrictions are bijections of one source. No statement
of independence between those restrictions is needed or inferred. -/
theorem actual_information_sets_bijective
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (idx : CodePosition I J ≃ Marked m)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card I = 4) :
    Function.Bijective (fun c : Source m s => fun i : I =>
      sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c
        (idx (Sum.inl i))) ∧
    Function.Bijective (fun c : Source m s => fun i : I =>
      sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c
        (idx (Sum.inr (Sum.inl i)))) := by
  constructor
  · apply actual_selected_projection_bijective m s (fun i : I => idx (Sum.inl i))
      _ hsize
    intro i j h
    exact Sum.inl.inj (idx.injective h)
  · apply actual_selected_projection_bijective m s
      (fun i : I => idx (Sum.inr (Sum.inl i))) _ hsize
    intro i j h
    exact Sum.inl.inj (Sum.inr.inj (idx.injective h))

/-- Actual low-dimensional shortened-code response with arbitrary separately
fixed ordinary/adjoint/Fourier choices on the marked physical legs. -/
theorem actual_normalized_low_energy_le
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (adjoint fourier : Marked m → Bool) (idx : CodePosition I J ≃ Marked m)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card I = 4) :
    (∑ y : Marked m → AES.Word,
      MixedCodeMoment.normalizedResponse
        (fun p => variant (adjoint p) (fourier p))
        (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y ^ 2) ≤
      (tau ^ 2 / q) ^ Fintype.card I * delta ^ Fintype.card J := by
  obtain ⟨he, hf⟩ := actual_information_sets_bijective m s idx hsize
  exact normalizedResponse_energy_le_of_bijective adjoint fourier
    (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) idx he hf

end ActualPhysicalSource
end AESPaper.WordMarkedMoment
