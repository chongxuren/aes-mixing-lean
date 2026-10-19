import AESMixing.WordMDS
import AESMixing.SupportNorm
import AESMixing.SupportDegreeDecomposition
import AESMixing.DegreeBilinear
import AESMixing.MDSInverse

/-!
# Exact activity / one-residual cancellation on the AES word alphabet

The concrete specialization uses `AES.Word`, whose cardinality is `2^32`,
and the physical four-word diffusion `AES.wordMix`.  It is not a reuse of a
byte-alphabet Gram certificate under a different name.

The generic support-incidence bound already has a zero surviving-dimension
coefficient when the total marked residual degree is one.  We expose that
case and sum the existing exact support decomposition.  No word operator
norm, column estimate, Gram moment, or final scalar bound is assumed.

These are raw diffusion identities.  Connecting them through the parallel
word channel and the centered extension `S = T - U` remains a separate step.
This module concerns constructive bounds only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.WordCrossZero
open AESMixing

/-- With one marked residual leg, no integer shortening dimension survives. -/
theorem incidence_coefficient_zero_one (m : ℝ) (n : ℕ) :
    incidenceNormCoefficient m n 0 1 = 0 := by
  unfold incidenceNormCoefficient
  by_cases hn : 4 ≤ n
  · simp only [hn, true_or, if_true]
  · have hsmall : n + 0 + 1 ≤ 4 := by omega
    simp only [hsmall, or_true, if_true]

/-- The inclusion-exclusion sum stays zero for every exact inactive support. -/
theorem shortening_sum_zero_one (m : ℝ) (r z out inp : Fin 16)
    (s : Finset GraphPosition)
    (hout : AES.maskSize out = 0) (hinp : AES.maskSize inp = 1) :
    shorteningNormSum m r z s out inp = 0 := by
  unfold shorteningNormSum
  apply Finset.sum_eq_zero
  intro t _
  rw [hout, hinp]
  exact incidence_coefficient_zero_one m _

section GenericMDS

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Exact support cancellation for arbitrary joint real input functions.
The marked input has degree one; the output is activity-only. -/
theorem support_zero_one_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hout : AES.maskSize out = 0) (hinp : AES.maskSize inp = 1)
    (f g : (Fin 4 → V) → ℝ) :
    (∑ x : Fin 4 → V,
      action (supportProduct 0 (AES.maskBit out) (AES.maskBit r)) g (L x) *
      action (supportProduct 0 (AES.maskBit inp) (AES.maskBit z)) f x) = 0 := by
  have hcard : 0 < Fintype.card (MaskCoordinates inp) := by
    rw [maskCoordinates_card, hinp]
    norm_num
  obtain ⟨k⟩ := Fintype.card_pos_iff.mp hcard
  have hbound := supportProduct_diffusion_bilinear L hL hn r z out inp hr hz k f g
  rw [shortening_sum_zero_one _ _ _ _ _ _ hout hinp] at hbound
  simp only [zero_div, zero_mul] at hbound
  exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))

/-- Indexed exact supports carry their disjointness and degree hypotheses. -/
theorem supportIndex_zero_one_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (p : SupportIndex 0) (q : SupportIndex 1)
    (f g : (Fin 4 → V) → ℝ) :
    (∑ x : Fin 4 → V,
      supportIndexComponent 0 p g (L x) * supportIndexComponent 0 q f x) = 0 := by
  exact support_zero_one_bilinear L hL hn p.val.2 q.val.2 p.val.1 q.val.1
    p.property.1 q.property.1 p.property.2 q.property.2 f g

/-- Summing all exact support pieces gives the full degree-zero/one identity. -/
theorem degree_zero_one_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (f g : (Fin 4 → V) → ℝ) :
    (∑ x : Fin 4 → V,
      degreeComponent 0 0 g (L x) * degreeComponent 0 1 f x) = 0 := by
  rw [← supportIndex_decomposition (0 : V) (0 : Fin 5) g,
    ← supportIndex_decomposition (0 : V) (1 : Fin 5) f]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro q _
  exact supportIndex_zero_one_bilinear L hL hn q p f g

/-- The raw degree-zero/one transfer has exactly zero energy.
The bilinear-to-energy theorem supplies the actual projected transfer. -/
theorem degree_zero_one_energy
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeTransfer 0 0 1 L.toEquiv f x ^ 2) = 0 := by
  have hb := degreeTransfer_energy_of_bilinear (0 : V) hn 0 1 L.toEquiv 0
    (by norm_num)
    (by
      intro u v
      change |∑ x, degreeComponent (0 : V) 0 v (L.toAddMonoidHom x) *
        degreeComponent 0 1 u x| ≤ _
      rw [degree_zero_one_bilinear L.toAddMonoidHom hL hn u v]
      simp) f
  exact le_antisymm (by simpa using hb)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- A zero sum of nonnegative squares gives pointwise cancellation. -/
theorem degree_zero_one_apply
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) (x : Fin 4 → V) :
    degreeTransfer 0 0 1 L.toEquiv f x = 0 := by
  have hsq : degreeTransfer 0 0 1 L.toEquiv f x ^ 2 ≤ 0 := by
    calc
      _ ≤ ∑ y, degreeTransfer 0 0 1 L.toEquiv f y ^ 2 :=
        Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
      _ = 0 := degree_zero_one_energy L hL hn f
  exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))

/-- The inverse MDS identity and adjoint transfer give the reverse block.
This is an identity for arbitrary joint functions, with no centered-input
condition and no use of a norm cap. -/
theorem degree_one_zero_energy
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeTransfer 0 1 0 L.toEquiv f x ^ 2) = 0 := by
  have hbound (u : (Fin 4 → V) → ℝ) :
      (∑ y, degreeTransfer 0 0 1 L.symm.toEquiv u y ^ 2) ≤
        (0 : ℝ) ^ 2 * ∑ x, u x ^ 2 := by
    rw [degree_zero_one_energy L.symm (zeroMDS_inverse L hL) hn u]
    simp
  have hb := degreeTransfer_reverse_bound (0 : V) 0 1 L.symm.toEquiv 0 hbound f
  exact le_antisymm (by simpa using hb)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Pointwise form of the reverse degree-one/zero cancellation. -/
theorem degree_one_zero_apply
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) (x : Fin 4 → V) :
    degreeTransfer 0 1 0 L.toEquiv f x = 0 := by
  have hsq : degreeTransfer 0 1 0 L.toEquiv f x ^ 2 ≤ 0 := by
    calc
      _ ≤ ∑ y, degreeTransfer 0 1 0 L.toEquiv f y ^ 2 :=
        Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ x)
      _ = 0 := degree_one_zero_energy L hL hn f
  exact sq_eq_zero_iff.mp (le_antisymm hsq (sq_nonneg _))

end GenericMDS

/-- The physical word diffusion is a permutation because each physical
linear layer and the word/byte transposition is injective. -/
theorem wordMix_injective : Function.Injective AES.wordMix := by
  intro x y hxy
  change AES.transposeState.symm (AES.wordDiffusion (AES.transposeState x)) =
    AES.transposeState.symm (AES.wordDiffusion (AES.transposeState y)) at hxy
  exact AES.transposeState.injective
    (AES.wordDiffusion_injective (AES.transposeState.symm.injective hxy))

/-- The same concrete `AES.wordMix`, equipped with its actual inverse. -/
def wordMixAddEquiv : AES.WordState ≃+ AES.WordState :=
  AddEquiv.ofBijective AES.wordMix
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨wordMix_injective, rfl⟩)

@[simp] theorem wordMixAddEquiv_apply (x : AES.WordState) :
    wordMixAddEquiv x = AES.wordMix x := rfl

theorem wordMixAddEquiv_zeroMDS : ZeroMDS wordMixAddEquiv :=
  AES.wordMix_zeroMDS

/-- Concrete four-word AES diffusion, retaining every exact support choice. -/
theorem word_support_zero_one_bilinear (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hout : AES.maskSize out = 0) (hinp : AES.maskSize inp = 1)
    (f g : AES.WordState → ℝ) :
    (∑ x : AES.WordState,
      action (supportProduct (0 : AES.Word) (AES.maskBit out) (AES.maskBit r)) g
        (AES.wordMix x) *
      action (supportProduct (0 : AES.Word) (AES.maskBit inp) (AES.maskBit z)) f x) = 0 := by
  apply support_zero_one_bilinear AES.wordMix AES.wordMix_zeroMDS
    (by rw [AES.word_card]; norm_num) r z out inp hr hz hout hinp f g

/-- The degree counts residual 32-bit words, not residual bytes inside a word. -/
theorem word_degree_zero_one_bilinear (f g : AES.WordState → ℝ) :
    (∑ x : AES.WordState,
      degreeComponent (0 : AES.Word) 0 g (AES.wordMix x) *
      degreeComponent (0 : AES.Word) 1 f x) = 0 :=
  degree_zero_one_bilinear AES.wordMix AES.wordMix_zeroMDS
    (by rw [AES.word_card]; norm_num) f g

/-- Actual four-word raw degree-zero/one block, with zero energy. -/
theorem word_degree_zero_one_energy (f : AES.WordState → ℝ) :
    (∑ x, degreeTransfer (0 : AES.Word) 0 1 wordMixAddEquiv.toEquiv f x ^ 2) = 0 :=
  degree_zero_one_energy wordMixAddEquiv wordMixAddEquiv_zeroMDS
    (by rw [AES.word_card]; norm_num) f

/-- Pointwise cancellation for the actual raw degree-zero/one block. -/
theorem word_degree_zero_one_apply (f : AES.WordState → ℝ) (x : AES.WordState) :
    degreeTransfer (0 : AES.Word) 0 1 wordMixAddEquiv.toEquiv f x = 0 :=
  degree_zero_one_apply wordMixAddEquiv wordMixAddEquiv_zeroMDS
    (by rw [AES.word_card]; norm_num) f x

/-- Actual four-word raw degree-one/zero block, with zero energy. -/
theorem word_degree_one_zero_energy (f : AES.WordState → ℝ) :
    (∑ x, degreeTransfer (0 : AES.Word) 1 0 wordMixAddEquiv.toEquiv f x ^ 2) = 0 :=
  degree_one_zero_energy wordMixAddEquiv wordMixAddEquiv_zeroMDS
    (by rw [AES.word_card]; norm_num) f

/-- Pointwise cancellation for the actual raw degree-one/zero block. -/
theorem word_degree_one_zero_apply (f : AES.WordState → ℝ) (x : AES.WordState) :
    degreeTransfer (0 : AES.Word) 1 0 wordMixAddEquiv.toEquiv f x = 0 :=
  degree_one_zero_apply wordMixAddEquiv wordMixAddEquiv_zeroMDS
    (by rw [AES.word_card]; norm_num) f x

end AESConcrete.WordCrossZero
