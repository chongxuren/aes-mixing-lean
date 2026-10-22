import AES8.Math.PaperRestrictedDiffusionGeometry
import AESConcrete.ShortenedLineResponse
import Mathlib.Logic.Equiv.Sum

/-!
# The checked AES diffusion is MDS in the generic graph interface

The legacy AES result says that each square masked submatrix has trivial
kernel (`ZeroMDS`). The current paper interface requires bijection on every
four physical coordinates of the input/output graph (`IsMDS`). This adapter
derives the latter using the checked zero-count argument and equality of
finite cardinalities. The two copies keep their physical input/output roles.
No information-set property or probability estimate is a premise.
Constructive mathematics only; no attacks or numerical searches.
-/

noncomputable section
namespace AES8.PaperAESSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open PaperMDSGram PaperRestrictedDiffusion
attribute [local instance] Classical.propDecidable

private def predicateMask (p : Fin 4 → Prop) : Fin 16 :=
  maskBitsEquiv.symm (fun i => decide (p i))

private theorem predicateMask_bit (p : Fin 4 → Prop) (i : Fin 4) :
    maskBit (predicateMask p) i = true ↔ p i := by
  have h := congrFun (maskBitsEquiv.apply_symm_apply (fun i => decide (p i))) i
  change maskBit (predicateMask p) i = decide (p i) at h
  simp only [h, decide_eq_true_eq]

private theorem predicateMask_size (p : Fin 4 → Prop) :
    maskSize (predicateMask p) = Fintype.card {i : Fin 4 // p i} := by
  rw [← maskCoordinates_card]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (predicateMask_bit p))

/-- The concrete square-minor zero criterion entails the paper's arbitrary
physical information-set criterion. No enumeration of field words is used. -/
theorem graph_isMDS_of_zeroMDS {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) :
    IsMDS (graph L) 4 := by
  intro p hp
  have hp' : Fintype.card {j : Fin 4 ⊕ Fin 4 // p j} = 4 := by
    simpa only [Nat.card_eq_fintype_card] using hp
  let inp := predicateMask (fun i => p (Sum.inl i))
  let out := predicateMask (fun i => p (Sum.inr i))
  have hsize : maskSize out + maskSize inp = 4 := by
    have hc := Fintype.card_congr
      (Equiv.subtypeSum (p := p) : {j : Fin 4 ⊕ Fin 4 // p j} ≃
        {i : Fin 4 // p (Sum.inl i)} ⊕ {i : Fin 4 // p (Sum.inr i)})
    rw [Fintype.card_sum, hp'] at hc
    dsimp [inp, out]
    rw [predicateMask_size, predicateMask_size]
    omega
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro c d h
    have hz : (graphEquiv L).symm c - (graphEquiv L).symm d = 0 := by
      apply mds_graph_zero_high L hL out inp (by omega)
      constructor
      · intro i hi
        have hpi : p (Sum.inr i) := (predicateMask_bit _ i).mp hi
        have he := congrFun h ⟨Sum.inr i, hpi⟩
        change c.val (Sum.inr i) = d.val (Sum.inr i) at he
        rw [map_sub]
        change L (fun i => c.val (Sum.inl i)) i -
          L (fun i => d.val (Sum.inl i)) i = 0
        rw [congrFun c.property i, congrFun d.property i, he, sub_self]
      · intro i hi
        have hpi : p (Sum.inl i) := (predicateMask_bit _ i).mp hi
        have he := congrFun h ⟨Sum.inl i, hpi⟩
        change c.val (Sum.inl i) = d.val (Sum.inl i) at he
        change c.val (Sum.inl i) - d.val (Sum.inl i) = 0
        exact sub_eq_zero.mpr he
    exact (graphEquiv L).symm.injective (sub_eq_zero.mp hz)
  · calc
      Fintype.card (graph L) = Fintype.card (Fin 4 → V) :=
        Fintype.card_congr (graphEquiv L).symm
      _ = Fintype.card V ^ 4 := by simp
      _ = Fintype.card ({j : Fin 4 ⊕ Fin 4 // p j} → V) := by
        simp only [Fintype.card_fun, hp']

/-- Both checked AES directions meet the current generic source theorem. -/
theorem byteDiffusion_graph_isMDS (inverse : Bool) :
    IsMDS (graph (AESConcrete.ShortenedLineResponse.byteDiffusionHom inverse)) 4 :=
  graph_isMDS_of_zeroMDS _
    (AESConcrete.ShortenedLineResponse.byteDiffusionHom_zeroMDS inverse)

end AES8.PaperAESSource
