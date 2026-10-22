import AESConcrete.ShortenedWeightedGeometry
import AESConcrete.DoubleUniformGeometry

/-!
# Actual two-zero plane for the (11,11) cap

Both selected types are (residual degree, active count) = (3,3). Their
inactive masks impose one actual input zero and one actual output zero. Every
retained output pair is an information set on the resulting plane. The
residual triple map is injective, not surjective: only subenergy is used.

Fixed independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct reference pairs and constructive AES10/14/16.

This module owns geometry and counting reindexing, not minor transport,
analytic energy, physical aggregation or certificate comparison.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeResidualPlaneGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

set_option maxRecDepth 100000
-- Development diagnostics report slow declarations; they add no proof premise.
set_option profiler true

abbrev Retained (pOut : SelectedSupport 3 3) := MaskCoordinates pOut.val.val.1
abbrev Residual (pIn : SelectedSupport 3 3) := MaskCoordinates pIn.val.val.1

/-- The first zero mask constrains outputs; the second constrains inputs. -/
abbrev PlaneCode (pOut pIn : SelectedSupport 3 3) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.2

instance planeFintype (pOut pIn : SelectedSupport 3 3) : Fintype (PlaneCode pOut pIn) := by
  classical
  exact inferInstance

theorem retainedMask_size (p : SelectedSupport 3 3) : maskSize p.val.val.1 = 3 := by
  have hd := p.val.property.2
  norm_num at hd
  exact hd

theorem inactiveMask_size (p : SelectedSupport 3 3) : maskSize p.val.val.2 = 1 := by
  have hp := p.property
  change maskSize p.val.val.2 + 3 = 4 at hp
  omega

theorem retainedCoordinates_card (p : SelectedSupport 3 3) :
    Fintype.card (Retained p) = 3 := by
  rw [maskCoordinates_card, retainedMask_size]

/--
With degree and activity both three, every unmarked label is inactive.
-/
theorem nonretained_inactive : ∀ (p : SelectedSupport 3 3) (i : Fin 4),
    maskBit p.val.val.1 i ≠ true → maskBit p.val.val.2 i = true := by decide

theorem inactive_iff_not_retained (p : SelectedSupport 3 3) (i : Fin 4) :
    maskBit p.val.val.2 i = true ↔ maskBit p.val.val.1 i ≠ true := by
  constructor
  · intro hi
    exact p.val.property.1 i hi
  · exact nonretained_inactive p i

attribute [local instance] Classical.propDecidable

def curve (pOut pIn : SelectedSupport 3 3) (c : PlaneCode pOut pIn) :
    Retained pOut → AES.Word := fun i => wordMixAddEquiv c.val i.val

def residualTuple (pOut pIn : SelectedSupport 3 3) (c : PlaneCode pOut pIn) :
    Residual pIn → AES.Word := fun i => c.val i.val

@[simp]
theorem curve_apply (pOut pIn : SelectedSupport 3 3)
    (c : PlaneCode pOut pIn) (i : Retained pOut) :
    curve pOut pIn c i = wordMixAddEquiv c.val i.val := rfl

theorem plane_code_card (pOut pIn : SelectedSupport 3 3) :
    Fintype.card (PlaneCode pOut pIn) = Fintype.card AES.Word ^ 2 := by
  calc
    _ = Fintype.card (ShortenedGraph wordMixAddEquiv.toAddMonoidHom
        pOut.val.val.2 pIn.val.val.2) :=
      Fintype.card_congr (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _)
    _ = _ := by
      -- Transport only the exponent; simplification must not visit the word cardinal.
      have hdim :
          4 - (maskSize pOut.val.val.2 + maskSize pIn.val.val.2) = 2 := by
        rw [inactiveMask_size, inactiveMask_size]
      exact (mds_graph_zero_count wordMixAddEquiv.toAddMonoidHom wordMixAddEquiv_zeroMDS
        pOut.val.val.2 pIn.val.val.2).trans
        (congrArg (fun n : ℕ => Fintype.card AES.Word ^ n) hdim)

/-- Any actual pair of retained output labels parametrizes the plane. -/
theorem retained_pair_bijective (pOut pIn : SelectedSupport 3 3) (s : Retained pOut) :
    Function.Bijective (fun c : PlaneCode pOut pIn =>
      fun i : {i : Retained pOut // i ≠ s} => curve pOut pIn c i.val) := by
  let pair := DoubleUniformGeometry.retainedPairMask pOut.val.val.1 s
  have hp : maskSize pair = 2 :=
    DoubleUniformGeometry.retainedPairMask_size _ (retainedMask_size pOut) s
  have hr : MaskDisjoint pOut.val.val.2 pair := by
    intro i hi hpair
    exact pOut.val.property.1 i hi
      ((DoubleUniformGeometry.retainedPairMask_bit _ s i).mp hpair).1
  have hsize : maskSize pOut.val.val.2 + maskSize pIn.val.val.2 + maskSize pair = 4 := by
    rw [inactiveMask_size, inactiveMask_size, hp]
  have hb : Function.Bijective (fun c : PlaneCode pOut pIn =>
      fun i : MaskCoordinates pair => wordMixAddEquiv.toAddMonoidHom c.val i.val) :=
    (RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS pOut.val.val.2 pIn.val.val.2 pair hr hsize).comp
        (graphEquiv wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 pIn.val.val.2).bijective
  exact (DoubleUniformGeometry.retainedPairCoordinatesEquiv (V := AES.Word)
    pOut.val.val.1 s).bijective.comp hb

private theorem sum_square_comp_le {C U : Type*} [Fintype C] [Fintype U]
    (f : C → U) (hf : Function.Injective f) (h : U → ℝ) :
    (∑ c, h (f c) ^ 2) ≤ ∑ u, h u ^ 2 := by
  classical
  calc
    (∑ c, h (f c) ^ 2) = ∑ u ∈ Finset.univ.image f, h u ^ 2 := by
      rw [Finset.sum_image]
      intro c _ d _ he
      exact hf he
    _ ≤ ∑ u ∈ (Finset.univ : Finset U), h u ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun u _ _ => sq_nonneg (h u))
    _ = ∑ u, h u ^ 2 := by simp

/-- Restricting the original signed state amplitude has no cardinality loss. -/
theorem plane_subenergy (pOut pIn : SelectedSupport 3 3) (G : AES.WordState → ℝ) :
    (∑ c : PlaneCode pOut pIn, G c.val ^ 2) ≤ ∑ x, G x ^ 2 :=
  sum_square_comp_le (fun c : PlaneCode pOut pIn => c.val)
    (fun _ _ he => Subtype.ext he) G

/-- The residual triple and the known input zero determine the physical state.
This is only injectivity; no parametrization by all residual triples is used. -/
theorem residualTuple_injective (pOut pIn : SelectedSupport 3 3) :
    Function.Injective (residualTuple pOut pIn) := by
  intro c d he
  apply Subtype.ext
  funext i
  by_cases hi : maskBit pIn.val.val.1 i = true
  · exact congrFun he (⟨i, hi⟩ : Residual pIn)
  · have hz := nonretained_inactive pIn i hi
    exact (c.property.2 i hz).trans (d.property.2 i hz).symm

/-- An arbitrary signed joint triple amplitude keeps subenergy on the plane. -/
theorem residual_subenergy (pOut pIn : SelectedSupport 3 3)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ c : PlaneCode pOut pIn, h (residualTuple pOut pIn c) ^ 2) ≤ ∑ u, h u ^ 2 :=
  sum_square_comp_le (residualTuple pOut pIn) (residualTuple_injective pOut pIn) h

end AESConcrete.ThreeResidualPlaneGeometry
