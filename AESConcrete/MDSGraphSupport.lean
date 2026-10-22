import AESConcrete.ActivityBranchZeros
import AESConcrete.ShortenedLineResponse
import AESConcrete.GraphColumnEnergy
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Partial graph support after MDS diffusion of a zero slab

For a four-coordinate additive MDS map, fixing one input coordinate to zero
makes any other three output coordinates an information set. The proof applies
the equal-size `(3,3)` ZeroMDS restriction to a difference. Consequently an
arbitrary signed function supported on that input zero slab has partial graph
support after pullback through the inverse diffusion.

The generic geometry comes first, then an exact-support input bridge and the
actual `wordMixAddEquiv` specializations. This file proves support statements
only: no graph-energy estimate, physical cap, or return bound is asserted.
Independent uniform retained keys, whitening, omitted final MixColumns and
ordered-distinct pairs remain the intended AES model.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MDSGraphSupport
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.RefinedWordProjection (supportIndexKernel)
open AESConcrete.GraphColumnEnergy (SupportedOnGraph)

variable {V : Type*}

/-- Separate any distinguished physical coordinate from the other three.
The inverse is insertion at the same coordinate, without changing labels. -/
def splitAt (s : Fin 4) : (Fin 4 → V) ≃ V × (Fin 3 → V) where
  toFun z := (z s, Fin.removeNth s z)
  invFun p := Fin.insertNth s p.1 p.2
  left_inv z := Fin.insertNth_eq_iff.mpr ⟨rfl, rfl⟩
  right_inv p := by
    rcases p with ⟨v, w⟩
    simp

private theorem complement_singleton_bit (s i : Fin 4) :
    maskBit (maskComplement (singletonMask s)) i = true ↔ i ≠ s := by
  rw [maskComplement_bit]
  have hs := singletonMask_bit s i
  cases hb : maskBit (singletonMask s) i <;> simp_all

section Generic
variable [AddCommGroup V]

/-- The `(3,3)` MDS information-set implication, expressed without a mask
parameterization: one zero input coordinate and agreement off one output
coordinate force equality of the two source points. -/
theorem zero_slab_points_equal
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 4) (x x' : Fin 4 → V) (hx : x r = 0) (hx' : x' r = 0)
    (heq : ∀ i, i ≠ s → L x i = L x' i) : x = x' := by
  apply sub_eq_zero.mp
  apply hL (maskComplement (singletonMask s)) (maskComplement (singletonMask r))
    (by simp only [maskComplement_size, singletonMask_size])
  · funext i
    by_cases hi : maskBit (maskComplement (singletonMask r)) i = true
    · simp [maskProjection, hi]
    · have hir : i = r := by
        by_contra hir
        exact hi ((complement_singleton_bit r i).mpr hir)
      subst i
      simp [maskProjection, hi, hx, hx']
  · rw [map_sub]
    funext i
    by_cases hi : maskBit (maskComplement (singletonMask s)) i = true
    · have his : i ≠ s := (complement_singleton_bit s i).mp hi
      simp [maskProjection, hi, heq i his]
    · simp [maskProjection, hi]

/-- Dropping any output coordinate is injective on the nonzero support of
the diffused zero-slab function `z ↦ f (L.symm z)`. No factorization, sign or
normalization premise is required of `f`. -/
theorem zero_slab_pullback_support_injective
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 4) (f : (Fin 4 → V) → ℝ)
    (hzero : ∀ x, f x ≠ 0 → x r = 0)
    (z z' : Fin 4 → V) (hz : f (L.symm z) ≠ 0) (hz' : f (L.symm z') ≠ 0)
    (heq : ∀ i, i ≠ s → z i = z' i) : z = z' := by
  apply L.symm.injective
  apply zero_slab_points_equal L.toAddMonoidHom hL r s
    (L.symm z) (L.symm z') (hzero _ hz) (hzero _ hz')
  intro i hi
  change L (L.symm z) i = L (L.symm z') i
  rw [L.apply_symm_apply, L.apply_symm_apply]
  exact heq i hi

/-- Product-indexed partial graph condition for the input of the graph-column
energy lemma. The distinguished output coordinate is arbitrary. -/
theorem zero_slab_pullback_fiber_unique
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 4) (f : (Fin 4 → V) → ℝ)
    (hzero : ∀ x, f x ≠ 0 → x r = 0) :
    ∀ (w : Fin 3 → V) (v v' : V),
      f (L.symm (Fin.insertNth s v w)) ≠ 0 →
      f (L.symm (Fin.insertNth s v' w)) ≠ 0 → v = v' := by
  intro w v v' hv hv'
  -- Elaboration: fix the constant codomain before the dependent insertNth API.
  have he : (Fin.insertNth s v w : Fin 4 → V) = Fin.insertNth s v' w := by
    apply zero_slab_pullback_support_injective L hL r s f hzero _ _ hv hv'
    intro i hi
    obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
    rw [← hj]
    simp
  simpa only [Fin.insertNth_apply_same] using congrFun he s

/-- Classical completion of the partial graph after diffusion. Empty fibers
are allowed; the assertion does not require graph surjectivity. -/
theorem zero_slab_pullback_supported_graph
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 4) (f : (Fin 4 → V) → ℝ)
    (hzero : ∀ x, f x ≠ 0 → x r = 0) :
    ∃ g : (Fin 3 → V) → V,
      SupportedOnGraph g (fun p : V × (Fin 3 → V) =>
        f (L.symm ((splitAt s).symm p))) := by
  letI : Nonempty V := ⟨0⟩
  apply GraphColumnEnergy.exists_supported_graph_of_fiber_unique
  exact zero_slab_pullback_fiber_unique L hL r s f hzero

end Generic

section ExactSupport
variable [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- A genuine exact-support projection vanishes away from any selected
inactive input coordinate. This supplies the slab premise without assuming
that the remaining three-coordinate input factors. -/
theorem supportIndexComponent_inactive_zero {d : ℕ} (p : SupportIndex d)
    (r : Fin 4) (hr : maskBit p.val.2 r = true)
    (f : (Fin 4 → V) → ℝ) :
    ∀ x, supportIndexComponent (0 : V) p f x ≠ 0 → x r = 0 := by
  intro x hnonzero
  by_contra hx
  apply hnonzero
  change (∑ y, supportIndexKernel (0 : V) p x y * f y) = 0
  apply Finset.sum_eq_zero
  intro y _
  have hk : supportIndexKernel (0 : V) p x y = 0 := by
    by_contra hk
    exact hx (ActivityBranchZeros.supportIndexKernel_inactive_row p x y hk r hr)
  rw [hk, zero_mul]

/-- The partial graph condition for one exact inactive-support source piece. -/
theorem supportIndex_pullback_fiber_unique {d : ℕ}
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SupportIndex d) (r s : Fin 4) (hr : maskBit p.val.2 r = true)
    (f : (Fin 4 → V) → ℝ) :
    ∀ (w : Fin 3 → V) (v v' : V),
      supportIndexComponent (0 : V) p f (L.symm (Fin.insertNth s v w)) ≠ 0 →
      supportIndexComponent (0 : V) p f (L.symm (Fin.insertNth s v' w)) ≠ 0 →
        v = v' :=
  zero_slab_pullback_fiber_unique L hL r s (supportIndexComponent (0 : V) p f)
    (supportIndexComponent_inactive_zero p r hr f)

end ExactSupport

-- Dependency boundary: the actual AES specialization uses the already exposed
-- physical additive equivalence and its ZeroMDS theorem. Generic support
-- geometry above contains no numerical AES resource or operator estimate.

/-- Actual physical four-word diffusion of an arbitrary zero-slab input. -/
theorem word_zero_slab_pullback_support_injective
    (r s : Fin 4) (f : AES.WordState → ℝ)
    (hzero : ∀ x, f x ≠ 0 → x r = 0)
    (z z' : AES.WordState)
    (hz : f (WordCrossZero.wordMixAddEquiv.symm z) ≠ 0)
    (hz' : f (WordCrossZero.wordMixAddEquiv.symm z') ≠ 0)
    (heq : ∀ i, i ≠ s → z i = z' i) : z = z' :=
  zero_slab_pullback_support_injective WordCrossZero.wordMixAddEquiv
    WordCrossZero.wordMixAddEquiv_zeroMDS r s f hzero z z' hz hz' heq

/-- Actual word specialization, in the partial graph API used downstream. -/
theorem word_zero_slab_pullback_fiber_unique
    (r s : Fin 4) (f : AES.WordState → ℝ)
    (hzero : ∀ x, f x ≠ 0 → x r = 0) :
    ∀ (w : Fin 3 → AES.Word) (v v' : AES.Word),
      f (WordCrossZero.wordMixAddEquiv.symm (Fin.insertNth s v w)) ≠ 0 →
      f (WordCrossZero.wordMixAddEquiv.symm (Fin.insertNth s v' w)) ≠ 0 → v = v' :=
  zero_slab_pullback_fiber_unique WordCrossZero.wordMixAddEquiv
    WordCrossZero.wordMixAddEquiv_zeroMDS r s f hzero

/-- Actual exact-support source pieces, including each `(3,3)` source piece
once its single inactive input coordinate has been selected. -/
theorem word_supportIndex_pullback_fiber_unique {d : ℕ}
    (p : SupportIndex d) (r s : Fin 4) (hr : maskBit p.val.2 r = true)
    (f : AES.WordState → ℝ) :
    ∀ (w : Fin 3 → AES.Word) (v v' : AES.Word),
      supportIndexComponent (0 : AES.Word) p f
        (WordCrossZero.wordMixAddEquiv.symm (Fin.insertNth s v w)) ≠ 0 →
      supportIndexComponent (0 : AES.Word) p f
        (WordCrossZero.wordMixAddEquiv.symm (Fin.insertNth s v' w)) ≠ 0 → v = v' :=
  supportIndex_pullback_fiber_unique WordCrossZero.wordMixAddEquiv
    WordCrossZero.wordMixAddEquiv_zeroMDS p r s hr f

end AESConcrete.MDSGraphSupport
