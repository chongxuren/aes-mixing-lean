import AES8.Math.PaperMDSShortening
import AES8.Math.PaperMDSOverlap
import AES8.Math.PaperKernelReindex

/-! An affine MDS code as a physical shortening with no fixed coordinates.
The equivalences preserve actual coordinate values and attained outside labels.
They permit reuse of normalized HS and thin estimates without dropping fibers. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperUnshortenedCode
open PaperMDSGram PaperMDSFiber PaperMDSOverlap PaperMDSShortening
open PaperFiberKernel PaperKernelBounds PaperKernelReindex
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

def asShortening (C : AddSubgroup (K → V)) (s n : ℕ)
    (hle : s ≤ Fintype.card K) (hC : IsMDS C s) (offset : K → V)
    (middle : Fin n ↪ K) (observed : Finset K)
    (hd : ∀ a, middle a ∉ observed) : PhysicalShortening K V s n where
  code := C
  dimension := s
  dimension_le := hle
  mds := hC
  offset := offset
  fixed := ∅
  target := 0
  remaining := by simp
  middle := middle
  middle_unfixed := by simp
  observed := observed
  outside_unfixed := by simp
  middle_outside := hd

def emptyFiberEquiv (C : AddSubgroup (K → V)) (offset : K → V) :
    AffineCode C offset ≃ AffineFiber C offset ∅ 0 where
  toFun x := ⟨x.val, x.property, by simp⟩
  invFun x := ⟨x.val, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem emptyFiberEquiv_val (C : AddSubgroup (K → V))
    (offset : K → V) (x : AffineCode C offset) :
    (emptyFiberEquiv C offset x).val = x.val := rfl

def emptyLabelsEquiv (C : AddSubgroup (K → V)) (offset : K → V)
    (observed : Finset K) :
    OutsideLabel C offset observed ≃ ShortOutsideLabels C offset ∅ 0 observed where
  toFun y := ⟨y.val, by
    obtain ⟨x, hx⟩ := y.property
    exact ⟨emptyFiberEquiv C offset x, hx⟩⟩
  invFun y := ⟨y.val, by
    obtain ⟨x, hx⟩ := y.property
    exact ⟨(emptyFiberEquiv C offset).symm x, hx⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem emptyLabelsEquiv_projection (C : AddSubgroup (K → V))
    (offset : K → V) (observed : Finset K) (x : AffineCode C offset) :
    shortOutside C offset ∅ 0 observed (emptyFiberEquiv C offset x) =
      emptyLabelsEquiv C offset observed (outsideProjection C offset observed x) := rfl

section TwoCodes
variable {J M 𝕜 : Type*} [Fintype J] [DecidableEq J] [Fintype M] [RCLike 𝕜]

theorem compressed_reindex
    (CL : AddSubgroup (K → V)) (CR : AddSubgroup (J → V))
    (offsetL : K → V) (offsetR : J → V) (observedL : Finset K) (observedR : Finset J)
    (middleL : M → K) (middleR : M → J) (T : M → V → V → 𝕜)
    (a b : ℕ) (y : OutsideLabel CL offsetL observedL) (x : OutsideLabel CR offsetR observedR) :
    compressedKernel (outsideProjection CL offsetL observedL)
      (outsideProjection CR offsetR observedR) a b
      (fun c d => ∏ m, T m (c.val (middleL m)) (d.val (middleR m))) y x =
    compressedKernel (shortOutside CL offsetL ∅ 0 observedL)
      (shortOutside CR offsetR ∅ 0 observedR) a b
      (fun c d => ∏ m, T m (c.val (middleL m)) (d.val (middleR m)))
      (emptyLabelsEquiv CL offsetL observedL y) (emptyLabelsEquiv CR offsetR observedR x) := by
  apply compressedKernel_reindex (emptyFiberEquiv CL offsetL) (emptyFiberEquiv CR offsetR)
    (emptyLabelsEquiv CL offsetL observedL) (emptyLabelsEquiv CR offsetR observedR)
  · intro c; rfl
  · intro d; rfl
  · intro c d; rfl

theorem compressed_norm_eq
    (CL : AddSubgroup (K → V)) (CR : AddSubgroup (J → V))
    (offsetL : K → V) (offsetR : J → V) (observedL : Finset K) (observedR : Finset J)
    (middleL : M → K) (middleR : M → J) (T : M → V → V → 𝕜) (a b : ℕ) :
    ‖kernelOperator (compressedKernel (outsideProjection CL offsetL observedL)
      (outsideProjection CR offsetR observedR) a b
      (fun c d => ∏ m, T m (c.val (middleL m)) (d.val (middleR m))))‖ =
    ‖kernelOperator (compressedKernel (shortOutside CL offsetL ∅ 0 observedL)
      (shortOutside CR offsetR ∅ 0 observedR) a b
      (fun c d => ∏ m, T m (c.val (middleL m)) (d.val (middleR m))))‖ := by
  have he := funext fun y => funext fun x =>
    compressed_reindex CL CR offsetL offsetR observedL observedR middleL middleR T a b y x
  rw [he]
  exact kernelOperator_reindex (emptyLabelsEquiv CR offsetR observedR)
    (emptyLabelsEquiv CL offsetL observedL) _

end TwoCodes
end AES8.PaperUnshortenedCode
