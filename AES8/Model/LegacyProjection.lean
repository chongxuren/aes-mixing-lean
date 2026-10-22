/- Module role: Concrete AES support definitions and coordinate/projection interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Model.SupportDegree
import AESConcrete.RefinedWordProjection
import AESConcrete.KernelOperator

/-!
# Exact bridge to the legacy refined projections

The fourteen raw-mask components use the same `(residual words, active words)`
table as the legacy physical projection system.  The table is stated locally
so this bridge needs only the existing vendored refined-kernel interface, not
the external physical-cap modules.  The equality below expands the legacy
`SupportIndex` sum into raw mask labels; overlap terms vanish by the already
proved raw projection identity.

The final statements identify the new counting `l2` profile with the ordinary
Euclidean norm of the legacy kernel operator on the same full word-state
space.  Inputs are arbitrary joint real functions.  No numerical cap, AES
transfer estimate, initialization estimate or mixing conclusion is supplied.
Constructive proof work only; no attacks or predecessor/manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace AES8.LegacyProjection
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.RefinedWordProjection
open AES8.SupportProfile

/-- The legacy physical order, copied as finite data rather than imported with caps. -/
def blockType : Fin 14 → Fin 5 × Fin 5 :=
  ![(0,1), (0,2), (0,3), (0,4), (1,1), (1,2), (1,3), (1,4),
    (2,2), (2,3), (2,4), (3,3), (3,4), (4,4)]

def residualIndex (i : Fin 14) : Fin 5 := (blockType i).1
def activeIndex (i : Fin 14) : Fin 5 := (blockType i).2

theorem residualIndex_val : ∀ i : Fin 14,
    (residualIndex i).val = SupportProfile.residualDegree i := by decide

theorem activeIndex_val : ∀ i : Fin 14,
    (activeIndex i).val = SupportProfile.supportSize i := by decide

theorem residualIndex_eq_degree (i : Fin 14) :
    residualIndex i = SupportDegree.degree i := by
  apply Fin.ext
  exact residualIndex_val i

private theorem valid_iff_disjoint : ∀ p : Label,
    Valid p ↔ MaskDisjoint p.2 p.1 := by decide

/-- The refined legacy action is exactly its selection of the two raw masks. -/
theorem refinedKernel_action_eq_raw (r k : Fin 5)
    (f : SupportProfile.State → ℝ) :
    action (refinedKernel (0 : AES.Word) r k) f = fun x =>
      ∑ p : Label,
        if maskSize p.1 = r.val ∧ 4 - maskSize p.2 = k.val
          then raw p f x else 0 := by
  funext x
  have ha : action (refinedKernel (0 : AES.Word) r k) f x =
      ∑ p : SupportIndex r.val,
        if maskSize p.val.2 + k.val = 4 then raw p.val f x else 0 := by
    unfold action refinedKernel
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : maskSize p.val.2 + k.val = 4
    · simp only [hp, if_true]
      rfl
    · simp only [hp, if_false, zero_mul, Finset.sum_const_zero]
  have hs :
      (∑ p : SupportIndex r.val,
        if maskSize p.val.2 + k.val = 4 then raw p.val f x else 0) =
      ∑ p : Label,
        if MaskDisjoint p.2 p.1 ∧ maskSize p.1 = r.val then
          (if maskSize p.2 + k.val = 4 then raw p f x else 0) else 0 := by
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [ha, hs]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : Valid p
  · have hd : MaskDisjoint p.2 p.1 := (valid_iff_disjoint p).mp hp
    have hm : maskSize p.2 ≤ 4 := maskSize_le_four p.2
    have hactive : maskSize p.2 + k.val = 4 ↔ 4 - maskSize p.2 = k.val := by omega
    simp only [hd, true_and, hactive]
    by_cases hr : maskSize p.1 = r.val <;> simp [hr]
  · simp [raw_invalid p hp f]

/-- Exact equality of the new component and the corresponding legacy refined action. -/
theorem component_eq_refinedKernel_action (f : SupportProfile.State → ℝ) (i : Fin 14) :
    SupportProfile.component f i =
      action (refinedKernel (0 : AES.Word) (residualIndex i) (activeIndex i)) f := by
  funext x
  rw [component_eq_support_residual]
  have h := congrFun (refinedKernel_action_eq_raw (residualIndex i) (activeIndex i) f) x
  simpa only [residualIndex_val, activeIndex_val] using h.symm

/-- Same kernel formula as the legacy physical projection system, in the same order. -/
def projectionKernel (i : Fin 14) : SupportProfile.State → SupportProfile.State → ℝ :=
  refinedKernel (0 : AES.Word) (residualIndex i) (activeIndex i)

theorem component_eq_projectionKernel_action (f : SupportProfile.State → ℝ)
    (i : Fin 14) :
    SupportProfile.component f i = action (projectionKernel i) f :=
  component_eq_refinedKernel_action f i

abbrev EuclideanState := EuclideanSpace ℝ SupportProfile.State

/-- The same finite coordinate function in the legacy Euclidean representation. -/
def toEuclidean (f : SupportProfile.State → ℝ) : EuclideanState := WithLp.toLp 2 f

@[simp] theorem toEuclidean_apply (f : SupportProfile.State → ℝ)
    (x : SupportProfile.State) : toEuclidean f x = f x := rfl

/-- Counting `l2` is the ordinary full-space Euclidean norm, with no size factor. -/
theorem l2_eq_euclidean_norm (f : EuclideanState) :
    AESMixing.l2 (fun x => f x) = ‖f‖ := by
  unfold AESMixing.l2
  rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

theorem l2_eq_toEuclidean_norm (f : SupportProfile.State → ℝ) :
    AESMixing.l2 f = ‖toEuclidean f‖ :=
  l2_eq_euclidean_norm (toEuclidean f)

/-- Continuous linear realization used by the legacy physical interfaces. -/
def euclideanProjection (i : Fin 14) : EuclideanState →L[ℝ] EuclideanState :=
  kernelOperator (projectionKernel i)

theorem euclideanProjection_apply (i : Fin 14) (f : EuclideanState)
    (x : SupportProfile.State) :
    euclideanProjection i f x = SupportProfile.component (fun y => f y) i x := by
  unfold euclideanProjection
  rw [kernelOperator_apply]
  exact congrFun (component_eq_projectionKernel_action (fun y => f y) i).symm x

theorem component_eq_euclideanProjection (f : EuclideanState) (i : Fin 14) :
    SupportProfile.component (fun y => f y) i = fun x => euclideanProjection i f x := by
  funext x
  exact (euclideanProjection_apply i f x).symm

/-- The new profile is exactly the Euclidean norm of the legacy refined projection. -/
theorem euclidean_profile_eq_norm (f : EuclideanState) (i : Fin 14) :
    SupportProfile.profile (fun x => f x) i = ‖euclideanProjection i f‖ := by
  unfold SupportProfile.profile
  rw [component_eq_euclideanProjection]
  exact l2_eq_euclidean_norm (euclideanProjection i f)

/-- Function-level profile bridge for arbitrary joint real inputs. -/
theorem profile_eq_euclidean_norm (f : SupportProfile.State → ℝ) (i : Fin 14) :
    SupportProfile.profile f i = ‖euclideanProjection i (toEuclidean f)‖ :=
  euclidean_profile_eq_norm (toEuclidean f) i

/-- The actual grouped error uses the same source and projection at index `j+1`. -/
theorem actual_eq_euclidean_norm (a : AES.State) (j : ℕ) (i : Fin 14) :
    SupportProfile.actual a j i =
      ‖euclideanProjection i (toEuclidean (AESPaper.GroupedLaw.error (j + 1) a))‖ :=
  profile_eq_euclidean_norm _ i

end AES8.LegacyProjection
