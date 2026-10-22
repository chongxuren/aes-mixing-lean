/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.MDSFiberIncidence

/-!
# Information coordinates on actual ordinary zero-fiber marked images

The attained three-coordinate middle image is not replaced by all triples.
Its restriction to two selected information coordinates is proved bijective
using the existing affine-graph `MDSFiberCollision.informationEquiv`.
Both input-middle and output-middle observations use the forward physical
AES boundary, with one prescribed zero on each graph side. The full graph
and each attained three-coordinate image therefore have dimension two,
and every attained image label has one graph preimage.

The last exact action identity identifies raw graph incidence on these
literal attained images as evaluation along the unique compatible graph
point. Inputs are arbitrary signed joint functions. No numerical resource,
target estimate, independence, or fiber-constancy premise is introduced.

This is one required component of the ordinary ell=3, mu=0 branch. It does
not identify an entire projected two-step kernel with InformationOverlap,
remove either centered step, expand the shared activity metric, or close
the (11,11) return cell.  Constructive proofs only; no attacks or source,
manuscript, or predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

namespace AES8.MarkedZeroFiber
open AESMixing AESMixing.AES
open AES8.MDSFiberCollision AES8.MDSFiberIncidence

/-- Inclusion of literal four-position masks, preserving the position label. -/
def MaskLE (small large : Fin 16) : Prop :=
  ∀ i : Fin 4, maskBit small i = true → maskBit large i = true

instance maskLEDecidable (small large : Fin 16) : Decidable (MaskLE small large) := by
  unfold MaskLE
  infer_instance

/-- The finite selection concerns four positions only, never AES values. -/
theorem three_has_two : ∀ middle : Fin 16, maskSize middle = 3 →
    ∃ info : Fin 16, maskSize info = 2 ∧ MaskLE info middle := by decide

def selectedPair (middle : Fin 16) (hthree : maskSize middle = 3) : Fin 16 :=
  Classical.choose (three_has_two middle hthree)

theorem selectedPair_size (middle : Fin 16) (hthree : maskSize middle = 3) :
    maskSize (selectedPair middle hthree) = 2 :=
  (Classical.choose_spec (three_has_two middle hthree)).1

theorem selectedPair_le (middle : Fin 16) (hthree : maskSize middle = 3) :
    MaskLE (selectedPair middle hthree) middle :=
  (Classical.choose_spec (three_has_two middle hthree)).2

private theorem zero_mask_size : maskSize (0 : Fin 16) = 0 := by decide
private theorem zero_mask_bit : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide

private theorem zero_le (large : Fin 16) : MaskLE 0 large := by
  intro i hi
  rw [zero_mask_bit] at hi
  contradiction

private theorem disjoint_zero (fixed : Fin 16) : MaskDisjoint fixed 0 := by
  intro i _ hi
  rw [zero_mask_bit] at hi
  contradiction

private theorem disjoint_of_le {fixed small large : Fin 16}
    (hd : MaskDisjoint fixed large) (hle : MaskLE small large) :
    MaskDisjoint fixed small := by
  intro i hi hs
  exact hd i hi (hle i hs)

section GenericImage
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
variable {out inp infoOut infoInp : Fin 16}

/-- The actual coordinate inclusion, with output/input tags retained. -/
def observedInclusion (hout : MaskLE infoOut out) (hinp : MaskLE infoInp inp) :
    ObservedIndex infoOut infoInp → ObservedIndex out inp
  | Sum.inl i => Sum.inl ⟨i.val, hout i.val i.property⟩
  | Sum.inr i => Sum.inr ⟨i.val, hinp i.val i.property⟩

def restrictObservation (hout : MaskLE infoOut out) (hinp : MaskLE infoInp inp)
    (y : ObservedIndex out inp → V) : ObservedIndex infoOut infoInp → V :=
  fun i => y (observedInclusion hout hinp i)

theorem restrict_projection
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) (u v : Fin 4 → V)
    (hout : MaskLE infoOut out) (hinp : MaskLE infoInp inp)
    (x : AffineGraph L r z u v) :
    restrictObservation hout hinp (projection L r z out inp u v x) =
      projection L r z infoOut infoInp u v x := by
  funext i
  cases i <;> rfl

/-- Restriction of the attained image to an information submask is an
equivalence. Its inverse reconstructs the graph point with the existing
information equivalence and then observes the full image. No full-tuple
surjectivity for the larger observation is asserted or required. -/
def informationImageEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp infoOut infoInp : Fin 16) (u v : Fin 4 → V)
    (hout : MaskLE infoOut out) (hinp : MaskLE infoInp inp)
    (hr : MaskDisjoint r infoOut) (hz : MaskDisjoint z infoInp)
    (hsize : maskSize r + maskSize z + maskSize infoOut + maskSize infoInp = 4) :
    AdmissibleImage L r z out inp u v ≃ (ObservedIndex infoOut infoInp → V) := by
  let e := informationEquiv L hL r z infoOut infoInp u v hr hz hsize
  refine
    { toFun := fun y => restrictObservation hout hinp y.val
      invFun := fun a => imageProjection L r z out inp u v (e.symm a)
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    obtain ⟨x, hx⟩ := y.property
    have hrestriction : restrictObservation hout hinp y.val = e x := by
      change restrictObservation hout hinp y.val =
        projection L r z infoOut infoInp u v x
      rw [← hx, restrict_projection]
    apply Subtype.ext
    change projection L r z out inp u v
      (e.symm (restrictObservation hout hinp y.val)) = y.val
    rw [hrestriction, e.symm_apply_apply]
    exact hx
  · intro a
    change restrictObservation hout hinp
      (projection L r z out inp u v (e.symm a)) = a
    rw [restrict_projection]
    exact e.apply_symm_apply a

@[simp] theorem informationImageEquiv_apply
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp infoOut infoInp : Fin 16) (u v : Fin 4 → V)
    (hout : MaskLE infoOut out) (hinp : MaskLE infoInp inp)
    (hr : MaskDisjoint r infoOut) (hz : MaskDisjoint z infoInp)
    (hsize : maskSize r + maskSize z + maskSize infoOut + maskSize infoInp = 4)
    (y : AdmissibleImage L r z out inp u v) :
    informationImageEquiv L hL r z out inp infoOut infoInp u v hout hinp hr hz hsize y =
      restrictObservation hout hinp y.val := rfl

/-- The equivalence is the selected literal graph observation, not merely
an unspecified bijection with a type of the same cardinality. -/
theorem informationImageEquiv_onGraph
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp infoOut infoInp : Fin 16) (u v : Fin 4 → V)
    (hout : MaskLE infoOut out) (hinp : MaskLE infoInp inp)
    (hr : MaskDisjoint r infoOut) (hz : MaskDisjoint z infoInp)
    (hsize : maskSize r + maskSize z + maskSize infoOut + maskSize infoInp = 4)
    (x : AffineGraph L r z u v) :
    informationImageEquiv L hL r z out inp infoOut infoInp u v hout hinp hr hz hsize
        (imageProjection L r z out inp u v x) =
      projection L r z infoOut infoInp u v x :=
  restrict_projection L r z u v hout hinp x

/-- Exact image reconstruction from selected information coordinates. -/
theorem informationImageEquiv_reconstruct
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp infoOut infoInp : Fin 16) (u v : Fin 4 → V)
    (hout : MaskLE infoOut out) (hinp : MaskLE infoInp inp)
    (hr : MaskDisjoint r infoOut) (hz : MaskDisjoint z infoInp)
    (hsize : maskSize r + maskSize z + maskSize infoOut + maskSize infoInp = 4)
    (x : AffineGraph L r z u v) :
    (informationImageEquiv L hL r z out inp infoOut infoInp u v
      hout hinp hr hz hsize).symm (projection L r z infoOut infoInp u v x) =
      imageProjection L r z out inp u v x := by
  let e := informationImageEquiv L hL r z out inp infoOut infoInp u v
    hout hinp hr hz hsize
  have hx : e (imageProjection L r z out inp u v x) =
      projection L r z infoOut infoInp u v x :=
    informationImageEquiv_onGraph L hL r z out inp infoOut infoInp u v
      hout hinp hr hz hsize x
  rw [← hx]
  exact e.symm_apply_apply _

/-- Counting-energy reindexing for arbitrary signed joint image inputs.
This is an equivalence, so it introduces no alphabet-size normalization. -/
theorem informationImage_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp infoOut infoInp : Fin 16) (u v : Fin 4 → V)
    (hout : MaskLE infoOut out) (hinp : MaskLE infoInp inp)
    (hr : MaskDisjoint r infoOut) (hz : MaskDisjoint z infoInp)
    (hsize : maskSize r + maskSize z + maskSize infoOut + maskSize infoInp = 4)
    (f : AdmissibleImage L r z out inp u v → ℝ) :
    (∑ a, f ((informationImageEquiv L hL r z out inp infoOut infoInp u v
      hout hinp hr hz hsize).symm a) ^ 2) = ∑ y, f y ^ 2 :=
  (informationImageEquiv L hL r z out inp infoOut infoInp u v
    hout hinp hr hz hsize).symm.sum_comp (fun y => f y ^ 2)

/-- When the full observation has at least four total fixed/observed
positions, the graph is exactly its attained image, with the projection
as forward map. This reuses the existing MDS injection theorem. -/
def graphImageEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hhigh : 4 ≤ maskSize r + maskSize z + maskSize out + maskSize inp) :
    AffineGraph L r z u v ≃ AdmissibleImage L r z out inp u v :=
  Equiv.ofBijective (imageProjection L r z out inp u v)
    ⟨imageProjection_injective_high L hL r z out inp u v hr hz hhigh,
      imageProjection_surjective L r z out inp u v⟩

end GenericImage

section ActualOrdinary

-- Orientation is fixed here: the ordinary forward physical boundary.
-- Input-middle images use (out,inp)=(0,middle); output-middle images use
-- (middle,0). Neither map is silently replaced by an inverse boundary.
abbrev boundary := AESPaper.GroupedRecurrence.boundary.toAddMonoidHom
abbrev ZeroGraph (r z : Fin 16) := AffineGraph boundary r z (0 : AES.WordState) 0
abbrev InputImage (r z middle : Fin 16) :=
  AdmissibleImage boundary r z 0 middle (0 : AES.WordState) 0
abbrev OutputImage (r z middle : Fin 16) :=
  AdmissibleImage boundary r z middle 0 (0 : AES.WordState) 0

theorem zeroGraph_constraints (r z : Fin 16) (x : ZeroGraph r z) :
    (∀ i, maskBit r i = true → AES.wordMix x.val i = 0) ∧
      (∀ i, maskBit z i = true → x.val i = 0) := by
  constructor
  · intro i hi
    rw [← AESPaper.BoundaryZeros.boundary_wordMix x.val]
    exact x.property.1 i hi
  · exact x.property.2

/-- Two selected input-middle positions label the actual attained image. -/
def inputInformationEquiv (r z middle info : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hi : maskSize info = 2) (hsub : MaskLE info middle)
    (hdis : MaskDisjoint z middle) :
    InputImage r z middle ≃ (ObservedIndex 0 info → AES.Word) :=
  informationImageEquiv boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
    r z 0 middle 0 info 0 0 (zero_le 0) hsub (disjoint_zero r)
    (disjoint_of_le hdis hsub) (by rw [hr, hz, zero_mask_size, hi])

/-- Two selected output-middle positions label the actual attained image. -/
def outputInformationEquiv (r z middle info : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hi : maskSize info = 2) (hsub : MaskLE info middle)
    (hdis : MaskDisjoint r middle) :
    OutputImage r z middle ≃ (ObservedIndex info 0 → AES.Word) :=
  informationImageEquiv boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
    r z middle 0 info 0 0 0 hsub (zero_le 0)
    (disjoint_of_le hdis hsub) (disjoint_zero z)
    (by rw [hr, hz, hi, zero_mask_size])

@[simp] theorem inputInformationEquiv_coordinate (r z middle info : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hi : maskSize info = 2) (hsub : MaskLE info middle)
    (hdis : MaskDisjoint z middle) (y : InputImage r z middle)
    (i : MaskCoordinates info) :
    inputInformationEquiv r z middle info hr hz hi hsub hdis y (Sum.inr i) =
      y.val (Sum.inr ⟨i.val, hsub i.val i.property⟩) := rfl

@[simp] theorem outputInformationEquiv_coordinate (r z middle info : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hi : maskSize info = 2) (hsub : MaskLE info middle)
    (hdis : MaskDisjoint r middle) (y : OutputImage r z middle)
    (i : MaskCoordinates info) :
    outputInformationEquiv r z middle info hr hz hi hsub hdis y (Sum.inl i) =
      y.val (Sum.inl ⟨i.val, hsub i.val i.property⟩) := rfl

/-- No information-set existence premise remains in this ell=3 wrapper. -/
def ordinaryInputInformationEquiv (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hthree : maskSize middle = 3) (hdis : MaskDisjoint z middle) :
    InputImage r z middle ≃ (ObservedIndex 0 (selectedPair middle hthree) → AES.Word) :=
  inputInformationEquiv r z middle (selectedPair middle hthree) hr hz
    (selectedPair_size middle hthree) (selectedPair_le middle hthree) hdis

def ordinaryOutputInformationEquiv (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hthree : maskSize middle = 3) (hdis : MaskDisjoint r middle) :
    OutputImage r z middle ≃ (ObservedIndex (selectedPair middle hthree) 0 → AES.Word) :=
  outputInformationEquiv r z middle (selectedPair middle hthree) hr hz
    (selectedPair_size middle hthree) (selectedPair_le middle hthree) hdis

theorem inputImage_fiber_one (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hthree : maskSize middle = 3) (hdis : MaskDisjoint z middle)
    (y : InputImage r z middle) :
    Fintype.card {x : ZeroGraph r z // imageProjection boundary r z 0 middle 0 0 x = y} = 1 :=
  imageProjection_fiber_card_high boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
    r z 0 middle 0 0 (disjoint_zero r) hdis
    (by rw [hr, hz, zero_mask_size, hthree]; decide) y

theorem outputImage_fiber_one (r z middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hthree : maskSize middle = 3) (hdis : MaskDisjoint r middle)
    (y : OutputImage r z middle) :
    Fintype.card {x : ZeroGraph r z // imageProjection boundary r z middle 0 0 0 x = y} = 1 :=
  imageProjection_fiber_card_high boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
    r z middle 0 0 0 hdis (disjoint_zero z)
    (by rw [hr, hz, hthree, zero_mask_size]; decide) y

/-- The outside observation of the ordinary zero-fiber graph is a genuine
bijection onto its attained image, with the literal projection forward. -/
def ordinaryOutsideEquiv (r z outside : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hthree : maskSize outside = 3) (hdis : MaskDisjoint r outside) :
    ZeroGraph r z ≃ OutputImage r z outside :=
  graphImageEquiv boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
    r z outside 0 0 0 hdis (disjoint_zero z)
    (by rw [hr, hz, hthree, zero_mask_size]; decide)

/-- Exact raw incidence action between literal outside and middle images.
For the ordinary zero-fiber branch the outside fiber has one graph point,
so its raw sum is evaluation at that point. All signed correlations in `f`
are retained. No ambient tuple is substituted for an attained image. -/
theorem ordinary_incidence_action (r z outside middle : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 1)
    (hthree : maskSize outside = 3) (hdis : MaskDisjoint r outside)
    (f : InputImage r z middle → ℝ) (y : OutputImage r z outside) :
    action (incidenceMultiplicity
      (imageProjection boundary r z outside 0 0 0)
      (imageProjection boundary r z 0 middle 0 0)) f y =
      f (imageProjection boundary r z 0 middle 0 0
        ((ordinaryOutsideEquiv r z outside hr hz hthree hdis).symm y)) := by
  let e := ordinaryOutsideEquiv r z outside hr hz hthree hdis
  rw [incidenceMultiplicity_action]
  rw [← e.symm.sum_comp (fun x : ZeroGraph r z =>
    if imageProjection boundary r z outside 0 0 0 x = y then
      f (imageProjection boundary r z 0 middle 0 0 x) else 0)]
  have he (w : OutputImage r z outside) :
      imageProjection boundary r z outside 0 0 0 (e.symm w) = w :=
    e.apply_symm_apply w
  simp_rw [he]
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true, e]

end ActualOrdinary
end AES8.MarkedZeroFiber
