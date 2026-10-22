/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.FiberCollision
import AESMixing.MDSPrescribedCount
import AESPaper.ActivityKernel

/-!
# Collision sums for actual prescribed-coordinate MDS graph fibers

`AffineGraph L r z u v` is the explicit set of inputs whose output coordinates
in `r` equal `u` and whose input coordinates in `z` equal `v`.  Observations
select further output/input masks, disjoint from the fixed masks on each side.
The MDS graph count on their unions proves constant observation-fiber sizes
whenever the total number of fixed and observed coordinates is at most four.
At equality, subtraction and the existing MDS zero theorem prove an actual
information-set bijection.  Neither property is assumed as a new premise.

These yield both collision-sum branches for explicit selected information
masks.  In a larger observed set, selecting those masks and identifying the
remaining coordinates is a separate combinatorial application.  Projection
onto a marked marginal code, its incidence normalization, Fourier changes,
local AES moment bounds and operator estimates are not supplied here.

The final specialization uses the actual grouped AES boundary and its existing
MDS certificate.  Local functions remain arbitrary with explicit bounds.
Constructive proof work only; no attacks or predecessor/manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.MDSFiberCollision
open AESMixing AESMixing.AES

abbrev ObservedIndex (out inp : Fin 16) := MaskCoordinates out ⊕ MaskCoordinates inp

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

abbrev AffineGraph (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (u v : Fin 4 → V) :=
  {x : Fin 4 → V // graphPrescribed L r z u v x}

/-- Literal selected coordinates of the graph `(L x, x)`. -/
def observe (L : (Fin 4 → V) →+ (Fin 4 → V)) (out inp : Fin 16)
    (x : Fin 4 → V) : ObservedIndex out inp → V :=
  Sum.elim (fun i => L x i.val) (fun i => x i.val)

def projection (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z out inp : Fin 16)
    (u v : Fin 4 → V) (x : AffineGraph L r z u v) : ObservedIndex out inp → V :=
  observe L out inp x.val

/-- Combine fixed values with a new observation, without overwriting fixed positions. -/
def mergedTarget (fixed observed : Fin 16) (u : Fin 4 → V)
    (y : MaskCoordinates observed → V) (i : Fin 4) : V :=
  if hi : maskBit fixed i = true then u i else
    if hj : maskBit observed i = true then y ⟨i, hj⟩ else 0

theorem mergedTarget_fixed (fixed observed : Fin 16) (u : Fin 4 → V)
    (y : MaskCoordinates observed → V) (i : Fin 4) (hi : maskBit fixed i = true) :
    mergedTarget fixed observed u y i = u i := by
  simp [mergedTarget, hi]

theorem mergedTarget_observed (fixed observed : Fin 16) (hd : MaskDisjoint fixed observed)
    (u : Fin 4 → V) (y : MaskCoordinates observed → V) (i : MaskCoordinates observed) :
    mergedTarget fixed observed u y i.val = y i := by
  have hi : maskBit fixed i.val ≠ true := fun h => hd i.val h i.property
  simp [mergedTarget, hi, i.property]

private theorem prescribed_union_iff (fixed observed : Fin 16)
    (hd : MaskDisjoint fixed observed) (u : Fin 4 → V)
    (y : MaskCoordinates observed → V) (f : Fin 4 → V) :
    (∀ i, maskBit (maskUnion fixed observed) i = true →
      f i = mergedTarget fixed observed u y i) ↔
      (∀ i, maskBit fixed i = true → f i = u i) ∧
        (fun i : MaskCoordinates observed => f i.val) = y := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hu : maskBit (maskUnion fixed observed) i = true := by
        rw [maskUnion_bit, hi]
        simp
      simpa only [mergedTarget_fixed fixed observed u y i hi] using h i hu
    · funext i
      have hu : maskBit (maskUnion fixed observed) i.val = true := by
        rw [maskUnion_bit, i.property]
        simp
      simpa only [mergedTarget_observed fixed observed hd u y i] using h i.val hu
  · rintro ⟨hfixed, hobs⟩ i hi
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · rw [mergedTarget_fixed fixed observed u y i hi]
      exact hfixed i hi
    · rw [mergedTarget_observed fixed observed hd u y ⟨i, hi⟩]
      exact congrFun hobs ⟨i, hi⟩

/-- Combining prescribed and observed positions gives exactly one union-mask fiber. -/
theorem graph_union_iff_projection (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (y : ObservedIndex out inp → V) (x : Fin 4 → V) :
    graphPrescribed L (maskUnion r out) (maskUnion z inp)
      (mergedTarget r out u (fun i => y (Sum.inl i)))
      (mergedTarget z inp v (fun i => y (Sum.inr i))) x ↔
      graphPrescribed L r z u v x ∧ observe L out inp x = y := by
  unfold graphPrescribed
  rw [prescribed_union_iff r out hr u (fun i => y (Sum.inl i)) (L x),
    prescribed_union_iff z inp hz v (fun i => y (Sum.inr i)) x]
  constructor
  · rintro ⟨⟨ho, hyo⟩, ⟨hi, hyi⟩⟩
    refine ⟨⟨ho, hi⟩, ?_⟩
    funext p
    cases p with
    | inl i => exact congrFun hyo i
    | inr i => exact congrFun hyi i
  · rintro ⟨⟨ho, hi⟩, hobs⟩
    refine ⟨⟨ho, ?_⟩, ⟨hi, ?_⟩⟩
    · funext i
      exact congrFun hobs (Sum.inl i)
    · funext i
      exact congrFun hobs (Sum.inr i)

/-- The observation fiber is literally the graph with the union coordinates prescribed. -/
def projectionFiberEquiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (y : ObservedIndex out inp → V) :
    {x : AffineGraph L r z u v // projection L r z out inp u v x = y} ≃
      {x : Fin 4 → V // graphPrescribed L (maskUnion r out) (maskUnion z inp)
        (mergedTarget r out u (fun i => y (Sum.inl i)))
        (mergedTarget z inp v (fun i => y (Sum.inr i))) x} where
  toFun x := ⟨x.val.val,
    (graph_union_iff_projection L r z out inp u v hr hz y x.val.val).mpr
      ⟨x.val.property, x.property⟩⟩
  invFun x := ⟨⟨x.val,
    ((graph_union_iff_projection L r z out inp u v hr hz y x.val).mp x.property).1⟩,
    ((graph_union_iff_projection L r z out inp u v hr hz y x.val).mp x.property).2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

/-- Exact constant multiplicity; no equal-fiber premise is assumed. -/
theorem projection_fiber_card (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hle : maskSize r + maskSize z + maskSize out + maskSize inp ≤ 4)
    (y : ObservedIndex out inp → V) :
    Fintype.card {x : AffineGraph L r z u v // projection L r z out inp u v x = y} =
      Fintype.card V ^ (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)) := by
  have hu : maskSize (maskUnion r out) + maskSize (maskUnion z inp) ≤ 4 := by
    rw [maskUnion_size r out hr, maskUnion_size z inp hz]
    omega
  rw [Fintype.card_congr (projectionFiberEquiv L r z out inp u v hr hz y),
    mds_graph_prescribed_count_low L hL (maskUnion r out) (maskUnion z inp) hu,
    maskUnion_size r out hr, maskUnion_size z inp hz]
  congr 1
  omega

/-- Observing enough distinct remaining coordinates determines the affine graph point. -/
theorem projection_injective (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize out + maskSize inp = 4) :
    Function.Injective (projection L r z out inp u v) := by
  intro x y he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply mds_graph_zero_high L hL (maskUnion r out) (maskUnion z inp)
  · rw [maskUnion_size r out hr, maskUnion_size z inp hz]
    omega
  · constructor
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rw [map_sub]
      change L x.val i - L y.val i = 0
      apply sub_eq_zero.mpr
      rcases hi with hi | hi
      · rw [x.property.1 i hi, y.property.1 i hi]
      · exact congrFun he (Sum.inl ⟨i, hi⟩)
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      change x.val i - y.val i = 0
      apply sub_eq_zero.mpr
      rcases hi with hi | hi
      · rw [x.property.2 i hi, y.property.2 i hi]
      · exact congrFun he (Sum.inr ⟨i, hi⟩)

/-- The full selected information projection is bijective by injection and exact counts. -/
theorem projection_bijective (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize out + maskSize inp = 4) :
    Function.Bijective (projection L r z out inp u v) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨projection_injective L hL r z out inp u v hr hz hsize, ?_⟩
  have hbase : maskSize r + maskSize z ≤ 4 := by omega
  change Fintype.card {x : Fin 4 → V // graphPrescribed L r z u v x} =
    Fintype.card (ObservedIndex out inp → V)
  rw [mds_graph_prescribed_count_low L hL r z hbase u v, Fintype.card_fun,
    Fintype.card_sum, maskCoordinates_card, maskCoordinates_card]
  congr 1
  omega

def informationEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize out + maskSize inp = 4) :
    AffineGraph L r z u v ≃ (ObservedIndex out inp → V) :=
  Equiv.ofBijective (projection L r z out inp u v)
    (projection_bijective L hL r z out inp u v hr hz hsize)

/-- The constant-fiber collision branch on the exposed affine graph, with its count proved. -/
theorem affine_projection_sum_bound (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hle : maskSize r + maskSize z + maskSize out + maskSize inp ≤ 4)
    (g : ObservedIndex out inp → V → ℝ) (h : ℝ)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgsum : ∀ i, (∑ x, g i x) ≤ h) :
    (∑ x : AffineGraph L r z u v, ∏ i, g i (projection L r z out inp u v x i)) ≤
      (Fintype.card V : ℝ) ^ (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)) *
        h ^ (maskSize out + maskSize inp) := by
  have hb := FiberCollision.constant_fiber_projection_sum_bound
    (projection L r z out inp u v)
    (Fintype.card V ^ (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)))
    (projection_fiber_card L hL r z out inp u v hr hz hle) g h hg0 hgsum
  simpa only [Nat.cast_pow, Fintype.card_sum, maskCoordinates_card] using hb

/-- The information-set collision branch, with the information bijection derived from MDS. -/
theorem affine_information_set_sum_bound {J : Type*} [Fintype J]
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize out + maskSize inp = 4)
    (rest : AffineGraph L r z u v → J → V)
    (g : ObservedIndex out inp → V → ℝ) (f : J → V → ℝ) (h delta : ℝ)
    (hd : 0 ≤ delta) (hg0 : ∀ i x, 0 ≤ g i x) (hf0 : ∀ j x, 0 ≤ f j x)
    (hgsum : ∀ i, (∑ x, g i x) ≤ h) (hfcap : ∀ j x, f j x ≤ delta) :
    (∑ x : AffineGraph L r z u v,
      (∏ i, g i (projection L r z out inp u v x i)) * (∏ j, f j (rest x j))) ≤
      h ^ (maskSize out + maskSize inp) * delta ^ Fintype.card J := by
  have hb := FiberCollision.information_set_sum_bound
    (informationEquiv L hL r z out inp u v hr hz hsize) rest g f h delta
    hd hg0 hf0 hgsum hfcap
  -- Expose the equivalence's forward map, which is the literal projection.
  simpa only [informationEquiv, Equiv.ofBijective_apply,
    Fintype.card_sum, maskCoordinates_card] using hb

/-- Concrete specialization to the physical grouped AES boundary; no numerical local cap. -/
theorem aes_affine_projection_sum_bound (r z out inp : Fin 16)
    (u v : AES.WordState) (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hle : maskSize r + maskSize z + maskSize out + maskSize inp ≤ 4)
    (g : ObservedIndex out inp → AES.Word → ℝ) (h : ℝ)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgsum : ∀ i, (∑ x, g i x) ≤ h) :
    (∑ x : AffineGraph AESPaper.GroupedRecurrence.boundary.toAddMonoidHom r z u v,
      ∏ i, g i (projection AESPaper.GroupedRecurrence.boundary.toAddMonoidHom
        r z out inp u v x i)) ≤
      (Fintype.card AES.Word : ℝ) ^
          (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)) *
        h ^ (maskSize out + maskSize inp) :=
  affine_projection_sum_bound AESPaper.GroupedRecurrence.boundary.toAddMonoidHom
    AESPaper.ActivityKernel.aesBoundary_zeroMDS r z out inp u v hr hz hle g h hg0 hgsum

end AES8.MDSFiberCollision
