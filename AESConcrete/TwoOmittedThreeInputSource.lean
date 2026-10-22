import AESConcrete.TwoOmittedThreeInputResponse

/-!
# Same-source output restrictions and exact (9,7) interfaces

Identity on physical input states transports the one-zero terms to INPUT-
WEIGHTED (9,7), and the double-zero term to its EXTRA-ZERO response. No (9,7)
actualResponse is substituted. All three original input uniforms stay inside
the same G, with literal J, E and arbitrary signed h including h(0). Geometry
and transports are separate from the following analytic aggregation.
Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedThreeInputSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedThreeInputGeometry
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

set_option maxRecDepth 100000

-- finite source proofs precede the local classical decision instance.
theorem complement_partition : ∀ E : Fin 16, maskSize E = 2 →
    ∀ a b : Fin 4, maskBit E a ≠ true → maskBit E b ≠ true → a ≠ b →
      ∀ i : Fin 4, maskBit (maskComplement E) i = true ↔ i = a ∨ i = b := by
  intro E hE a b ha hb hab i
  let t : Finset (Fin 4) :=
    Finset.univ.filter (fun j => maskBit (maskComplement E) j)
  have ht : t.card = 2 := by
    change maskSize (maskComplement E) = 2
    rw [maskComplement_size, hE]
  have ha' : a ∈ t := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ a, ?_⟩
    rw [maskComplement_bit, Bool.eq_false_of_not_eq_true ha]
    rfl
  have hb' : b ∈ t := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ b, ?_⟩
    rw [maskComplement_bit, Bool.eq_false_of_not_eq_true hb]
    rfl
  have hsub : ({a, b} : Finset (Fin 4)) ⊆ t := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact ha'
    · exact hb'
  have hpair : ({a, b} : Finset (Fin 4)) = t :=
    Finset.eq_of_subset_of_card_le hsub
      (le_of_eq (ht.trans (Finset.card_pair hab).symm))
  have hi : i ∈ t ↔ i = a ∨ i = b := by
    rw [← hpair]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using hi

attribute [local instance] Classical.propDecidable

abbrev Omitted (pOut : SelectedSupport 2 4) := OtherCoordinates pOut.val.val.1

theorem omitted_card (pOut : SelectedSupport 2 4) : Fintype.card (Omitted pOut) = 2 := by
  rw [GeneralMDSGraphSupport.otherCoordinates_card, retainedMask_size]

def omittedIndexEquiv (pOut : SelectedSupport 2 4) : Omitted pOut ≃ Fin 2 :=
  Fintype.equivOfCardEq (by rw [omitted_card]; simp)

def omittedFirst (pOut : SelectedSupport 2 4) : Omitted pOut :=
  (omittedIndexEquiv pOut).symm 0

def omittedSecond (pOut : SelectedSupport 2 4) : Omitted pOut :=
  (omittedIndexEquiv pOut).symm 1

theorem omittedFirst_ne_second (pOut : SelectedSupport 2 4) :
    omittedFirst pOut ≠ omittedSecond pOut :=
  (omittedIndexEquiv pOut).symm.injective.ne (by decide)

theorem omitted_labels_ne (pOut : SelectedSupport 2 4) :
    (omittedFirst pOut).val ≠ (omittedSecond pOut).val := by
  intro he
  exact omittedFirst_ne_second pOut (Subtype.ext he)

/-- Preserve literal E, adding only the specified original omitted zero. -/
def oneZero (pOut : SelectedSupport 2 4) (a : Omitted pOut) : SelectedSupport 2 3 :=
  ⟨⟨(pOut.val.val.1, singletonMask a.val), ⟨by
    intro i hi hE
    have he := (singletonMask_bit a.val i).mp hi
    subst i
    exact a.property hE, pOut.val.property.2⟩⟩, by rw [singletonMask_size]; decide⟩

theorem double_zero_partition (pOut : SelectedSupport 2 4) (i : Fin 4) :
    maskBit (OmittedUniformTwoOutputSplit.zeroCompletion
      (oneZero pOut (omittedFirst pOut))).val.val.2 i = true ↔
        i = (omittedFirst pOut).val ∨ i = (omittedSecond pOut).val :=
  complement_partition _ (retainedMask_size pOut) _ _
    (omittedFirst pOut).property (omittedSecond pOut).property (omitted_labels_ne pOut) i

def omittedValue (pOut : SelectedSupport 2 4) (a : Omitted pOut)
    (x : AES.WordState) : AES.Word := wordMixAddEquiv x a.val

def singleConditionalResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.zeroResponse (normalizedSource pIn h) (stateKernel pOut)
    (omittedValue pOut a)

def doubleConditionalResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  TripleResponse.intersectionResponse (normalizedSource pIn h) (stateKernel pOut)
    (omittedValue pOut (omittedFirst pOut)) (omittedValue pOut (omittedSecond pOut))

def oneZeroResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :=
  OmittedUniformTwoOutputSplit.inputWeightedResponse (oneZero pOut a) pIn h

def twoZeroResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  OmittedUniformTwoOutputSplit.extraZeroResponse (oneZero pOut (omittedFirst pOut)) pIn h

def singleRestrictionEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (a : Omitted pOut) :
    {x : AES.WordState // omittedValue pOut a x = 0} ≃
      OmittedUniformTwoOutputGeometry.Code (oneZero pOut a) pIn where
  toFun x := ⟨x.val, by
    constructor
    · intro i hi
      rw [(singletonMask_bit a.val i).mp hi]
      exact x.property
    · intro i hi
      exact (input_inactive_not pIn i hi).elim⟩
  invFun c := ⟨c.val, c.property.1 a.val ((singletonMask_bit _ _).mpr rfl)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem singleConditionalResponse_eq_oneZeroResponse
    (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4) (a : Omitted pOut)
    (h : (Residual pIn → AES.Word) → ℝ) :
    singleConditionalResponse pOut pIn a h = oneZeroResponse pOut pIn a h := by
  funext y
  unfold singleConditionalResponse WeightedResponse.zeroResponse oneZeroResponse
    OmittedUniformTwoOutputSplit.inputWeightedResponse
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (fun x : AES.WordState => omittedValue pOut a x = 0),
      normalizedSource pIn h x * stateKernel pOut y x) =
    ∑ x : {x : AES.WordState // omittedValue pOut a x = 0},
      normalizedSource pIn h x.val * stateKernel pOut y x.val from
        Finset.sum_subtype _ (by simp) _]
  exact (singleRestrictionEquiv pOut pIn a).sum_comp
    (fun c : OmittedUniformTwoOutputGeometry.Code (oneZero pOut a) pIn =>
      OmittedUniformTwoOutputSplit.normalizedSource pIn h c.val *
        OmittedUniformTwoOutputBareResponse.bareKernel (oneZero pOut a) pIn y c)

def doubleRestrictionEquiv (pOut : SelectedSupport 2 4) :
    {x : AES.WordState // omittedValue pOut (omittedFirst pOut) x = 0 ∧
      omittedValue pOut (omittedSecond pOut) x = 0} ≃
        TwoOutputThreeUniformGeometry.Plane (OmittedUniformTwoOutputSplit.zeroCompletion
          (oneZero pOut (omittedFirst pOut))) where
  toFun x := ⟨x.val, by
    constructor
    · intro i hi
      rcases (double_zero_partition pOut i).mp hi with he | he
      · rw [he]; exact x.property.1
      · rw [he]; exact x.property.2
    · intro i hi; exact (empty_mask_coordinate ⟨i, hi⟩).elim⟩
  invFun c := ⟨c.val, by
    constructor
    · exact c.property.1 _ ((double_zero_partition pOut _).mpr (Or.inl rfl))
    · exact c.property.1 _ ((double_zero_partition pOut _).mpr (Or.inr rfl))⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem doubleConditionalResponse_eq_twoZeroResponse
    (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    doubleConditionalResponse pOut pIn h = twoZeroResponse pOut pIn h := by
  funext y
  unfold doubleConditionalResponse TripleResponse.intersectionResponse twoZeroResponse
    OmittedUniformTwoOutputSplit.extraZeroResponse
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (fun x : AES.WordState =>
      omittedValue pOut (omittedFirst pOut) x = 0 ∧
      omittedValue pOut (omittedSecond pOut) x = 0),
        normalizedSource pIn h x * stateKernel pOut y x) =
    ∑ x : {x : AES.WordState // omittedValue pOut (omittedFirst pOut) x = 0 ∧
      omittedValue pOut (omittedSecond pOut) x = 0},
        normalizedSource pIn h x.val * stateKernel pOut y x.val from
          Finset.sum_subtype _ (by simp) _]
  exact (doubleRestrictionEquiv pOut).sum_comp
    (fun c : TwoOutputThreeUniformGeometry.Plane (OmittedUniformTwoOutputSplit.zeroCompletion
        (oneZero pOut (omittedFirst pOut))) =>
      OmittedUniformTwoOutputSplit.normalizedSource pIn h c.val *
        OmittedUniformTwoOutputSplit.stateKernel (oneZero pOut (omittedFirst pOut)) y c.val)

end AESConcrete.TwoOmittedThreeInputSource
