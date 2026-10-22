import AESConcrete.ActivityMinorCounting
import AESConcrete.GeneralMDSGraphSupport

/-!
# Exact geometry of a signed singleton residual source

Candidate development only. This module identifies actual support, coordinates,
finite sums and counting energies. It contains no graph-energy inequality,
omitted-weight estimate, physical cap, inventory change or acceptance claim.
The source amplitude remains an arbitrary signed real function throughout;
it is never replaced by a normalized subgroup indicator.

Constructive mathematics only; no attacks. Independent retained uniform keys,
whitening, omitted final MixColumns, ordered-distinct pairs and fixed 10/14/16
remain unchanged. Compilation and independent review are separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.SingletonResidualGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ActivityCodeGeometry (wordCode mem_imageCode_iff)
open AESConcrete.ActivityMinor (selectedRetained)
open AESConcrete.ActivityMinorCounting (selectedRetained_card)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

section CodeCoordinate

/-- Every actual output coordinate is an information set of a size-one code. -/
theorem coordinate_bijective (U : Fin 16) (hU : maskSize U = 1) (k : Fin 4) :
    Function.Bijective (fun c : wordCode U => c.val k) := by
  have hb := ActivityCodeMoment.wordCode_projection_bijective U
    (fun _ : Fin 1 => k) (fun _ _ _ => Subsingleton.elim _ _)
    (by simpa only [Fintype.card_fin] using hU.symm)
  constructor
  · intro c d h
    apply hb.1
    funext i
    exact h
  · intro v
    obtain ⟨c, hc⟩ := hb.2 (fun _ => v)
    exact ⟨c, congrFun hc 0⟩

/-- Evaluation at the chosen physical coordinate, with no normalization. -/
def coordinateEquiv (U : Fin 16) (hU : maskSize U = 1) (k : Fin 4) :
    wordCode U ≃ AES.Word :=
  Equiv.ofBijective (fun c => c.val k) (coordinate_bijective U hU k)

@[simp]
theorem coordinateEquiv_apply (U : Fin 16) (hU : maskSize U = 1)
    (k : Fin 4) (c : wordCode U) : coordinateEquiv U hU k c = c.val k := rfl

/-- The unique actual codeword with the specified chosen output value. -/
def point (U : Fin 16) (hU : maskSize U = 1) (k : Fin 4) (v : AES.Word) :
    AES.WordState := ((coordinateEquiv U hU k).symm v).val

theorem point_mem (U : Fin 16) (hU : maskSize U = 1) (k : Fin 4) (v : AES.Word) :
    point U hU k v ∈ wordCode U := ((coordinateEquiv U hU k).symm v).property

@[simp]
theorem point_base (U : Fin 16) (hU : maskSize U = 1)
    (k : Fin 4) (v : AES.Word) : point U hU k v k = v := by
  change coordinateEquiv U hU k ((coordinateEquiv U hU k).symm v) = v
  exact (coordinateEquiv U hU k).apply_symm_apply v

theorem point_reconstruct (U : Fin 16) (hU : maskSize U = 1)
    (k : Fin 4) (c : wordCode U) : point U hU k (c.val k) = c.val := by
  exact congrArg Subtype.val ((coordinateEquiv U hU k).symm_apply_apply c)

/-- A single physical coordinate determines all four values on the code. -/
theorem coordinate_determines_state (U : Fin 16) (hU : maskSize U = 1)
    (k : Fin 4) (z z' : AES.WordState) (hz : z ∈ wordCode U)
    (hz' : z' ∈ wordCode U) (heq : z k = z' k) : z = z' := by
  have hc : (⟨z, hz⟩ : wordCode U) = ⟨z', hz'⟩ :=
    (coordinate_bijective U hU k).1 heq
  exact congrArg Subtype.val hc

theorem code_coordinate_zero_iff (U : Fin 16) (hU : maskSize U = 1)
    (i : Fin 4) (c : wordCode U) : c.val i = 0 ↔ c = 0 := by
  constructor
  · intro h
    exact (coordinate_bijective U hU i).1 h
  · rintro rfl
    rfl

@[simp]
theorem point_zero (U : Fin 16) (hU : maskSize U = 1) (k : Fin 4) :
    point U hU k 0 = 0 := by
  have h : (coordinateEquiv U hU k).symm 0 = (0 : wordCode U) := by
    apply (coordinateEquiv U hU k).injective
    rw [Equiv.apply_symm_apply]
    rfl
  exact congrArg Subtype.val h

/-- In particular, a nonzero code parameter has four nonzero physical words. -/
theorem point_coordinate_zero_iff (U : Fin 16) (hU : maskSize U = 1)
    (k i : Fin 4) (v : AES.Word) : point U hU k v i = 0 ↔ v = 0 := by
  constructor
  · intro hi
    have hc : (coordinateEquiv U hU k).symm v = (0 : wordCode U) :=
      (code_coordinate_zero_iff U hU i _).mp hi
    have hk := congrArg (fun c : wordCode U => c.val k) hc
    change point U hU k v k = 0 at hk
    simpa only [point_base] using hk
  · rintro rfl
    rw [point_zero]
    rfl

theorem point_all_nonzero (U : Fin 16) (hU : maskSize U = 1)
    (k : Fin 4) (v : AES.Word) (hv : v ≠ 0) :
    ∀ i : Fin 4, point U hU k v i ≠ 0 := by
  intro i hi
  exact hv ((point_coordinate_zero_iff U hU k i v).mp hi)

end CodeCoordinate

section SignedReindex

/-- Restrict the same signed function to its code parameter. -/
def amplitude (U : Fin 16) (hU : maskSize U = 1) (k : Fin 4)
    (F : AES.WordState → ℝ) (v : AES.Word) : ℝ := F (point U hU k v)

private theorem supported_sum (U : Fin 16) (F : AES.WordState → ℝ)
    (hF : ∀ z, F z ≠ 0 → z ∈ wordCode U) :
    (∑ z, F z) = ∑ c : wordCode U, F c.val := by
  calc
    _ = ∑ z, if z ∈ wordCode U then F z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ wordCode U
      · simp only [if_pos hz]
      · have hf : F z = 0 := by
          by_contra hf
          exact hz (hF z hf)
        simp only [if_neg hz, hf]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

/-- Exact rectangular-kernel action on an arbitrary signed supported source. -/
theorem supported_action_reindex {Y : Type*} (U : Fin 16)
    (hU : maskSize U = 1) (k : Fin 4) (F : AES.WordState → ℝ)
    (hF : ∀ z, F z ≠ 0 → z ∈ wordCode U)
    (K : Y → AES.WordState → ℝ) (y : Y) :
    action K F y = ∑ v, K y (point U hU k v) * amplitude U hU k F v := by
  unfold action
  rw [supported_sum U (fun z => K y z * F z) (by
    intro z hz
    apply hF z
    intro hf
    exact hz (by rw [hf, mul_zero]))]
  exact ((coordinateEquiv U hU k).symm.sum_comp
    (fun c : wordCode U => K y c.val * F c.val)).symm

/-- No code cardinality, fiber multiplicity or probability factor is present. -/
theorem supported_energy_reindex (U : Fin 16) (hU : maskSize U = 1)
    (k : Fin 4) (F : AES.WordState → ℝ)
    (hF : ∀ z, F z ≠ 0 → z ∈ wordCode U) :
    (∑ v, amplitude U hU k F v ^ 2) = ∑ z, F z ^ 2 := by
  calc
    _ = ∑ c : wordCode U, F c.val ^ 2 :=
      (coordinateEquiv U hU k).symm.sum_comp (fun c : wordCode U => F c.val ^ 2)
    _ = _ := (supported_sum U (fun z => F z ^ 2) (by
      intro z hz
      apply hF z
      intro hf
      exact hz (by rw [hf]; norm_num))).symm

end SignedReindex

section ActualSelectedInput

/-- The source's full active mask, not an assumed independent input tuple. -/
def activeMask (p : SelectedSupport 1 1) : Fin 16 := maskComplement p.val.val.2

theorem activeMask_size (p : SelectedSupport 1 1) : maskSize (activeMask p) = 1 := by
  unfold activeMask
  rw [maskComplement_size]
  have hp := p.property
  omega

/-- The actual selected source after physical word diffusion. -/
def selectedPullback (p : SelectedSupport 1 1) (f : AES.WordState → ℝ)
    (z : AES.WordState) : ℝ :=
  supportIndexComponent (0 : AES.Word) p.val f (wordMixAddEquiv.symm z)

theorem selectedPullback_supported (p : SelectedSupport 1 1)
    (f : AES.WordState → ℝ) :
    ∀ z, selectedPullback p f z ≠ 0 → z ∈ wordCode (activeMask p) := by
  intro z hz
  apply (mem_imageCode_iff wordMixAddEquiv (activeMask p) z).mpr
  exact GeneralMDSGraphSupport.supportIndexComponent_supported p.val f _ hz

theorem selectedPullback_coordinate_determines_state (p : SelectedSupport 1 1)
    (k : Fin 4) (f : AES.WordState → ℝ) (z z' : AES.WordState)
    (hz : selectedPullback p f z ≠ 0) (hz' : selectedPullback p f z' ≠ 0)
    (heq : z k = z' k) : z = z' :=
  coordinate_determines_state (activeMask p) (activeMask_size p) k z z'
    (selectedPullback_supported p f z hz) (selectedPullback_supported p f z' hz') heq

/-- The full nonzero support is on this fixed one-word graph for every sign of f. -/
theorem selectedPullback_on_graph (p : SelectedSupport 1 1) (k : Fin 4)
    (f : AES.WordState → ℝ) (z : AES.WordState) (hz : selectedPullback p f z ≠ 0) :
    point (activeMask p) (activeMask_size p) k (z k) = z :=
  point_reconstruct (activeMask p) (activeMask_size p) k
    ⟨z, selectedPullback_supported p f z hz⟩

/-- A nonzero original singleton source cannot give a zero physical output word. -/
theorem selectedSource_all_nonzero (p : SelectedSupport 1 1)
    (f : AES.WordState → ℝ) (x : AES.WordState)
    (hx : supportIndexComponent (0 : AES.Word) p.val f x ≠ 0) (hx0 : x ≠ 0) :
    ∀ i : Fin 4, wordMixAddEquiv x i ≠ 0 := by
  have hz : wordMixAddEquiv x ∈ wordCode (activeMask p) := by
    apply (mem_imageCode_iff wordMixAddEquiv (activeMask p) _).mpr
    simpa only [activeMask, wordMixAddEquiv.symm_apply_apply] using
      GeneralMDSGraphSupport.supportIndexComponent_supported p.val f x hx
  intro i hi
  have hc : (⟨wordMixAddEquiv x, hz⟩ : wordCode (activeMask p)) = 0 :=
    (code_coordinate_zero_iff (activeMask p) (activeMask_size p) i _).mp hi
  have he : wordMixAddEquiv x = wordMixAddEquiv 0 := by
    have hval := congrArg Subtype.val hc
    -- Expose the subgroup zero as the ambient word-state zero first.
    change wordMixAddEquiv x = (0 : AES.WordState) at hval
    simpa only [map_zero] using hval
  exact hx0 (wordMixAddEquiv.injective he)

/-- Finite permutation alone preserves the genuine selected source energy. -/
theorem selectedPullback_energy (p : SelectedSupport 1 1) (f : AES.WordState → ℝ) :
    (∑ z, selectedPullback p f z ^ 2) =
      ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2 :=
  wordMixAddEquiv.symm.toEquiv.sum_comp
    (fun x => supportIndexComponent (0 : AES.Word) p.val f x ^ 2)

/-- An actual marked residual factor vanishes at the all-zero source. -/
theorem selectedComponent_zero (p : SelectedSupport 1 1) (f : AES.WordState → ℝ) :
    supportIndexComponent (0 : AES.Word) p.val f 0 = 0 := by
  have hc : 0 < Fintype.card (MaskCoordinates p.val.val.1) := by
    rw [maskCoordinates_card, p.val.property.2]
    norm_num
  obtain ⟨k⟩ := Fintype.card_pos_iff.mp hc
  have hi : maskBit p.val.val.2 k.val ≠ true :=
    fun hi => p.val.property.1 k.val hi k.property
  have hfalse : maskBit p.val.val.2 k.val = false := Bool.eq_false_iff.mpr hi
  change (∑ x, supportProduct (0 : AES.Word) (maskBit p.val.val.1)
    (maskBit p.val.val.2) (0 : AES.WordState) x * f x) = 0
  apply Finset.sum_eq_zero
  intro x _
  have hk : supportProduct (0 : AES.Word) (maskBit p.val.val.1)
      (maskBit p.val.val.2) (0 : AES.WordState) x = 0 := by
    unfold supportProduct
    apply Finset.prod_eq_zero (Finset.mem_univ k.val)
    change supportPiece (0 : AES.Word) (maskBit p.val.val.1 k.val)
      (maskBit p.val.val.2 k.val) 0 (x k.val) = 0
    rw [hfalse]
    exact RefinedProjectionCompleteness.supportPiece_active_zero 0 (x k.val) _
  rw [hk, zero_mul]

@[simp]
theorem selectedPullback_zero (p : SelectedSupport 1 1)
    (f : AES.WordState → ℝ) : selectedPullback p f 0 = 0 := by
  simpa only [selectedPullback, map_zero] using selectedComponent_zero p f

def selectedAmplitude (p : SelectedSupport 1 1) (k : Fin 4)
    (f : AES.WordState → ℝ) : AES.Word → ℝ :=
  amplitude (activeMask p) (activeMask_size p) k (selectedPullback p f)

@[simp]
theorem selectedAmplitude_zero (p : SelectedSupport 1 1) (k : Fin 4)
    (f : AES.WordState → ℝ) : selectedAmplitude p k f 0 = 0 := by
  simp only [selectedAmplitude, amplitude, point_zero, selectedPullback_zero]

theorem selectedAmplitude_energy (p : SelectedSupport 1 1) (k : Fin 4)
    (f : AES.WordState → ℝ) :
    (∑ v, selectedAmplitude p k f v ^ 2) =
      ∑ x, supportIndexComponent (0 : AES.Word) p.val f x ^ 2 :=
  (supported_energy_reindex (activeMask p) (activeMask_size p) k
    (selectedPullback p f) (selectedPullback_supported p f)).trans
      (selectedPullback_energy p f)

theorem selected_action_reindex {Y : Type*} (p : SelectedSupport 1 1)
    (k : Fin 4) (f : AES.WordState → ℝ) (K : Y → AES.WordState → ℝ) (y : Y) :
    action K (selectedPullback p f) y =
      ∑ v, K y (point (activeMask p) (activeMask_size p) k v) *
        selectedAmplitude p k f v :=
  supported_action_reindex (activeMask p) (activeMask_size p) k
    (selectedPullback p f) (selectedPullback_supported p f) K y

end ActualSelectedInput

section RetainedOutputLabels

-- Editorial choice: choose a fixed enumeration of only the three physical
-- retained labels. The equivalences below keep this choice explicit everywhere.
def retainedLabels (p : SelectedSupport 3 4) :
    Fin 3 ≃ {i : Fin 4 // selectedRetained 3 4 p i} :=
  Fintype.equivOfCardEq (by rw [selectedRetained_card]; simp)

def retainedBase (p : SelectedSupport 3 4) : Fin 4 := (retainedLabels p 2).val

def retainedOutputEquiv (p : SelectedSupport 3 4) :
    ({i : Fin 4 // selectedRetained 3 4 p i} → AES.Word) ≃
      (AES.Word × AES.Word) × AES.Word where
  toFun y := ((y (retainedLabels p 0), y (retainedLabels p 1)), y (retainedLabels p 2))
  invFun y i := ![y.1.1, y.1.2, y.2] ((retainedLabels p).symm i)
  left_inv y := by
    funext i
    obtain ⟨j, rfl⟩ := (retainedLabels p).surjective i
    fin_cases j <;> simp
  right_inv y := by
    rcases y with ⟨⟨a, b⟩, c⟩
    simp

theorem retained_prod (p : SelectedSupport 3 4)
    (F : {i : Fin 4 // selectedRetained 3 4 p i} → ℝ) :
    (∏ i, F i) = F (retainedLabels p 0) * F (retainedLabels p 1) *
      F (retainedLabels p 2) := by
  rw [← (retainedLabels p).prod_comp F]
  simp [Fin.prod_univ_succ, mul_assoc]

theorem omitted_card (p : SelectedSupport 3 4) :
    Fintype.card {i : Fin 4 // ¬ selectedRetained 3 4 p i} = 1 := by
  rw [Fintype.card_subtype_compl, selectedRetained_card]
  norm_num

def omittedLabels (p : SelectedSupport 3 4) :
    Fin 1 ≃ {i : Fin 4 // ¬ selectedRetained 3 4 p i} :=
  Fintype.equivOfCardEq (by rw [omitted_card]; simp)

def omittedLabel (p : SelectedSupport 3 4) : Fin 4 := (omittedLabels p 0).val

theorem omittedLabel_not_retained (p : SelectedSupport 3 4) :
    ¬ selectedRetained 3 4 p (omittedLabel p) := (omittedLabels p 0).property

/-- Active count four leaves no pinned-zero output coordinate. -/
theorem selectedZeros_empty (p : SelectedSupport 3 4) :
    ∀ i : Fin 4, ¬ ActivityMinor.selectedZeros 3 4 p i := by
  intro i hi
  have hc : 0 < Fintype.card {j : Fin 4 // ActivityMinor.selectedZeros 3 4 p j} :=
    Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  rw [ActivityMinorCounting.selectedZeros_card] at hc
  norm_num at hc

theorem omitted_prod (p : SelectedSupport 3 4)
    (F : {i : Fin 4 // ¬ selectedRetained 3 4 p i} → ℝ) :
    (∏ i, F i) = F (omittedLabels p 0) := by
  rw [← (omittedLabels p).prod_comp F]
  simp

def retainedPairMap (p : SelectedSupport 3 4) (U : Fin 16) (hU : maskSize U = 1)
    (v : AES.Word) : AES.Word × AES.Word :=
  (point U hU (retainedBase p) v (retainedLabels p 0).val,
    point U hU (retainedBase p) v (retainedLabels p 1).val)

def omittedMap (p : SelectedSupport 3 4) (U : Fin 16) (hU : maskSize U = 1)
    (v : AES.Word) : AES.Word := point U hU (retainedBase p) v (omittedLabel p)

theorem point_retained_output (p : SelectedSupport 3 4) (U : Fin 16)
    (hU : maskSize U = 1) (v : AES.Word) :
    retainedOutputEquiv p (fun i => point U hU (retainedBase p) v i.val) =
      (retainedPairMap p U hU v, v) := by
  change ((_, _), point U hU (retainedBase p) v (retainedBase p)) = _
  rw [point_base]
  rfl

@[simp]
theorem omittedMap_zero (p : SelectedSupport 3 4) (U : Fin 16)
    (hU : maskSize U = 1) : omittedMap p U hU 0 = 0 := by
  simp only [omittedMap, point_zero, Pi.zero_apply]

theorem omittedMap_zero_iff (p : SelectedSupport 3 4) (U : Fin 16)
    (hU : maskSize U = 1) (v : AES.Word) : omittedMap p U hU v = 0 ↔ v = 0 :=
  point_coordinate_zero_iff U hU (retainedBase p) (omittedLabel p) v

end RetainedOutputLabels
end AESConcrete.SingletonResidualGeometry
