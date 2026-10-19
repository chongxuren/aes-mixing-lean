import AESPaper.ZeroEventMDS
import AESPaper.BiasTensorEnergy
import AESPaper.ActivityKernel
import AESPaper.BiasStartup

/-!
# Joint prescribed-zero events for the actual source law
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators
namespace AESPaper.ActualZeroEvents
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.ManySourceBounds (activeSourceMask activeSourceCount)

/-- A finite mask certificate, independent of AES values. -/
theorem inactive_mask_exists : ∀ a : Fin 4 → Bool, ∃ z : Fin 16,
    (∀ i, maskBit z i = !a i) ∧ maskSize z = 4-residualDegree a := by decide

theorem positive_mask_has_active : ∀ a : Fin 4 → Bool,
    0 < residualDegree a → ∃ i, a i = true := by decide

theorem set_mask_exists : ∀ D : Finset (Fin 4), ∃ r : Fin 16,
    (∀ i, maskBit r i = true ↔ i ∈ D) ∧ maskSize r = D.card := by decide

/-- The event mass in actual boundary coordinates, without conditioning. -/
def maskMass (b : AES.State) (r : Fin 16) : ℝ :=
  ∑ y : AES.WordState, if (∀ i, maskBit r i = true → y i=0)
    then BiasStartup.inputLaw b y else 0

theorem maskMass_source (b : AES.State) (r : Fin 16) :
    maskMass b r = ZeroEventMDS.eventMass GroupedRecurrence.boundary.toAddMonoidHom r
      (fun i => wordLaw (sourceInput b i)) := by
  let F : AES.WordState → ℝ := fun y =>
    if (∀ i, maskBit r i=true → y i=0) then BiasStartup.inputLaw b y else 0
  have he := Equiv.sum_comp GroupedRecurrence.boundary.toEquiv F
  change (∑ x, F (GroupedRecurrence.boundary x)) = maskMass b r at he
  rw [← he]
  unfold ZeroEventMDS.eventMass
  apply Finset.sum_congr rfl
  intro x _
  have hl : BiasStartup.inputLaw b (GroupedRecurrence.boundary x) =
      ∏ i, wordLaw (sourceInput b i) (x i) := by
    rw [BiasStartup.inputLaw, GroupedRecurrence.Pi_apply,
      AddEquiv.symm_apply_apply, StartingWord.grouped_initial_product]
  change (if (∀ i, maskBit r i=true → GroupedRecurrence.boundary x i=0)
    then BiasStartup.inputLaw b (GroupedRecurrence.boundary x) else 0) = _
  rw [hl]
  rfl

theorem source_product_nonnegative (b : AES.State) (x : AES.WordState) :
    0 ≤ ∏ i, wordLaw (sourceInput b i) (x i) :=
  Finset.prod_nonneg (fun i _ => StartingWord.wordLaw_nonnegative _ _)

theorem source_product_zero (b : AES.State) (hb : 0 < activeSourceCount b) :
    (∏ i, wordLaw (sourceInput b i) 0) = 0 := by
  obtain ⟨i,hi⟩ := positive_mask_has_active (activeSourceMask b) hb
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (StartingWord.wordLaw_zero _ ((ManySourceBounds.activeSourceMask_iff b i).mp hi))

/-- A source factor with inactive input can be nonzero only at zero. -/
theorem source_support (b : AES.State) (x : AES.WordState)
    (hx : (∏ i, wordLaw (sourceInput b i) (x i)) ≠ 0)
    (i : Fin 4) (hi : sourceInput b i = 0) : x i = 0 := by
  by_contra hne
  have hfactor : wordLaw (sourceInput b i) (x i) = 0 := by
    rw [hi, OneSourceLaw.wordLaw_zero_input, if_neg hne]
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hfactor)

/-- Too many prescribed output zeros force the zero source tuple. -/
theorem maskMass_eq_zero (b : AES.State) (hb : 0 < activeSourceCount b)
    (r : Fin 16) (hr : activeSourceCount b ≤ maskSize r) : maskMass b r = 0 := by
  rw [maskMass_source]
  unfold ZeroEventMDS.eventMass
  apply Finset.sum_eq_zero
  intro x _
  by_cases hout : ZeroEventMDS.outputZero GroupedRecurrence.boundary.toAddMonoidHom r x
  · rw [if_pos hout]
    by_contra hx
    obtain ⟨z,hz,hsize⟩ := inactive_mask_exists (activeSourceMask b)
    have hbound := residualDegree_le (activeSourceMask b)
    have hcount : 4 ≤ maskSize r+maskSize z := by
      change activeSourceCount b ≤ 4 at hbound
      change maskSize z = 4-activeSourceCount b at hsize
      omega
    have hinput : ∀ i, maskBit z i=true → x i=0 := by
      intro i hi
      have ha : activeSourceMask b i = false := by
        have hnot : Bool.not (activeSourceMask b i) = true := (hz i).symm.trans hi
        cases hm : activeSourceMask b i
        · rfl
        · simp only [hm, Bool.not_true, Bool.false_eq_true] at hnot
      have hs : sourceInput b i = 0 := by
        simpa only [activeSourceMask, decide_eq_false_iff_not, not_not] using ha
      exact source_support b x hx i hs
    have hzero := mds_graph_zero_high GroupedRecurrence.boundary.toAddMonoidHom
      ActivityKernel.aesBoundary_zeroMDS r z hcount x ⟨hout,hinput⟩
    have hp := congrArg (fun v : AES.WordState =>
      ∏ i, wordLaw (sourceInput b i) (v i)) hzero
    exact hx (hp.trans (source_product_zero b hb))
  · rw [if_neg hout]

/-- Select only active source factors for the pointwise cap. -/
theorem maskMass_le_of_le (b : AES.State) (r : Fin 16)
    (hr : maskSize r ≤ activeSourceCount b) :
    maskMass b r ≤ (20/q)^maskSize r := by
  obtain ⟨z,hz,hsize⟩ := inactive_mask_exists (activeSourceMask b)
  have hbound := residualDegree_le (activeSourceMask b)
  have hcount : maskSize r+maskSize z ≤ 4 := by
    change activeSourceCount b ≤ 4 at hbound
    change maskSize z = 4-activeSourceCount b at hsize
    omega
  obtain ⟨c,hc,hdis⟩ := low_mask_extension r z hcount
  have hcap : ∀ i, maskBit c i=true → ∀ x,
      wordLaw (sourceInput b i) x ≤ 20/q := by
    intro i hi x
    have ha : activeSourceMask b i = true := by
      by_contra ha
      have hfalse : activeSourceMask b i = false := by
        cases hm : activeSourceMask b i
        · rfl
        · exact False.elim (ha hm)
      have hztrue : maskBit z i = true := by
        rw [hz i, hfalse]
        rfl
      exact hdis i hztrue hi
    have he := StartingWord.wordLaw_abs_point_lt (sourceInput b i) x
      ((ManySourceBounds.activeSourceMask_iff b i).mp ha)
    exact (le_abs_self _).trans he.le
  rw [maskMass_source]
  exact ZeroEventMDS.eventMass_le GroupedRecurrence.boundary.toAddMonoidHom
    ActivityKernel.aesBoundary_zeroMDS r c hc (fun i => wordLaw (sourceInput b i))
    (20/q) (by norm_num [q]) (fun i x => StartingWord.wordLaw_nonnegative _ _)
    (fun i => StartingWord.wordLaw_total _) hcap

theorem maskMass_le (b : AES.State) (hb : 0 < activeSourceCount b) (r : Fin 16) :
    maskMass b r ≤ (20/q)^maskSize r := by
  by_cases hr : maskSize r ≤ activeSourceCount b
  · exact maskMass_le_of_le b r hr
  · rw [maskMass_eq_zero b hb r (Nat.le_of_lt (Nat.lt_of_not_ge hr))]
    exact pow_nonneg (by norm_num [q]) _

/-- The shared joint-event definition; its mass is not divided out. -/
def zeroMass (g : AES.WordState → ℝ) (D : Finset (Fin 4)) : ℝ :=
  BiasTensorEnergy.jointZeroMass (0 : AES.Word) g D

theorem zeroMass_mask (b : AES.State) (D : Finset (Fin 4)) (r : Fin 16)
    (hr : ∀ i, maskBit r i=true ↔ i∈D) :
    zeroMass (BiasStartup.inputLaw b) D = maskMass b r := by
  unfold zeroMass BiasTensorEnergy.jointZeroMass maskMass
  apply Finset.sum_congr rfl
  intro x _
  have he : (∀ i∈D, x i=0) ↔ (∀ i, maskBit r i=true → x i=0) := by
    constructor
    · intro h i hi; exact h i ((hr i).mp hi)
    · intro h i hi; exact h i ((hr i).mpr hi)
  by_cases hz : ∀ i∈D, x i=0
  · simp only [if_pos hz, if_pos (he.mp hz)]
  · have hn : ¬ (∀ i, maskBit r i=true → x i=0) := fun h => hz (he.mpr h)
    simp only [if_neg hz, if_neg hn]

theorem actual_zeroMass_le (b : AES.State) (hb : 0 < activeSourceCount b)
    (D : Finset (Fin 4)) :
    zeroMass (BiasStartup.inputLaw b) D ≤ (20/q)^D.card := by
  obtain ⟨r,hr,hsize⟩ := set_mask_exists D
  rw [zeroMass_mask b D r hr, ← hsize]
  exact maskMass_le b hb r

theorem actual_zeroMass_eq_zero (b : AES.State) (hb : 0 < activeSourceCount b)
    (D : Finset (Fin 4)) (hD : activeSourceCount b ≤ D.card) :
    zeroMass (BiasStartup.inputLaw b) D = 0 := by
  obtain ⟨r,hr,hsize⟩ := set_mask_exists D
  rw [zeroMass_mask b D r hr]
  exact maskMass_eq_zero b hb r (hsize.symm ▸ hD)

end AESPaper.ActualZeroEvents
