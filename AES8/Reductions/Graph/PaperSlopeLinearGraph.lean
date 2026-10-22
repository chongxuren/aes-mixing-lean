import AES8.Reductions.Graph.PaperSlopePhysicalFamily
import AES8.Math.PaperActivityInputAnalysis
import AES8.Math.PaperFramePartition
import AES8.Math.PaperActivityFrameJoin

/-! A literal linear diffusion graph and its unnormalized frame columns.
The graph-to-input equivalence is explicit, so changing from a graph sum to
an input sum introduces no q factor. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeLinearGraph
open AESMixing WordActivityFrame PaperActivityMinorTransport
open PaperActivityInputCoordinates PaperActivityInputAnalysis
open PaperSlopePhysicalContraction
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def inputPos (i : Fin 4) : Position := ⟨i.val,by omega⟩
def outputPos (i : Fin 4) : Position := ⟨4+i.val,by omega⟩

theorem outputPos_injective : Function.Injective outputPos := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp [outputPos] at hv
  omega

theorem input_ne_output (i j : Fin 4) : inputPos i ≠ outputPos j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [inputPos,outputPos] at hv
  omega

def positionsEquiv : (Fin 4 ⊕ Fin 4) ≃ Position where
  toFun := Sum.elim inputPos outputPos
  invFun i := if h : i.val < 4 then Sum.inl ⟨i.val,h⟩ else Sum.inr ⟨i.val-4,by omega⟩
  left_inv i := by
    cases i with
    | inl i => simp [inputPos]
    | inr i => simp [outputPos]
  right_inv i := by
    by_cases hi : i.val < 4
    · simp only [dif_pos hi,Sum.elim_inl]
      rfl
    · simp only [dif_neg hi,Sum.elim_inr]
      apply Fin.ext
      simp only [outputPos]
      omega

def graphWord (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) (x : Fin 4 → F) : Position → F :=
  fun i => if h : i.val < 4 then x ⟨i.val,h⟩ else L x ⟨i.val-4,by omega⟩

@[simp] theorem graphWord_input (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (x : Fin 4 → F) (i : Fin 4) : graphWord L x (inputPos i) = x i := by
  simp [graphWord,inputPos]

@[simp] theorem graphWord_output (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (x : Fin 4 → F) (i : Fin 4) : graphWord L x (outputPos i) = L x i := by
  simp [graphWord,outputPos]

def graphLinearMap (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) :
    (Fin 4 → F) →ₗ[F] (Position → F) where
  toFun := graphWord L
  map_add' x y := by
    funext i
    by_cases hi : i.val < 4 <;> simp [graphWord,hi,map_add]
  map_smul' t x := by
    funext i
    by_cases hi : i.val < 4 <;> simp [graphWord,hi,map_smul]

def graphCode (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) : Submodule F (Position → F) :=
  (graphLinearMap L).range

def graphEquiv (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F)) : (Fin 4 → F) ≃ graphCode L :=
  Equiv.ofBijective (graphLinearMap L).rangeRestrict ⟨by
    intro x y h
    funext i
    have he := congrArg (fun c : graphCode L => c.val (inputPos i)) h
    change graphWord L x (inputPos i) = graphWord L y (inputPos i) at he
    simpa only [graphWord_input] using he,
    by
      intro c
      obtain ⟨x,hx⟩ := c.property
      exact ⟨x,Subtype.ext hx⟩⟩

/-- A physical information-set proof for the graph word gives the original
code's MDS predicate, without changing coordinate labels. -/
theorem graph_isMDS_of_informationSets (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (hL : ∀ (s : Finset Position), s.card = 4 →
      Function.Bijective (fun x : Fin 4 → F => fun i : s => graphWord L x i.val)) :
    PaperMDSGram.IsMDS (graphCode L).toAddSubgroup 4 := by
  intro p hp
  let s : Finset Position := Finset.univ.filter p
  let ep : {i : Position // p i} ≃ s :=
    Equiv.subtypeEquivRight (fun i => by simp [s])
  have hs : s.card = 4 := by
    have hc := Fintype.card_congr ep
    have hp' : Fintype.card {i : Position // p i} = 4 := by
      simpa only [Nat.card_eq_fintype_card] using hp
    simpa only [Fintype.card_coe,hp'] using hc.symm
  have hb := hL s hs
  let e := graphEquiv L
  constructor
  · intro c d h
    apply e.symm.injective
    apply hb.injective
    funext i
    have hi : p i.val := (Finset.mem_filter.mp i.property).2
    have he := congrFun h (⟨i.val,hi⟩ : {i // p i})
    change c.val i.val = d.val i.val at he
    have hc : graphWord L (e.symm c) i.val = c.val i.val := by
      exact congrArg (fun v : graphCode L => v.val i.val) (e.apply_symm_apply c)
    have hd : graphWord L (e.symm d) i.val = d.val i.val := by
      exact congrArg (fun v : graphCode L => v.val i.val) (e.apply_symm_apply d)
    exact hc.trans (he.trans hd.symm)
  · intro v
    obtain ⟨x,hx⟩ := hb.surjective (fun i => v ⟨i.val,(Finset.mem_filter.mp i.property).2⟩)
    refine ⟨e x,?_⟩
    funext i
    change graphWord L x i.val = v i
    exact congrFun hx (⟨i.val,by simp [s,i.property]⟩ : s)

/-- An actual graph sum is exactly the original four-input sum. -/
theorem contraction_graph_sum (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (m₀ m₁ : Position) (U : Finset Position) (y : F × F) :
    contraction (graphCode L).toAddSubgroup m₀ m₁ U y =
      ∑ x : Fin 4 → F, R y.1 (graphWord L x m₀) * R y.2 (graphWord L x m₁) *
        (∏ i : U, wordFrame 0 true (graphWord L x i.val)) *
        ∏ i : zeroPositions m₀ m₁ U, wordFrame 0 false (graphWord L x i.val) := by
  unfold contraction
  exact ((graphEquiv L).sum_comp (fun c : graphCode L =>
    R y.1 (c.val m₀) * R y.2 (c.val m₁) *
      (∏ i : U, wordFrame 0 true (c.val i.val)) *
      ∏ i : zeroPositions m₀ m₁ U, wordFrame 0 false (c.val i.val))).symm

def diffusionColumn (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (a : Fin 4 → Bool) (x : Fin 4 → F) : ℝ := frameColumn 0 a (L.symm x)

/-- The partial analysis after the genuine degree projection is the
residual/frame graph sum of the actual diffused input frame column. -/
theorem partialAnalysis_diffusionColumn
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (S : Finset (Fin 4))
    (a : Fin 4 → Bool) (b : ↥(Sᶜ) → Bool) (y : S → F) :
    partialAnalysis 0 S
      (action (productProjection 0 (residualMask S)) (diffusionColumn L a)) b y =
      ∑ x : Fin 4 → F,
        analysis S (extend S b) y (L x) * frameColumn 0 a x := by
  rw [partialAnalysis_projected (PaperSlopeLineGram.card_gt_one (K := F))]
  unfold action
  rw [← L.toEquiv.sum_comp (fun x => analysis S (extend S b) y x * diffusionColumn L a x)]
  apply Finset.sum_congr rfl
  intro x _
  simp [diffusionColumn]

def pairOutputLabel (i₀ i₁ : Fin 4) (y : F × F) : ({i₀,i₁} : Finset (Fin 4)) → F :=
  fun i => if i.val = i₀ then y.1 else y.2

def inputFrame (U : Finset Position) (i : Fin 4) : Bool := decide (inputPos i ∈ U)
def outputFrame (U : Finset Position) (i : Fin 4) : Bool := decide (outputPos i ∈ U)

theorem residual_output_pair {i₀ i₁ : Fin 4} (hne : i₀ ≠ i₁)
    (y : F × F) (x : Fin 4 → F) :
    (∏ i : ({i₀,i₁} : Finset (Fin 4)), R (pairOutputLabel i₀ i₁ y i) (x i.val)) =
      R y.1 (x i₀) * R y.2 (x i₁) := by
  change (∏ i : ({i₀,i₁} : Finset (Fin 4)),
    R (if i.val = i₀ then y.1 else y.2) (x i.val)) = _
  rw [Finset.prod_coe_sort {i₀,i₁} (fun i : Fin 4 => R (if i = i₀ then y.1 else y.2) (x i))]
  simp [hne,Ne.symm hne]

theorem graph_frame_partition (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    (i₀ i₁ : Fin 4) (U : Finset Position)
    (hd : Disjoint (marks (outputPos i₀) (outputPos i₁)) U) (x : Fin 4 → F) :
    (∏ i : U, wordFrame 0 true (graphWord L x i.val)) *
      (∏ i : zeroPositions (outputPos i₀) (outputPos i₁) U,
        wordFrame 0 false (graphWord L x i.val)) =
      frameColumn 0 (inputFrame U) x *
        PaperActivityFrameJoin.outside {i₀,i₁} (outputFrame U) (L x) := by
  change (∏ i : U, wordFrame 0 true (graphWord L x i.val)) *
    (∏ i : ↥((marks (outputPos i₀) (outputPos i₁) ∪ U)ᶜ),
      wordFrame 0 false (graphWord L x i.val)) = _
  rw [PaperFramePartition.frame_partition _ _ hd (0 : F) (graphWord L x)]
  rw [← positionsEquiv.prod_comp (fun i : Position =>
    if i ∈ marks (outputPos i₀) (outputPos i₁) then (1 : ℝ)
    else wordFrame 0 (decide (i ∈ U)) (graphWord L x i))]
  rw [Fintype.prod_sum_type]
  apply congrArg₂ (· * ·)
  · unfold frameColumn
    apply Finset.prod_congr rfl
    intro i _
    simp only [positionsEquiv,Equiv.coe_fn_mk,Sum.elim_inl]
    simp [marks,input_ne_output,graphWord_input,inputFrame]
    rfl
  · unfold PaperActivityFrameJoin.outside
    apply Finset.prod_congr rfl
    intro i _
    simp only [positionsEquiv,Equiv.coe_fn_mk,Sum.elim_inr]
    simp only [marks,Finset.mem_insert,Finset.mem_singleton,
      outputPos_injective.eq_iff,graphWord_output,outputFrame]
    rfl

/-- Graph contraction equals analysis of a physical diffusion column. -/
theorem contraction_eq_graph_analysis (L : (Fin 4 → F) →ₗ[F] (Fin 4 → F))
    {i₀ i₁ : Fin 4} (hne : i₀ ≠ i₁) (U : Finset Position)
    (hd : Disjoint (marks (outputPos i₀) (outputPos i₁)) U) (y : F × F) :
    contraction (graphCode L).toAddSubgroup (outputPos i₀) (outputPos i₁) U y =
      ∑ x : Fin 4 → F, analysis {i₀,i₁} (outputFrame U) (pairOutputLabel i₀ i₁ y) (L x) *
        frameColumn 0 (inputFrame U) x := by
  rw [contraction_graph_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [graphWord_output,graphWord_output,PaperActivityFrameJoin.analysis_split,
    residual_output_pair hne]
  have h := graph_frame_partition L i₀ i₁ U hd x
  simp only [mul_assoc]
  rw [h]
  ring

/-- This is the bridge consumed by the exact inverse-output-frame energy. -/
theorem contraction_eq_partialAnalysis
    (L : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) {i₀ i₁ : Fin 4} (hne : i₀ ≠ i₁)
    (U : Finset Position) (hd : Disjoint (marks (outputPos i₀) (outputPos i₁)) U)
    (y : F × F) :
    contraction (graphCode L.toLinearMap).toAddSubgroup (outputPos i₀) (outputPos i₁) U y =
      partialAnalysis 0 {i₀,i₁}
        (action (productProjection 0 (residualMask {i₀,i₁}))
          (diffusionColumn L (inputFrame U)))
        (fun j => outputFrame U j.val) (pairOutputLabel i₀ i₁ y) := by
  rw [contraction_eq_graph_analysis _ hne U hd,partialAnalysis_diffusionColumn]
  apply Finset.sum_congr rfl
  intro x _
  apply congrArg (fun r : ℝ => r * frameColumn 0 (inputFrame U) x)
  unfold analysis
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ ({i₀,i₁} : Finset (Fin 4))
  · simp only [dif_pos hi]
    rfl
  · simp only [dif_neg hi,extend]
    rfl

end AES8.PaperSlopeLinearGraph
