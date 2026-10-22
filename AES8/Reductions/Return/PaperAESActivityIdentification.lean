import AES8.Math.PaperFramePartition
import AES8.Math.PaperActivityMinorTransport
import AES8.Reductions.Return.PaperAESFixedStepTransport
import AES8.Reductions.Support.TransferZeros

/-!
# Actual grouped-step activity contractions and the marked graph kernel

The canonical word graph has input on inl and output on inr; the marked
matrix enumerates output first. Both coordinate orders are implemented here.
No MDS-dimension hypothesis is used in the literal identification. Thus the
zero and full-image branches, including an empty retained side, are preserved.
Constructive proof work only; no attacks, searches, or manuscript changes.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityIdentification
open AESMixing PaperKernelBounds PaperFiberKernel
open PaperWordGraphCode PaperWordGraphDuality PaperAESFixedStepTransport
open PaperActivityMinorTransport
open AESConcrete.WordCrossZero AESConcrete.WordFourierVariants
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
local instance : DecidablePred (fun c : Position → AES.Word => c ∈ wordGraph) :=
  fun _ => Classical.propDecidable _

/-- Input/output physical marked positions, in canonical graph order. -/
def marked (O I : Finset (Fin 4)) : Finset Position := I.disjSum O

/-- Only omitted positions may supply a uniform frame leg. -/
def uniform (O I A B : Finset (Fin 4)) : Finset Position :=
  (B \ I).disjSum (A \ O)

/-- The matrix uses output first, while the physical graph uses input first. -/
def markedEquiv {i j : ℕ} (O I : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) : marked O I ≃ Fin i ⊕ Fin j where
  toFun p := match hp : p.val with
    | Sum.inl k => Sum.inr (ei ⟨k, by simpa [marked, hp] using p.property⟩)
    | Sum.inr k => Sum.inl (eo ⟨k, by simpa [marked, hp] using p.property⟩)
  invFun p := match p with
    | Sum.inl k => ⟨Sum.inr (eo.symm k).val, by simp [marked, (eo.symm k).property]⟩
    | Sum.inr k => ⟨Sum.inl (ei.symm k).val, by simp [marked, (ei.symm k).property]⟩
  left_inv p := by
    rcases p with ⟨p,hp⟩
    cases p with
    | inl k => simp
    | inr k => simp
  right_inv p := by
    cases p <;> simp

theorem marked_uniform_disjoint (O I A B : Finset (Fin 4)) :
    Disjoint (marked O I) (uniform O I A B) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  cases p <;> simp_all [marked, uniform]

def graphOutput {i j : ℕ} {M : Finset Position} (e : M ≃ Fin i ⊕ Fin j)
    (c : wordGraph) (k : Fin i) : AES.Word := c.val (e.symm (Sum.inl k)).val

def graphInput {i j : ℕ} {M : Finset Position} (e : M ≃ Fin i ⊕ Fin j)
    (c : wordGraph) (k : Fin j) : AES.Word := c.val (e.symm (Sum.inr k)).val

def graphWeight (M U : Finset Position) (c : wordGraph) : ℝ :=
  (∏ p : U, WordActivityFrame.wordFrame 0 true (c.val p.val)) *
    ∏ p : zeroPositions M U, WordActivityFrame.wordFrame 0 false (c.val p.val)

theorem graphEquiv_input (a : AES.WordState) (k : Fin 4) :
    (PaperRestrictedDiffusion.graphEquiv wordMixAddEquiv.toAddMonoidHom a).val
      (Sum.inl k) = a k := rfl

theorem graphEquiv_output (a : AES.WordState) (k : Fin 4) :
    (PaperRestrictedDiffusion.graphEquiv wordMixAddEquiv.toAddMonoidHom a).val
      (Sum.inr k) = wordMixAddEquiv a k := rfl

theorem marked_assignment_iff {i j : ℕ} (M : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (c : wordGraph)
    (a : Fin i → AES.Word) (b : Fin j → AES.Word) :
    (fun p : M => c.val p.val) = (fun p => Sum.elim a b (e p)) ↔
      a = graphOutput e c ∧ b = graphInput e c := by
  constructor
  · intro h
    constructor
    · funext k
      simpa only [Equiv.apply_symm_apply, Sum.elim_inl, graphOutput] using
        (congrFun h (e.symm (Sum.inl k))).symm
    · funext k
      simpa only [Equiv.apply_symm_apply, Sum.elim_inr, graphInput] using
        (congrFun h (e.symm (Sum.inr k))).symm
  · rintro ⟨rfl,rfl⟩
    funext p
    cases hp : e p with
    | inl k =>
      simp only [Sum.elim_inl, graphOutput]
      have he : e.symm (Sum.inl k) = p := by rw [← hp, e.symm_apply_apply]
      exact congrArg (fun a : M => c.val a.val) he.symm
    | inr k =>
      simp only [Sum.elim_inr, graphInput]
      have he : e.symm (Sum.inr k) = p := by rw [← hp, e.symm_apply_apply]
      exact congrArg (fun a : M => c.val a.val) he.symm

/-- Raw graph formula, before any strict shortening or coefficient theorem.
The right-hand residual projection has its required matrix orientation. -/
theorem physicalStep_graph_formula {i j : ℕ} (M U : Finset Position)
    (e : M ≃ Fin i ⊕ Fin j) (adjoint : Bool)
    (y : Fin i → AES.Word) (x : Fin j → AES.Word) :
    physicalStep M U e adjoint y x = ∑ c : wordGraph,
      R i adjoint y (graphOutput e c) * graphWeight M U c * P j (graphInput e c) x := by
  unfold physicalStep physicalGraph graphContraction
  simp only [kernelCompose, Finset.mul_sum, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin j → AES.Word)))
    (t := (Finset.univ : Finset wordGraph))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin i → AES.Word)))
    (t := (Finset.univ : Finset wordGraph))]
  apply Finset.sum_congr rfl
  intro c _
  simp only [marked_assignment_iff M e c]
  simp [graphWeight, ite_and, mul_ite, ite_mul, mul_assoc]

section FramePartition
variable {K V : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

/-- Write the literal outside frame product over all physical coordinates. -/
theorem frame_partition (M U : Finset K) (hd : Disjoint M U)
    (z : V) (c : K → V) :
    (∏ p : U, WordActivityFrame.wordFrame z true (c p.val)) *
      (∏ p : ↥((M ∪ U)ᶜ), WordActivityFrame.wordFrame z false (c p.val)) =
      ∏ p : K, if p ∈ M then 1 else
        WordActivityFrame.wordFrame z (decide (p ∈ U)) (c p) :=
  PaperFramePartition.frame_partition M U hd z c

end FramePartition

theorem graphWeight_physical (O I A B : Finset (Fin 4)) (c : wordGraph) :
    graphWeight (marked O I) (uniform O I A B) c =
      (∏ k : Fin 4, if k ∈ O then 1 else
        WordActivityFrame.wordFrame 0 (decide (k ∈ A)) (c.val (Sum.inr k))) *
      (∏ k : Fin 4, if k ∈ I then 1 else
        WordActivityFrame.wordFrame 0 (decide (k ∈ B)) (c.val (Sum.inl k))) := by
  change (∏ p : uniform O I A B, WordActivityFrame.wordFrame 0 true (c.val p.val)) *
    (∏ p : ↥(((marked O I) ∪ (uniform O I A B))ᶜ),
      WordActivityFrame.wordFrame 0 false (c.val p.val)) = _
  rw [frame_partition _ _ (marked_uniform_disjoint O I A B)]
  rw [Fintype.prod_sum_type]
  rw [mul_comm]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro k _
    by_cases h : k ∈ O <;> simp [marked, uniform, h]
  · apply Finset.prod_congr rfl
    intro k _
    by_cases h : k ∈ I <;> simp [marked, uniform, h]

/-- The actual ordinary or transposed superbox at every physical output.
The Boolean flag transposes H, not the diffusion or the complete step. -/
def channel (adjoint : Bool) : AES.Word → AES.Word → ℝ :=
  if adjoint then fun y x => AES.wordSuperboxKernel x y else AES.wordSuperboxKernel

theorem channel_pointed (adjoint : Bool) : PointedBistochastic (channel adjoint) 0 := by
  cases adjoint
  · exact AES.word_superbox_pointed
  · exact ⟨fun y x => AES.word_superbox_pointed.nonnegative x y,
      AES.word_superbox_pointed.zero_column, AES.word_superbox_pointed.zero_row,
      AES.word_superbox_pointed.row_sum, AES.word_superbox_pointed.column_sum⟩

theorem channel_residual (adjoint : Bool) : residualMatrix (channel adjoint) 0 = baseResidual adjoint := by
  cases adjoint
  · rfl
  · funext y x
    change AES.wordSuperboxKernel x y - activityMatrix (0 : AES.Word) y x =
      AES.wordSuperboxKernel x y - activityMatrix (0 : AES.Word) x y
    rw [activityMatrix_symmetric]

def actualStep (adjoint : Bool) (y x : AES.WordState) : ℝ :=
  coordinateKernel (fun _ : Fin 4 => channel adjoint) y (wordMixAddEquiv x)

theorem actualStep_ordinary : actualStep false = AESConcrete.WordStepZeros.wordStepKernel := rfl

/-- Actual retained-coordinate contraction, with outside normalized frames. -/
def contracted {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (adjoint : Bool)
    (y : Fin i → AES.Word) (x : Fin j → AES.Word) : ℝ :=
  kernelCompose (fun y => analysis O (fun k => decide (k ∈ A)) (fun p => y (eo p)))
    (kernelCompose (actualStep adjoint)
      (fun a x => synthesis I (fun k => decide (k ∈ B)) a (fun p => x (ei p)))) y x

theorem contracted_formula {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (adjoint : Bool)
    (y : Fin i → AES.Word) (x : Fin j → AES.Word) :
    contracted O I A B eo ei adjoint y x =
      ∑ a : AES.WordState,
        (∏ k : Fin 4, if h : k ∈ O then baseResidual adjoint (y (eo ⟨k,h⟩)) (wordMixAddEquiv a k)
          else WordActivityFrame.wordFrame 0 (decide (k ∈ A)) (wordMixAddEquiv a k)) *
        analysis I (fun k => decide (k ∈ B)) (fun p => x (ei p)) a := by
  unfold contracted
  rw [← compose_assoc]
  change (∑ a : AES.WordState,
    (∑ b : AES.WordState, analysis O (fun k => decide (k ∈ A))
      (fun p => y (eo p)) b * actualStep adjoint b a) *
        analysis I (fun k => decide (k ∈ B)) (fun p => x (ei p)) a) = _
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (fun v : ℝ => v *
    analysis I (fun k => decide (k ∈ B)) (fun p => x (ei p)) a)
  change kernelCompose (analysis O (fun k => decide (k ∈ A)))
      (coordinateKernel (fun _ : Fin 4 => channel adjoint)) (fun p => y (eo p))
        (wordMixAddEquiv a) = _
  rw [analysis_channel _ _ _ (fun _ => channel_pointed adjoint), channel_residual]

theorem product_retained {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (T : S → ℝ) (w : K → ℝ) :
    (∏ k : K, if h : k ∈ S then T ⟨k,h⟩ else w k) =
      (∏ k : S, T k) * (∏ k : K, if k ∈ S then 1 else w k) := by
  have hleft : (∏ k : K, if h : k ∈ S then T ⟨k,h⟩ else w k) =
      (∏ k : S, T k) * (∏ k : {k // k ∉ S}, w k.val) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => k ∈ S)]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr (by ext; simp)
      intro k _
      simp only [dif_pos k.property]
    · apply Finset.prod_congr (by ext; simp)
      intro k _
      simp only [dif_neg k.property]
  have hright : (∏ k : K, if k ∈ S then (1 : ℝ) else w k) =
      ∏ k : {k // k ∉ S}, w k.val := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun k => k ∈ S)]
    calc
      _ = 1 * (∏ k : {k // k ∉ S}, w k.val) := by
        apply congrArg₂ (· * ·)
        · apply Finset.prod_eq_one
          intro k _
          exact if_pos k.property
        · apply Finset.prod_congr (by ext; simp)
          intro k _
          exact if_neg k.property
      _ = _ := one_mul _
  rw [hleft, hright]

/-- Literal physical identity, with both coordinate permutations and no
normalizing scalar omitted. All zero/full-uniform choices are included. -/
theorem contracted_eq_physicalStep {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (adjoint : Bool) :
    contracted O I A B eo ei adjoint =
      physicalStep (marked O I) (uniform O I A B) (markedEquiv O I eo ei) adjoint := by
  funext y x
  rw [contracted_formula, physicalStep_graph_formula]
  rw [← (PaperRestrictedDiffusion.graphEquiv wordMixAddEquiv.toAddMonoidHom).sum_comp
    (fun c => R i adjoint y (graphOutput (markedEquiv O I eo ei) c) *
      graphWeight (marked O I) (uniform O I A B) c *
      P j (graphInput (markedEquiv O I eo ei) c) x)]
  apply Finset.sum_congr rfl
  intro a _
  rw [graphWeight_physical,
    product_retained O (fun p => baseResidual adjoint (y (eo p)) (wordMixAddEquiv a p.val))
      (fun k => WordActivityFrame.wordFrame 0 (decide (k ∈ A)) (wordMixAddEquiv a k)),
    analysis_product,
    product_retained I (fun p => residualProjection 0 (x (ei p)) (a p.val))
      (fun k => WordActivityFrame.wordFrame 0 (decide (k ∈ B)) (a k))]
  have hR : R i adjoint y
      (graphOutput (markedEquiv O I eo ei)
        (PaperRestrictedDiffusion.graphEquiv wordMixAddEquiv.toAddMonoidHom a)) =
      ∏ p : O, baseResidual adjoint (y (eo p)) (wordMixAddEquiv a p.val) := by
    change (∏ k : Fin i, baseResidual adjoint (y k)
      (wordMixAddEquiv a (eo.symm k).val)) = _
    simpa only [Equiv.symm_apply_apply] using
      (eo.prod_comp (fun k => baseResidual adjoint (y k)
        (wordMixAddEquiv a (eo.symm k).val))).symm
  have hP : P j
      (graphInput (markedEquiv O I eo ei)
        (PaperRestrictedDiffusion.graphEquiv wordMixAddEquiv.toAddMonoidHom a)) x =
      ∏ p : I, residualProjection (0 : AES.Word) (x (ei p)) (a p.val) := by
    have hs (k : Fin j) : residualProjection (0 : AES.Word)
        (a (ei.symm k).val) (x k) = residualProjection (0 : AES.Word)
        (x k) (a (ei.symm k).val) := degreePiece_symmetric 0 true _ _
    change (∏ k : Fin j, residualProjection (0 : AES.Word)
      (a (ei.symm k).val) (x k)) = _
    simp_rw [hs]
    simpa only [Equiv.symm_apply_apply] using
      (ei.prod_comp (fun k => residualProjection (0 : AES.Word)
        (x k) (a (ei.symm k).val))).symm
  rw [hR, hP]
  simp only [graphEquiv_input, graphEquiv_output]
  ring

/-- The ordinary channel is the actual grouped H Pi execution on every
signed joint input; the inverse law-transport direction is source-proved. -/
theorem actualStep_grouped (f : AES.WordState → ℝ) :
    action (actualStep false) f = AESPaper.GroupedRecurrence.step f := by
  rw [actualStep_ordinary]
  exact TransferZeros.physicalWordStep_eq_step f

/-- The contracted Hilbert adjoint reverses all three actual maps.
This is separate from transposing only the superbox flag. -/
theorem contracted_adjoint {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (adjoint : Bool) :
    (kernelOperator (contracted O I A B eo ei adjoint)).adjoint =
      kernelOperator (transpose
        (physicalStep (marked O I) (uniform O I A B) (markedEquiv O I eo ei) adjoint)) := by
  rw [contracted_eq_physicalStep, kernelOperator_adjoint]
  rfl

theorem contracted_zero_branch {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (adjoint : Bool) (hn : 0 < i+j)
    (hZ : 4 ≤ (zeroPositions (marked O I) (uniform O I A B)).card) :
    contracted O I A B eo ei adjoint = 0 := by
  rw [contracted_eq_physicalStep]
  exact physicalStep_zero_branch _ _ _ hn hZ adjoint

theorem contracted_full_branch {i j : ℕ} (O I A B : Finset (Fin 4))
    (eo : O ≃ Fin i) (ei : I ≃ Fin j) (adjoint : Bool) (hn : 0 < i+j)
    (hfull : (zeroPositions (marked O I) (uniform O I A B)).card +
      (marked O I).card ≤ 4) :
    contracted O I A B eo ei adjoint = 0 := by
  rw [contracted_eq_physicalStep]
  exact physicalStep_full_branch _ _ _ hn hfull adjoint

end AES8.PaperAESActivityIdentification
