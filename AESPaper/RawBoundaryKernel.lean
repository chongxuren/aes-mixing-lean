import AESPaper.WordPhysicalActivity
import AESPaper.UniformBias

/-!
# Exact raw boundary graph and activity-frame interfaces

The raw kernel is the actual Pi permutation operator. Its common graph
point is (boundary x,x), while law transport evaluates the old function at
the inverse boundary. Marked output legs are residual projections; marked
input legs retain their literal transpose. Frame analysis introduces one
divisor 65536^uniformCount, and the assembly includes both frame factors.
No numerical C/t cap, q^2 scaling, physical symmetry or independence premise
is asserted. All activity and shortening formulas use the word alphabet.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RawBoundaryKernel
open AESMixing AESConcrete
open AESPaper.GroupedRecurrence
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros
  rawResponse sourceCoordinates)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordActivitySplit (OutputActivity InputActivity)
open AESPaper.WordPhysicalActivity (outputSource inputSource)
open AESPaper.WordFrameCoordinates (projectActivity tensorActivityKernel)
open AESPaper.RectangularFourier (EnergyBound)
-- Use the same decidable instances as ProfileSpace and the generic degree projections.

/-- Actual forward boundary transport, with identity channels on both sides. -/
def rawKernel : AES.WordState → AES.WordState → ℝ :=
  WordGraphKernel.transportKernel boundary.toEquiv identityKernel identityKernel

theorem rawKernel_action (f : AES.WordState → ℝ) : action rawKernel f = Pi f := by
  have h := WordGraphKernel.transportKernel_action_relabel boundary.toEquiv
    (identityKernel : AES.WordState → AES.WordState → ℝ) identityKernel f
  change action (WordGraphKernel.transportKernel boundary.toEquiv identityKernel identityKernel) f =
    lawRelabel boundary.toEquiv f
  simpa only [identityKernel_action] using h

/-- The kernel uses the forward graph, consistently with inverse transport
of functions in rawKernel_action. -/
theorem rawKernel_graph (y x : AES.WordState) :
    rawKernel y x = identityKernel y (boundary x) := by
  simp only [rawKernel, WordGraphKernel.transportKernel, UniformBias.compose_identity]
  rfl

theorem boundaryLayer_eq_action (f : ProfileSpace.State) (x : AES.WordState) :
    BoundaryContraction.boundaryLayer f x = action rawKernel (fun y => f y) x := by
  exact (BoundaryContraction.boundaryLayer_apply f x).trans
    (congrFun (rawKernel_action (fun y => f y)) x).symm

/-- Actual two-sided product-position block of Pi, without word channels. -/
def markedKernel (out inp : Fin 4 → Bool) : AES.WordState → AES.WordState → ℝ :=
  kernelCompose (productProjection (0 : AES.Word) out)
    (kernelCompose rawKernel (productProjection (0 : AES.Word) inp))

theorem markedKernel_action (out inp : Fin 4 → Bool) (f : AES.WordState → ℝ) :
    action (markedKernel out inp) f =
      action (productProjection (0 : AES.Word) out)
        (Pi (action (productProjection (0 : AES.Word) inp) f)) := by
  simp only [markedKernel, kernelCompose_action, rawKernel_action]

/-- Identity channels turn their residual matrices into the raw projections. -/
theorem residualMatrix_identity :
    residualMatrix (identityKernel : AES.Word → AES.Word → ℝ) 0 =
      residualProjection (0 : AES.Word) := by
  funext y x
  rfl

theorem channelPiece_identity (b : Bool) :
    WordGraphKernel.channelPiece (identityKernel : AES.Word → AES.Word → ℝ) b =
      degreePiece (0 : AES.Word) b := by
  cases b <;> rfl

theorem markedKernel_piece_kernel (out inp : Fin 4 → Bool) :
    markedKernel out inp = WordGraphKernel.transportKernel boundary.toEquiv
      (coordinateKernel (fun i => degreePiece (0 : AES.Word) (out i)))
      (coordinateKernel (fun i => degreePiece (0 : AES.Word) (inp i))) := by
  simp only [markedKernel, rawKernel, WordGraphKernel.transportKernel_two_sided,
    UniformBias.compose_identity, UniformBias.identity_compose,
    productProjection, coordinateKernel]
  rfl

/-- All physical graph coordinates keep the same source x. -/
theorem markedKernel_graph (out inp : Fin 4 → Bool) (y a : AES.WordState) :
    markedKernel out inp y a = ∑ x : AES.WordState,
      (∏ i : Fin 4, degreePiece (0 : AES.Word) (out i) (y i) (boundary x i)) *
        ∏ i : Fin 4, degreePiece (0 : AES.Word) (inp i) (x i) (a i) := by
  rw [markedKernel_piece_kernel]
  exact WordGraphKernel.coordinate_transportKernel boundary.toEquiv
    (fun i => degreePiece (0 : AES.Word) (out i))
    (fun i => degreePiece (0 : AES.Word) (inp i)) y a

/-- Output residuals keep their orientation; input residuals are transposed
literally, without using symmetry to alter the physical specification. -/
def rawMarkedLeg (m : GraphPosition → Bool) (p : Marked m) : AES.Word → AES.Word → ℝ :=
  Sum.elim (fun _ y x => residualProjection (0 : AES.Word) y x)
    (fun _ y x => residualProjection (0 : AES.Word) x y) p.val

theorem rawMarkedLeg_output (m : GraphPosition → Bool) (i : OutputMarked m)
    (y x : AES.Word) :
    rawMarkedLeg m (WordMarkedSplit.outputPosition m i) y x =
      residualProjection (0 : AES.Word) y x := rfl

theorem rawMarkedLeg_input (m : GraphPosition → Bool) (i : InputMarked m)
    (y x : AES.Word) :
    rawMarkedLeg m (WordMarkedSplit.inputPosition m i) y x =
      residualProjection (0 : AES.Word) x y := rfl

/-- The accepted generic vectorization applies with identity one-word channels. -/
theorem rawMarkedLeg_eq_identity_markedLeg (m : GraphPosition → Bool) :
    rawMarkedLeg m = WordGraphKernel.markedLeg
      (fun _ : Fin 4 => (identityKernel : AES.Word → AES.Word → ℝ))
      (fun _ : Fin 4 => (identityKernel : AES.Word → AES.Word → ℝ)) m := by
  funext p y x
  rcases p with ⟨p,hp⟩
  cases p <;> rfl

def vectorizedResponse (m : GraphPosition → Bool) : (GraphPosition → AES.Word) → ℝ :=
  MarkedBlockVectorization.fullResponse m (rawMarkedLeg m)
    (graphCoordinate boundary.toAddMonoidHom)

theorem vectorizedResponse_matrix (m : GraphPosition → Bool) (y a : AES.WordState) :
    vectorizedResponse m (Sum.elim y a) =
      markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)) y a := by
  rw [markedKernel_piece_kernel]
  have h := WordGraphKernel.vectorizedResponse_matrix
    (fun _ : Fin 4 => (identityKernel : AES.Word → AES.Word → ℝ))
    (fun _ : Fin 4 => (identityKernel : AES.Word → AES.Word → ℝ)) boundary.toEquiv m y a
  have hc : (graphCoordinate boundary.toAddMonoidHom :
      AES.WordState → GraphPosition → AES.Word) =
      (fun x : AES.WordState => Sum.elim (boundary.toEquiv x) x) := by
    funext x p
    cases p <;> rfl
  unfold vectorizedResponse
  rw [rawMarkedLeg_eq_identity_markedLeg, hc]
  simpa only [WordGraphKernel.vectorizedResponse, channelPiece_identity] using h

theorem vectorizedResponse_join (m : GraphPosition → Bool)
    (y : Marked m → AES.Word) (v : Activity m → AES.Word) :
    vectorizedResponse m (MarkedBlockVectorization.join m y v) =
      MarkedBlockVectorization.splitResponse m (rawMarkedLeg m)
        (graphCoordinate boundary.toAddMonoidHom) y v :=
  MarkedBlockVectorization.fullResponse_join m (rawMarkedLeg m)
    (graphCoordinate boundary.toAddMonoidHom) y v

theorem markedKernel_hilbertSchmidt_square (m : GraphPosition → Bool) :
    (∑ y : AES.WordState, ∑ a : AES.WordState,
      markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)) y a ^ 2) =
      ∑ v : GraphPosition → AES.Word, vectorizedResponse m v ^ 2 := by
  rw [← (Equiv.sumArrowEquivProdArrow (Fin 4) (Fin 4) AES.Word).symm.sum_comp
    (fun v => vectorizedResponse m v ^ 2), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun z : ℝ => z ^ 2) (vectorizedResponse_matrix m y a).symm

/-- Word-frame analysis of raw marked legs, before canonical inverse Grams. -/
def contractedResponse (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (Marked m → AES.Word) → ℝ :=
  WordMarkedResponse.contractedResponse m (rawMarkedLeg m)
    (graphCoordinate boundary.toAddMonoidHom) s

theorem contractedResponse_formula (m : GraphPosition → Bool)
    (s : Activity m → Bool) (y : Marked m → AES.Word) :
    contractedResponse m s y = ∑ x : AES.WordState,
      (∏ p : Marked m, rawMarkedLeg m p (y p)
        (graphCoordinate boundary.toAddMonoidHom x p.val)) *
      WordActivityFrame.frameColumn s
        (fun p => graphCoordinate boundary.toAddMonoidHom x p.val) :=
  WordMarkedResponse.contractedResponse_formula m (rawMarkedLeg m)
    (graphCoordinate boundary.toAddMonoidHom) s y

theorem contractedResponse_analyze (m : GraphPosition → Bool)
    (s : Activity m → Bool) (y : Marked m → AES.Word) :
    contractedResponse m s y = WordFrameCoordinates.analyze
      (fun v => vectorizedResponse m (MarkedBlockVectorization.join m y v)) s := by
  have hj : (fun v => vectorizedResponse m (MarkedBlockVectorization.join m y v)) =
      MarkedBlockVectorization.splitResponse m (rawMarkedLeg m)
        (graphCoordinate boundary.toAddMonoidHom) y := by
    funext v
    exact vectorizedResponse_join m y v
  exact (congrFun (congrArg WordFrameCoordinates.analyze hj) s).symm

/-- There is exactly one inverse 65536 per uniform activity coordinate. -/
theorem contractedResponse_shortened (m : GraphPosition → Bool)
    (s : Activity m → Bool) (y : Marked m → AES.Word) :
    contractedResponse m s y =
      rawResponse boundary.toAddMonoidHom m s (rawMarkedLeg m) y /
        (65536 : ℝ) ^ uniformCount s :=
  WordMarkedResponse.contractedResponse_shortened boundary.toAddMonoidHom m s
    (rawMarkedLeg m) y

/-- The normalized source is the same actual shortened graph on all legs. -/
theorem contractedResponse_normalized (m : GraphPosition → Bool)
    (s : Activity m → Bool) (y : Marked m → AES.Word) :
    contractedResponse m s y =
      (Real.sqrt (Fintype.card (ShortenedGraph boundary.toAddMonoidHom
        (outputZeros m s) (inputZeros m s))) / (65536 : ℝ) ^ uniformCount s) *
      MixedCodeMoment.normalizedResponse (rawMarkedLeg m)
        (sourceCoordinates boundary.toAddMonoidHom m s) y :=
  WordMarkedResponse.contractedResponse_normalized boundary.toAddMonoidHom m s
    (rawMarkedLeg m) y

theorem normalization_square (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (Real.sqrt (Fintype.card (ShortenedGraph boundary.toAddMonoidHom
      (outputZeros m s) (inputZeros m s))) / (65536 : ℝ) ^ uniformCount s) ^ 2 =
      WordMarkedResponse.q ^
        (4 - (AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))) /
        WordMarkedResponse.q ^ uniformCount s :=
  WordMarkedResponse.boundary_normalization_square m s

/-- Raw marked Pi in the accepted physical output/input coordinate split. -/
def physicalKernel (m : GraphPosition → Bool) :
    ((OutputMarked m → AES.Word) × (OutputActivity m → AES.Word)) →
    ((InputMarked m → AES.Word) × (InputActivity m → AES.Word)) → ℝ :=
  fun yu xv => vectorizedResponse m
    (MarkedBlockVectorization.join m (WordMarkedSplit.join m yu.1 xv.1)
      (WordActivitySplit.join m yu.2 xv.2))

theorem physicalKernel_matrix (m : GraphPosition → Bool)
    (yu : (OutputMarked m → AES.Word) × (OutputActivity m → AES.Word))
    (xv : (InputMarked m → AES.Word) × (InputActivity m → AES.Word)) :
    physicalKernel m yu xv =
      markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i))
        (WordActivitySplit.outputEquiv m yu) (WordActivitySplit.inputEquiv m xv) := by
  unfold physicalKernel
  rw [WordActivitySplit.physical_join, vectorizedResponse_matrix]

theorem physicalKernel_splitResponse (m : GraphPosition → Bool)
    (y : OutputMarked m → AES.Word) (x : InputMarked m → AES.Word)
    (u : OutputActivity m → AES.Word) (v : InputActivity m → AES.Word) :
    physicalKernel m (y,u) (x,v) =
      MarkedBlockVectorization.splitResponse m (rawMarkedLeg m)
        (graphCoordinate boundary.toAddMonoidHom)
        (WordMarkedSplit.join m y x) (WordActivitySplit.join m u v) :=
  vectorizedResponse_join m _ _

def markedWeight (m : GraphPosition → Bool)
    (y : OutputMarked m → AES.Word) (x : InputMarked m → AES.Word)
    (w : AES.WordState) : ℝ :=
  ∏ p : Marked m, rawMarkedLeg m p (WordMarkedSplit.join m y x p)
    (graphCoordinate boundary.toAddMonoidHom w p.val)

/-- Both activity projectors and all residual factors share the source w. -/
theorem physicalKernel_formula (m : GraphPosition → Bool)
    (y : OutputMarked m → AES.Word) (x : InputMarked m → AES.Word)
    (u : OutputActivity m → AES.Word) (v : InputActivity m → AES.Word) :
    physicalKernel m (y,u) (x,v) = ∑ w : AES.WordState,
      markedWeight m y x w * tensorActivityKernel u (outputSource m w) *
        tensorActivityKernel v (inputSource m w) := by
  rw [physicalKernel_splitResponse]
  unfold MarkedBlockVectorization.splitResponse
  apply Finset.sum_congr rfl
  intro w _
  rw [WordActivitySplit.prod_positions]
  simp only [WordActivitySplit.join_output, WordActivitySplit.join_input]
  change markedWeight m y x w *
    (tensorActivityKernel u (outputSource m w) * tensorActivityKernel v (inputSource m w)) = _
  ring

theorem physicalKernel_output_fixed (m : GraphPosition → Bool)
    (y : OutputMarked m → AES.Word)
    (xv : (InputMarked m → AES.Word) × (InputActivity m → AES.Word)) :
    projectActivity (fun u => physicalKernel m (y,u) xv) =
      (fun u => physicalKernel m (y,u) xv) := by
  have he : (fun u => physicalKernel m (y,u) xv) =
      (fun u => ∑ w : AES.WordState,
        (markedWeight m y xv.1 w * tensorActivityKernel xv.2 (inputSource m w)) *
          tensorActivityKernel u (outputSource m w)) := by
    funext u
    rw [physicalKernel_formula]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [he]
  exact WordPhysicalActivity.project_sum_columns _ _

theorem physicalKernel_input_fixed (m : GraphPosition → Bool)
    (yu : (OutputMarked m → AES.Word) × (OutputActivity m → AES.Word))
    (x : InputMarked m → AES.Word) :
    projectActivity (fun v => physicalKernel m yu (x,v)) =
      (fun v => physicalKernel m yu (x,v)) := by
  have he : (fun v => physicalKernel m yu (x,v)) =
      (fun v => ∑ w : AES.WordState,
        (markedWeight m yu.1 x w * tensorActivityKernel yu.2 (outputSource m w)) *
          tensorActivityKernel v (inputSource m w)) := by
    funext v
    exact physicalKernel_formula m yu.1 x yu.2 v
  rw [he]
  exact WordPhysicalActivity.project_sum_columns _ _

/-- The double word-frame analysis is exactly the raw contracted response. -/
theorem physicalKernel_contraction (m : GraphPosition → Bool)
    (so : OutputActivity m → Bool) (si : InputActivity m → Bool)
    (y : OutputMarked m → AES.Word) (x : InputMarked m → AES.Word) :
    (∑ u : OutputActivity m → AES.Word, ∑ v : InputActivity m → AES.Word,
      WordActivityFrame.frameColumn so u * physicalKernel m (y,u) (x,v) *
        WordActivityFrame.frameColumn si v) =
      contractedResponse m (WordActivitySplit.join m so si) (WordMarkedSplit.join m y x) := by
  rw [contractedResponse_analyze]
  unfold WordFrameCoordinates.analyze action
  rw [WordActivitySplit.sum_tuples]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  dsimp only
  rw [WordActivitySplit.frameColumn_join]
  change _ = (WordActivityFrame.frameColumn so u * WordActivityFrame.frameColumn si v) *
    physicalKernel m (y,u) (x,v)
  ring

theorem physical_contraction_eq (m : GraphPosition → Bool)
    (so : OutputActivity m → Bool) (si : InputActivity m → Bool) :
    WordActivityArray.contraction (physicalKernel m) so si =
      WordOperatorDuality.reshape m (contractedResponse m (WordActivitySplit.join m so si)) := by
  funext y x
  exact physicalKernel_contraction m so si y x

/-- Generic signed-input activity-array comparison for actual raw Pi.
Its premises are the explicit per-choice and scalar estimates. -/
theorem physicalKernel_array_bound (m : GraphPosition → Bool)
    (F : (OutputActivity m → Bool) → (InputActivity m → Bool) → ℝ) (n : ℝ)
    (hF : ∀ so si, 0 ≤ F so si)
    (hT : ∀ so si, EnergyBound (WordOperatorDuality.reshape m
      (contractedResponse m (WordActivitySplit.join m so si))) (F so si))
    (hScalar : EnergyBound F n) :
    EnergyBound (physicalKernel m)
      ((WordActivityFrame.conditioningFactor (Fintype.card (OutputActivity m)) *
        WordActivityFrame.conditioningFactor (Fintype.card (InputActivity m))) * n) := by
  apply WordActivityArray.activity_array_bound_of_sections (physicalKernel m) F n
    (physicalKernel_input_fixed m) (physicalKernel_output_fixed m) hF _ hScalar
  intro so si
  rw [physical_contraction_eq]
  exact hT so si

/-- Both raw physical frame factors, transported back by the actual
coordinate equivalences to the full word-state marked Pi kernel. -/
theorem markedKernel_array_bound (m : GraphPosition → Bool)
    (F : (OutputActivity m → Bool) → (InputActivity m → Bool) → ℝ) (n : ℝ)
    (hF : ∀ so si, 0 ≤ F so si)
    (hT : ∀ so si, EnergyBound (WordOperatorDuality.reshape m
      (contractedResponse m (WordActivitySplit.join m so si))) (F so si))
    (hScalar : EnergyBound F n) :
    EnergyBound
      (markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)))
      ((WordActivityFrame.conditioningFactor (Fintype.card (OutputActivity m)) *
        WordActivityFrame.conditioningFactor (Fintype.card (InputActivity m))) * n) := by
  have h := RectangularArrays.energyBound_reindex (physicalKernel m) _
    (WordActivitySplit.outputEquiv m).symm (WordActivitySplit.inputEquiv m).symm
    (physicalKernel_array_bound m F n hF hT hScalar)
  simpa only [physicalKernel_matrix, Equiv.apply_symm_apply] using h

end AESPaper.RawBoundaryKernel
