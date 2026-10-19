import AESPaper.WordGraphKernel
import AESPaper.WordFrameCoordinates
import AESPaper.ActivityKernel
import AESConcrete.MarkedBlockShortening
import AESConcrete.MarkedBlockVanishing

/-!
# Exact marked contractions and shortened sources over actual AES words

The frozen MarkedBlockShortening API is used only for alphabet-generic zero
positions, graph conditions, source coordinates, raw response, and source
cardinality. Its byte-frame contractions and 16/256 wrappers are not used.
Every activity and frame identity below concerns the actual word alphabet;
the normalized uniform word column has value 1/65536.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordMarkedResponse
open AESMixing AESConcrete
open AESPaper.WordActivityFrame
open AESConcrete.MarkedBlockVectorization (Marked Activity splitResponse)
open AESConcrete.MarkedBlockShortening (uniformCount outputZeros inputZeros
  sourceCoordinates rawResponse)

attribute [local instance] Classical.propDecidable

/-- The actual word alphabet size, retained as a real scalar. -/
def q : ℝ := 2^32

theorem q_eq_word_card : q = (Fintype.card AES.Word : ℝ) := by
  rw [AES.word_card]
  norm_num [q]

section ActivityProjector
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Idempotence at the exact kernel interface, with no range premise. -/
theorem tensorActivityKernel_idempotent :
    kernelCompose (WordFrameCoordinates.tensorActivityKernel (I := J))
      WordFrameCoordinates.tensorActivityKernel = WordFrameCoordinates.tensorActivityKernel := by
  apply kernel_action_ext
  intro f
  rw [kernelCompose_action]
  exact WordFrameCoordinates.projectActivity_idempotent f

/-- Analysis of an actual activity-projector column is the corresponding
word-frame entry. This uses the exact projector/analysis identity. -/
theorem analyze_activity_column (s : J → Bool) (x : J → AES.Word) :
    (∑ v : J → AES.Word, frameColumn s v *
      WordFrameCoordinates.tensorActivityKernel v x) = frameColumn s x := by
  have hc : kernelCompose
      (fun (t : J → Bool) (v : J → AES.Word) => frameColumn t v)
      WordFrameCoordinates.tensorActivityKernel =
      (fun (t : J → Bool) (v : J → AES.Word) => frameColumn t v) := by
    apply kernel_action_ext
    intro f
    rw [kernelCompose_action]
    exact WordFrameCoordinates.analyze_projectActivity f
  exact congrFun (congrFun hc s) x

end ActivityProjector

section Response
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

/-- Actual word-frame analysis of the activity family, with marked arguments
untouched. It is not the canonical inverse-Gram coefficient map. -/
def contractedResponse (m : I → Bool) (T : Marked m → AES.Word → AES.Word → ℝ)
    (coord : X → I → AES.Word) (s : Activity m → Bool) (y : Marked m → AES.Word) : ℝ :=
  WordFrameCoordinates.analyze (splitResponse m T coord y) s

/-- Arbitrary signed marked kernels give a family fixed by the actual
tensor activity projection. The same source point remains on all legs. -/
theorem splitResponse_activity (m : I → Bool)
    (T : Marked m → AES.Word → AES.Word → ℝ) (coord : X → I → AES.Word)
    (y : Marked m → AES.Word) :
    WordFrameCoordinates.projectActivity (splitResponse m T coord y) =
      splitResponse m T coord y := by
  funext v
  unfold WordFrameCoordinates.projectActivity action splitResponse
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = (∏ i : Marked m, T i (y i) (coord x i.val)) *
        ∑ w : Activity m → AES.Word,
          WordFrameCoordinates.tensorActivityKernel v w *
            WordFrameCoordinates.tensorActivityKernel w (fun i => coord x i.val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      change WordFrameCoordinates.tensorActivityKernel v w *
          ((∏ i : Marked m, T i (y i) (coord x i.val)) *
            WordFrameCoordinates.tensorActivityKernel w (fun i => coord x i.val)) = _
      ring
    _ = _ := by
      have hc := congrFun (congrFun (tensorActivityKernel_idempotent
        (J := Activity m)) v) (fun i => coord x i.val)
      change (∑ w : Activity m → AES.Word,
        WordFrameCoordinates.tensorActivityKernel v w *
          WordFrameCoordinates.tensorActivityKernel w (fun i => coord x i.val)) = _ at hc
      rw [hc]
      rfl

/-- Exact contraction formula. The sum remains over the original common
source; its coordinate values have not been replaced by independent labels. -/
theorem contractedResponse_formula (m : I → Bool)
    (T : Marked m → AES.Word → AES.Word → ℝ) (coord : X → I → AES.Word)
    (s : Activity m → Bool) (y : Marked m → AES.Word) :
    contractedResponse m T coord s y =
      ∑ x : X, (∏ i : Marked m, T i (y i) (coord x i.val)) *
        frameColumn s (fun i => coord x i.val) := by
  unfold contractedResponse WordFrameCoordinates.analyze action splitResponse
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = (∏ i : Marked m, T i (y i) (coord x i.val)) *
        ∑ v : Activity m → AES.Word, frameColumn s v *
          WordFrameCoordinates.tensorActivityKernel v (fun i => coord x i.val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      change frameColumn s v *
          ((∏ i : Marked m, T i (y i) (coord x i.val)) *
            WordFrameCoordinates.tensorActivityKernel v (fun i => coord x i.val)) = _
      ring
    _ = _ := by rw [analyze_activity_column]

/-- Canonical coefficients retain the separate inverse Gram after analysis. -/
theorem coefficients_splitResponse (m : I → Bool)
    (T : Marked m → AES.Word → AES.Word → ℝ) (coord : X → I → AES.Word)
    (y : Marked m → AES.Word) :
    WordFrameCoordinates.coefficients (splitResponse m T coord y) =
      action frameInverse (fun s => contractedResponse m T coord s y) := rfl

/-- Reconstruction follows from actual fixedness, rather than being an
assumed property of the marked activity family. -/
theorem splitResponse_reconstruct (m : I → Bool)
    (T : Marked m → AES.Word → AES.Word → ℝ) (coord : X → I → AES.Word)
    (y : Marked m → AES.Word) :
    synthesize (WordFrameCoordinates.coefficients (splitResponse m T coord y)) =
      splitResponse m T coord y :=
  WordFrameCoordinates.reconstruct_of_fixed _ (splitResponse_activity m T coord y)

end Response

section FrameWeight
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Exact zero/uniform weight for normalized actual word-frame columns. -/
theorem frame_weight (s : I → Bool) (x : I → AES.Word) :
    frameColumn s x =
      (if ∀ i : I, s i = false → x i = 0 then (1 : ℝ) else 0) /
        (65536 : ℝ)^uniformCount s := by
  have hp (i : I) : wordFrame (s i) (x i) =
      (if s i = false → x i = 0 then (1 : ℝ) else 0) /
        (if s i then (65536 : ℝ) else 1) := by
    cases hs : s i <;> simp [wordFrame, identityKernel, hs]
  unfold frameColumn
  simp_rw [hp]
  rw [Finset.prod_div_distrib, product_indicator]
  congr 1
  simp [uniformCount, Fintype.card_subtype, Finset.prod_ite]

end FrameWeight

section Shortening

/-- Word contraction imposes exactly the physical graph zero conditions. -/
theorem contractedResponse_shortened (L : AES.WordState →+ AES.WordState)
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (T : Marked m → AES.Word → AES.Word → ℝ) (y : Marked m → AES.Word) :
    contractedResponse m T (graphCoordinate L) s y =
      rawResponse L m s T y / (65536 : ℝ)^uniformCount s := by
  rw [contractedResponse_formula]
  have hw (x : AES.WordState) :
      frameColumn s (fun i => graphCoordinate L x i.val) =
        (if graphZeroConditions L (outputZeros m s) (inputZeros m s) x
          then (1 : ℝ) else 0) / (65536 : ℝ)^uniformCount s := by
    rw [frame_weight]
    by_cases hx : graphZeroConditions L (outputZeros m s) (inputZeros m s) x
    · rw [if_pos ((MarkedBlockShortening.graph_conditions L m s x).mp hx), if_pos hx]
    · have hf : ¬ ∀ i : Activity m, s i = false → graphCoordinate L x i.val = 0 :=
        fun h => hx ((MarkedBlockShortening.graph_conditions L m s x).mpr h)
      rw [if_neg hf, if_neg hx]
  calc
    _ = (∑ x : AES.WordState,
        (if graphZeroConditions L (outputZeros m s) (inputZeros m s) x
          then (1 : ℝ) else 0) *
          ∏ p : Marked m, T p (y p) (graphCoordinate L x p.val)) /
        (65536 : ℝ)^uniformCount s := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x _
      rw [hw x]
      ring
    _ = rawResponse L m s T y / (65536 : ℝ)^uniformCount s := by
      -- Scalar congruence stops at the numerator instead of recursively
      -- traversing concrete AES function types inside an untyped congr tactic.
      apply congrArg (fun a : ℝ => a / (65536 : ℝ)^uniformCount s)
      exact shortened_graph_weight L (outputZeros m s) (inputZeros m s)
        (fun x => ∏ p : Marked m, T p (y p) (graphCoordinate L x p.val))

/-- Normalization uses the square root of the cardinality of the same actual
shortened source. This is unit-source, rather than probability, normalization. -/
theorem contractedResponse_normalized (L : AES.WordState →+ AES.WordState)
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (T : Marked m → AES.Word → AES.Word → ℝ) (y : Marked m → AES.Word) :
    contractedResponse m T (graphCoordinate L) s y =
      (Real.sqrt (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s))) /
        (65536 : ℝ)^uniformCount s) *
        MixedCodeMoment.normalizedResponse T (sourceCoordinates L m s) y := by
  have hc : 0 < Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s)) :=
    Fintype.card_pos_iff.mpr
      ⟨ShortenedLineResponse.zeroGraph L (outputZeros m s) (inputZeros m s)⟩
  have hs : 0 < Real.sqrt
      (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s)) : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hc)
  rw [contractedResponse_shortened]
  unfold MixedCodeMoment.normalizedResponse MixedCodeMoment.responseKernel rawResponse
  field_simp [ne_of_gt hs]

/-- Exact scalar square; no MDS, surviving-code, or dimension premise is used. -/
theorem normalization_square (L : AES.WordState →+ AES.WordState)
    (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (Real.sqrt (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s))) /
      (65536 : ℝ)^uniformCount s)^2 =
      (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s)) : ℝ) /
        q^uniformCount s := by
  have hp : ((65536 : ℝ)^uniformCount s)^2 = q^uniformCount s := by
    rw [← pow_mul, Nat.mul_comm (uniformCount s) 2, pow_mul]
    norm_num [q]
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), hp]

/-- The generic exact MDS count is specialized to the word alphabet. The
natural subtraction is retained literally; it is not a surviving-dimension
formula or an integer-exponent simplification. -/
theorem normalization_square_of_zeroMDS (L : AES.WordState →+ AES.WordState)
    (hL : ZeroMDS L) (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (Real.sqrt (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s))) /
      (65536 : ℝ)^uniformCount s)^2 =
      q^(4-(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))) /
        q^uniformCount s := by
  rw [normalization_square, MarkedBlockShortening.source_card L hL m s,
    Nat.cast_pow, ← q_eq_word_card]

end Shortening

/- The actual boundary and residual-leg wrappers below preserve the physical
orientation already fixed by WordGraphKernel. Never replace input R(x,a)
by output-oriented R(a,x) without an independently proved adjoint identity. -/

def wordMarkedLeg (m : GraphPosition → Bool) : Marked m → AES.Word → AES.Word → ℝ :=
  WordGraphKernel.markedLeg (fun _ : Fin 4 => AES.wordSuperboxKernel)
    (fun _ : Fin 4 => AES.wordSuperboxKernel) m

/-- Input residual transposition changes a zero-column check into the
actual word residual's zero-row check on input legs. -/
theorem wordMarkedLeg_zero_column (m : GraphPosition → Bool) (p : Marked m)
    (y : AES.Word) : wordMarkedLeg m p y 0 = 0 := by
  rcases p with ⟨p,hp⟩
  cases p with
  | inl i =>
      change residualMatrix AES.wordSuperboxKernel 0 y 0 = 0
      exact AESConcrete.pointed_residual_zero_column AES.word_superbox_pointed y
  | inr i =>
      change residualMatrix AES.wordSuperboxKernel 0 0 y = 0
      exact AESConcrete.pointed_residual_zero_row AES.word_superbox_pointed y

def boundaryContractedResponse (m : GraphPosition → Bool) (s : Activity m → Bool)
    (y : Marked m → AES.Word) : ℝ :=
  contractedResponse m (wordMarkedLeg m)
    (graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom) s y

/-- Match contraction to a slice of the actual vectorized marked H Pi H. -/
theorem boundaryContractedResponse_analyze (m : GraphPosition → Bool)
    (s : Activity m → Bool) (y : Marked m → AES.Word) :
    boundaryContractedResponse m s y =
      WordFrameCoordinates.analyze
        (fun v => WordGraphKernel.wordVectorizedResponse m
          (MarkedBlockVectorization.join m y v)) s := by
  have hj : (fun v => WordGraphKernel.wordVectorizedResponse m
      (MarkedBlockVectorization.join m y v)) =
      splitResponse m (wordMarkedLeg m)
        (graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom) y := by
    funext v
    exact WordGraphKernel.wordVectorizedResponse_join m y v
  exact (congrFun (congrArg WordFrameCoordinates.analyze hj) s).symm

theorem boundaryContractedResponse_shortened (m : GraphPosition → Bool)
    (s : Activity m → Bool) (y : Marked m → AES.Word) :
    boundaryContractedResponse m s y =
      rawResponse GroupedRecurrence.boundary.toAddMonoidHom m s (wordMarkedLeg m) y /
        (65536 : ℝ)^uniformCount s :=
  contractedResponse_shortened _ _ _ _ _

theorem boundaryContractedResponse_normalized (m : GraphPosition → Bool)
    (s : Activity m → Bool) (y : Marked m → AES.Word) :
    boundaryContractedResponse m s y =
      (Real.sqrt (Fintype.card (ShortenedGraph GroupedRecurrence.boundary.toAddMonoidHom
        (outputZeros m s) (inputZeros m s))) / (65536 : ℝ)^uniformCount s) *
        MixedCodeMoment.normalizedResponse (wordMarkedLeg m)
          (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) y :=
  contractedResponse_normalized _ _ _ _ _

theorem boundary_source_card (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Fintype.card (ShortenedGraph GroupedRecurrence.boundary.toAddMonoidHom
      (outputZeros m s) (inputZeros m s)) =
      (2^32 : ℕ)^(4-(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))) := by
  have hc := MarkedBlockShortening.source_card GroupedRecurrence.boundary.toAddMonoidHom
    ActivityKernel.aesBoundary_zeroMDS m s
  rw [AES.word_card] at hc
  exact hc

theorem boundary_normalization_square (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (Real.sqrt (Fintype.card (ShortenedGraph GroupedRecurrence.boundary.toAddMonoidHom
      (outputZeros m s) (inputZeros m s))) / (65536 : ℝ)^uniformCount s)^2 =
      q^(4-(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))) /
        q^uniformCount s :=
  normalization_square_of_zeroMDS _ ActivityKernel.aesBoundary_zeroMDS m s

/-- Four actual physical zeros force the graph source to zero. A marked
coordinate witness is retained to justify the vanishing residual product. -/
theorem boundaryContractedResponse_zero_of_high_zeros (m : GraphPosition → Bool)
    (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hz : 4 ≤ AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))
    (y : Marked m → AES.Word) : boundaryContractedResponse m s y = 0 := by
  have hr := MarkedBlockVanishing.rawResponse_zero_of_high_zeros
    GroupedRecurrence.boundary.toAddMonoidHom ActivityKernel.aesBoundary_zeroMDS
    m s hm hz (wordMarkedLeg m) (wordMarkedLeg_zero_column m) y
  rw [boundaryContractedResponse_shortened, hr, zero_div]

end AESPaper.WordMarkedResponse
