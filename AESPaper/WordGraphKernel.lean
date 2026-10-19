import AESPaper.BoundaryContraction
import AESConcrete.MarkedBlockVectorization

/-!
# Exact graph kernels for the outer word sandwich

The middle transport is the actual forward boundary acting on laws by its
inverse. Hence the common graph/source label is `(boundary x,x)`. Every
input residual leg is transposed under vectorization. No symmetry of the
word channel, sign condition, probability normalization, or independence
of an input function is used in these exact identities.

Only the alphabet-generic definitions `Marked`, `Activity`, `join`,
`partitionEquiv`, `fullResponse`, `splitResponse`, and `fullResponse_join`
from the frozen MarkedBlockVectorization API are used below. In particular,
no byte-cardinality, byte-frame, or byte-energy wrapper is instantiated on
the word alphabet.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordGraphKernel
open AESMixing AESConcrete
open AESPaper.GroupedRecurrence
open AESPaper.WordDamping

section FiniteTransport

variable {W : Type*} [Fintype W]

/-- A kernel before and after forward law transport by a permutation. -/
def transportKernel (e : Equiv.Perm W) (K L : W → W → ℝ) : W → W → ℝ :=
  kernelCompose (fun y x => K y (e x)) L

/-- Reindexing uses the forward map in the kernel and the inverse on laws. -/
theorem transportKernel_action (e : Equiv.Perm W) (K L : W → W → ℝ)
    (f : W → ℝ) :
    action (transportKernel e K L) f =
      action K (fun y => action L f (e.symm y)) := by
  rw [transportKernel, kernelCompose_action]
  funext y
  change (∑ x, K y (e x) * action L f x) =
    ∑ z, K y z * action L f (e.symm z)
  simpa only [Equiv.symm_apply_apply] using
    Equiv.sum_comp e (fun z => K y z * action L f (e.symm z))

/-- The same generic identity with the law-transport wrapper kept opaque. -/
theorem transportKernel_action_relabel (e : Equiv.Perm W) (K L : W → W → ℝ)
    (f : W → ℝ) :
    action (transportKernel e K L) f = action K (lawRelabel e (action L f)) :=
  transportKernel_action e K L f

variable [DecidableEq W]

/-- Output composition preserves the same middle graph label. -/
theorem transportKernel_compose_left (e : Equiv.Perm W)
    (P K L : W → W → ℝ) :
    kernelCompose P (transportKernel e K L) =
      transportKernel e (kernelCompose P K) L := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action, transportKernel_action]

/-- Input composition preserves the same middle graph label. -/
theorem transportKernel_compose_right (e : Equiv.Perm W)
    (K L Q : W → W → ℝ) :
    kernelCompose (transportKernel e K L) Q =
      transportKernel e K (kernelCompose L Q) := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action, transportKernel_action]

theorem transportKernel_two_sided (e : Equiv.Perm W)
    (P K L Q : W → W → ℝ) :
    kernelCompose P (kernelCompose (transportKernel e K L) Q) =
      transportKernel e (kernelCompose P K) (kernelCompose L Q) := by
  rw [transportKernel_compose_right, transportKernel_compose_left]

end FiniteTransport

section CoordinateKernels

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [DecidableEq V]

/-- Exact common-source graph sum for arbitrary coordinate kernels. -/
theorem coordinate_transportKernel (e : Equiv.Perm (I → V))
    (D E : I → V → V → ℝ) (y a : I → V) :
    transportKernel e (coordinateKernel D) (coordinateKernel E) y a =
      ∑ x : I → V, (∏ i : I, D i (y i) (e x i)) *
        ∏ i : I, E i (x i) (a i) := rfl

variable [Zero V]

/-- The activity/residual piece of an arbitrary channel; no byte constants. -/
def channelPiece (D : V → V → ℝ) (b : Bool) : V → V → ℝ :=
  if b then residualMatrix D 0 else activityMatrix 0

/-- Vectorization preserves output orientation and transposes input legs. -/
def residualLeg (D E : I → V → V → ℝ) : (I ⊕ I) → V → V → ℝ :=
  Sum.elim (fun i y x => residualMatrix (D i) 0 y x)
    (fun i a x => residualMatrix (E i) 0 x a)

def markedLeg (D E : I → V → V → ℝ) (m : (I ⊕ I) → Bool) :
    MarkedBlockVectorization.Marked m → V → V → ℝ :=
  fun p => residualLeg D E p.val

/-- The full physical graph is retained before any shortening or estimates. -/
def vectorizedResponse (D E : I → V → V → ℝ)
    (e : Equiv.Perm (I → V)) (m : (I ⊕ I) → Bool) : ((I ⊕ I) → V) → ℝ :=
  MarkedBlockVectorization.fullResponse m (markedLeg D E m)
    (fun x => Sum.elim (e x) x)

/-- Alphabet-generic vectorization. Activity symmetry is used only on the
unmarked input legs; residual input legs keep their transpose. -/
theorem vectorizedResponse_matrix (D E : I → V → V → ℝ)
    (e : Equiv.Perm (I → V)) (m : (I ⊕ I) → Bool) (y a : I → V) :
    vectorizedResponse D E e m (Sum.elim y a) =
      transportKernel e
        (coordinateKernel (fun i => channelPiece (D i) (m (Sum.inl i))))
        (coordinateKernel (fun i => channelPiece (E i) (m (Sum.inr i)))) y a := by
  rw [coordinate_transportKernel]
  unfold vectorizedResponse MarkedBlockVectorization.fullResponse
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    by_cases hm : m (Sum.inl i) = true <;>
      simp [markedLeg, residualLeg, channelPiece, hm]
  · apply Finset.prod_congr rfl
    intro i _
    by_cases hm : m (Sum.inr i) = true <;>
      simp [markedLeg, residualLeg, channelPiece, hm, activityMatrix_symmetric]

/-- Splitting marked and activity coordinates is a change of indexing only. -/
theorem vectorizedResponse_join (D E : I → V → V → ℝ)
    (e : Equiv.Perm (I → V)) (m : (I ⊕ I) → Bool)
    (y : MarkedBlockVectorization.Marked m → V)
    (v : MarkedBlockVectorization.Activity m → V) :
    vectorizedResponse D E e m (MarkedBlockVectorization.join m y v) =
      MarkedBlockVectorization.splitResponse m (markedLeg D E m)
        (fun x => Sum.elim (e x) x) y v :=
  MarkedBlockVectorization.fullResponse_join m (markedLeg D E m)
    (fun x => Sum.elim (e x) x) y v

end CoordinateKernels

/- The specialization below stops at the opaque actual word-channel and
boundary interfaces. Do not unfold the concrete bit-level AES definitions
to establish a function equality or a permutation change of variables. -/

/-- The actual matrix of H Pi H, before the separate final input Pi. -/
def sandwichKernel : AES.WordState → AES.WordState → ℝ :=
  transportKernel boundary.toEquiv AES.parallelSuperboxKernel AES.parallelSuperboxKernel

theorem sandwichKernel_action (f : AES.WordState → ℝ) :
    action sandwichKernel f = H (Pi (H f)) := by
  -- Use typed wrapper equalities instead of comparing nested concrete inverse
  -- maps during definitional equality; the generic relabel theorem already
  -- proved the entire permutation change of variables.
  have hs : action sandwichKernel f =
      action (transportKernel boundary.toEquiv
        AES.parallelSuperboxKernel AES.parallelSuperboxKernel) f := rfl
  have hh : action AES.parallelSuperboxKernel f = H f := rfl
  have hp : lawRelabel boundary.toEquiv (H f) = Pi (H f) := rfl
  have ho : action AES.parallelSuperboxKernel (Pi (H f)) = H (Pi (H f)) := rfl
  exact hs.trans ((transportKernel_action_relabel boundary.toEquiv
    AES.parallelSuperboxKernel AES.parallelSuperboxKernel f).trans
      ((congrArg (fun g : AES.WordState → ℝ =>
        action AES.parallelSuperboxKernel (lawRelabel boundary.toEquiv g)) hh).trans
          ((congrArg (fun g : AES.WordState → ℝ =>
            action AES.parallelSuperboxKernel g) hp).trans ho)))

/-- Exact physical outer-word kernel, with one common graph/source point. -/
theorem sandwichKernel_graph (y a : AES.WordState) :
    sandwichKernel y a =
      ∑ x : AES.WordState,
        (∏ i : Fin 4, AES.wordSuperboxKernel (y i) (boundary x i)) *
        ∏ i : Fin 4, AES.wordSuperboxKernel (x i) (a i) := by
  exact coordinate_transportKernel boundary.toEquiv
    (fun _ : Fin 4 => AES.wordSuperboxKernel)
    (fun _ : Fin 4 => AES.wordSuperboxKernel) y a

/-- The action identity applies to every signed joint function. -/
theorem sandwichKernel_graph_action (f : AES.WordState → ℝ) (y : AES.WordState) :
    H (Pi (H f)) y =
      ∑ a : AES.WordState,
        (∑ x : AES.WordState,
          (∏ i : Fin 4, AES.wordSuperboxKernel (y i) (boundary x i)) *
          ∏ i : Fin 4, AES.wordSuperboxKernel (x i) (a i)) * f a := by
  rw [← sandwichKernel_action]
  simp only [action, sandwichKernel_graph]

/-- Match the existing Hilbert-space sandwich without changing its domain. -/
theorem sandwich_eq_action (f : AESPaper.ProfileSpace.State) (x : AES.WordState) :
    BoundaryContraction.sandwich f x = action sandwichKernel (fun y => f y) x := by
  exact (BoundaryContraction.sandwich_apply f x).trans
    (congrFun (sandwichKernel_action (fun y => f y)) x).symm

/-- The complete repeated operator retains the separate right boundary. -/
theorem fourRound_eq_action (f : AESPaper.ProfileSpace.State) (x : AES.WordState) :
    ConcreteProfile.fourRound f x =
      action sandwichKernel (fun y => f (boundary.symm y)) x := by
  rw [BoundaryContraction.fourRound_eq_sandwich_boundary]
  have hs := sandwich_eq_action (BoundaryContraction.boundaryLayer f) x
  have hb : (fun y => BoundaryContraction.boundaryLayer f y) =
      (fun y => f (boundary.symm y)) := by
    funext y
    exact (BoundaryContraction.boundaryLayer_apply f y).trans (Pi_apply (fun z => f z) y)
  exact hs.trans (congrArg (fun g : AES.WordState → ℝ => action sandwichKernel g x) hb)

/-- Projecting the output of the actual H produces the same word pieces. -/
theorem parallel_pattern_left (out : Fin 4 → Bool) :
    kernelCompose (productProjection (0 : AES.Word) out) AES.parallelSuperboxKernel =
      coordinateKernel (fun i => wordPiece (out i)) := by
  exact (WordChannelCommutation.coordinate_pattern_commutes
    (fun _ : Fin 4 => AES.word_superbox_pointed) out).symm.trans
    (parallel_pattern_right out)

/-- Actual two-sided residual-position block of the physical sandwich. -/
def markedKernel (out inp : Fin 4 → Bool) : AES.WordState → AES.WordState → ℝ :=
  kernelCompose (productProjection (0 : AES.Word) out)
    (kernelCompose sandwichKernel (productProjection (0 : AES.Word) inp))

theorem markedKernel_action (out inp : Fin 4 → Bool) (f : AES.WordState → ℝ) :
    action (markedKernel out inp) f =
      action (productProjection (0 : AES.Word) out)
        (H (Pi (H (action (productProjection (0 : AES.Word) inp) f)))) := by
  simp only [markedKernel, kernelCompose_action, sandwichKernel_action]

/-- Both projections are absorbed into the actual channel factors. -/
theorem markedKernel_piece_kernel (out inp : Fin 4 → Bool) :
    markedKernel out inp = transportKernel boundary.toEquiv
      (coordinateKernel (fun i => wordPiece (out i)))
      (coordinateKernel (fun i => wordPiece (inp i))) := by
  rw [markedKernel, sandwichKernel, transportKernel_two_sided,
    parallel_pattern_left, parallel_pattern_right]

theorem markedKernel_graph (out inp : Fin 4 → Bool) (y a : AES.WordState) :
    markedKernel out inp y a =
      ∑ x : AES.WordState, (∏ i : Fin 4, wordPiece (out i) (y i) (boundary x i)) *
        ∏ i : Fin 4, wordPiece (inp i) (x i) (a i) := by
  rw [markedKernel_piece_kernel]
  exact coordinate_transportKernel boundary.toEquiv
    (fun i => wordPiece (out i)) (fun i => wordPiece (inp i)) y a

/-- The word marked response reuses only the frozen generic fullResponse. -/
def wordVectorizedResponse (m : GraphPosition → Bool) : (GraphPosition → AES.Word) → ℝ :=
  MarkedBlockVectorization.fullResponse m
    (markedLeg (fun _ : Fin 4 => AES.wordSuperboxKernel)
      (fun _ : Fin 4 => AES.wordSuperboxKernel) m)
    (graphCoordinate boundary.toAddMonoidHom)

theorem wordVectorizedResponse_matrix (m : GraphPosition → Bool)
    (y a : AES.WordState) :
    wordVectorizedResponse m (Sum.elim y a) =
      markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)) y a := by
  rw [markedKernel_piece_kernel]
  have h := vectorizedResponse_matrix
    (fun _ : Fin 4 => AES.wordSuperboxKernel)
    (fun _ : Fin 4 => AES.wordSuperboxKernel) boundary.toEquiv m y a
  have hc : (graphCoordinate boundary.toAddMonoidHom :
      AES.WordState → GraphPosition → AES.Word) =
      (fun x : AES.WordState => Sum.elim (boundary.toEquiv x) x) := by
    funext x p
    cases p <;> rfl
  unfold wordVectorizedResponse
  rw [hc]
  simpa only [vectorizedResponse, channelPiece, wordPiece] using h

/-- The actual graph response with marked and activity arguments separated. -/
theorem wordVectorizedResponse_join (m : GraphPosition → Bool)
    (y : MarkedBlockVectorization.Marked m → AES.Word)
    (v : MarkedBlockVectorization.Activity m → AES.Word) :
    wordVectorizedResponse m (MarkedBlockVectorization.join m y v) =
      MarkedBlockVectorization.splitResponse m
        (markedLeg (fun _ : Fin 4 => AES.wordSuperboxKernel)
          (fun _ : Fin 4 => AES.wordSuperboxKernel) m)
        (graphCoordinate boundary.toAddMonoidHom) y v :=
  MarkedBlockVectorization.fullResponse_join m
    (markedLeg (fun _ : Fin 4 => AES.wordSuperboxKernel)
      (fun _ : Fin 4 => AES.wordSuperboxKernel) m)
    (graphCoordinate boundary.toAddMonoidHom) y v

/-- Exact sum-of-squares reindexing, before activity-frame contraction. -/
theorem markedKernel_hilbertSchmidt_square (m : GraphPosition → Bool) :
    (∑ y : AES.WordState, ∑ a : AES.WordState,
      markedKernel (fun i => m (Sum.inl i)) (fun i => m (Sum.inr i)) y a ^ 2) =
      ∑ v : GraphPosition → AES.Word, wordVectorizedResponse m v ^ 2 := by
  rw [← (Equiv.sumArrowEquivProdArrow (Fin 4) (Fin 4) AES.Word).symm.sum_comp
    (fun v => wordVectorizedResponse m v ^ 2), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun z : ℝ => z ^ 2) (wordVectorizedResponse_matrix m y a).symm

end AESPaper.WordGraphKernel
