/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Return.PhysicalMiddleKernel
import AES8.Reductions.Fibers.MarkedZeroOverlap
import AESMixing.GraphExpansion

/-!
# A literal ordinary zero-frame physical summand

The full physical return is first distributed into its shared-frame
summands. For the false/false middle frame, a fixed zero on the raw output
and an input point in the right zero graph expose the left zero graph
exactly. The resulting signed action is a double sum on the two actual
forward graphs, with every middle residual channel retained.

This is an entry/action identity before outside residual projections and
before reindexing by outside attained images. It supplies no norm resource,
return cap, event-moment estimate, or full AES theorem. Right inputs are
explicitly graph points; no assertion about ambient zero extension is made.
Constructive proof work only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.PhysicalZeroPattern
open AESMixing AESMixing.AES
open AES8.WordActivityFrame (wordFrame wordInverse)
open AES8.PhysicalMiddleKernel (channelFrameAtom framePair middlePhysicalKernel)
open AES8.MarkedZeroFiber (ZeroGraph boundary)
open AES8.MarkedZeroOverlap (singleMask)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

section Generic
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Three actual residual-channel factors, with the omitted position explicit. -/
def channelTail (D : V → V → ℝ) (z : V) (c : Fin 4)
    (y x : Fin 4 → V) : ℝ :=
  ∏ i : Fin 4, if i = c then 1 else residualMatrix D z (y i) (x i)

theorem channelFrameAtom_zero_frame (D : V → V → ℝ) (z : V) (c : Fin 4)
    (y x : Fin 4 → V) :
    channelFrameAtom D z c false false y x =
      if y c = z ∧ x c = z then channelTail D z c y x else 0 := by
  have hprod : channelFrameAtom D z c false false y x =
      wordFrame z false (y c) * channelTail D z c y x *
        wordFrame z false (x c) := by
    fin_cases c <;>
      simp [channelFrameAtom, channelTail, coordinateKernel, framePair,
        Fin.prod_univ_four] <;> ring
  rw [hprod]
  by_cases hy : y c = z <;> by_cases hx : x c = z <;>
    simp [wordFrame, identityKernel, hy, hx]

/-- A fixed-zero output row reads only the corresponding zero input column. -/
theorem coordinateChannel_zero_of_fixed_row (D : V → V → ℝ) (z : V)
    (hD : PointedBistochastic D z) (r : Fin 4) (y w : Fin 4 → V)
    (hy : y r = z) (hw : w r ≠ z) :
    coordinateKernel (fun _ : Fin 4 => D) y w = 0 := by
  unfold coordinateKernel
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  simp only [hy, hD.zero_row, hw, if_false]

end Generic

/-- One literal middle-frame summand of the uncentered physical return. -/
def frameReturnKernel (c : Fin 4) (s t : Bool) (y x : WordState) : ℝ :=
  ∑ v : WordState,
    parallelSuperboxKernel y (wordMixAddEquiv v) *
      channelFrameAtom wordSuperboxKernel 0 c s t v (wordMixAddEquiv x)

def fourReturnKernel (y x : WordState) : ℝ :=
  ∑ v : WordState,
    parallelSuperboxKernel y (wordMixAddEquiv v) *
      AESConcrete.FourResidualStep.residualTensor v (wordMixAddEquiv x)

private theorem distribute_shared_frame {X : Type*} [Fintype X]
    (h g : X → ℝ) (a : Bool → Bool → ℝ)
    (F : Fin 4 → Bool → Bool → X → ℝ) :
    (∑ v, h v * ((∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
        a s t * F c s t v) + g v)) =
      (∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
        a s t * ∑ v, h v * F c s t v) + ∑ v, h v * g v := by
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Exact distribution of the physical integral, with one inverse coefficient.
The theorem uses whole-return centering removal, not atom-wise cancellation. -/
theorem physicalReturnKernel_frame_expansion (y x : WordState) :
    ReturnCentering.physicalReturnKernel y x =
      (∑ c : Fin 4, ∑ s : Bool, ∑ t : Bool,
        wordInverse AES.Word s t * frameReturnKernel c s t y x) +
      fourReturnKernel y x := by
  rw [PhysicalMiddleKernel.physicalReturnKernel_entry]
  exact distribute_shared_frame
    (fun v => parallelSuperboxKernel y (wordMixAddEquiv v))
    (fun v => AESConcrete.FourResidualStep.residualTensor v (wordMixAddEquiv x))
    (wordInverse AES.Word)
    (fun c s t v =>
      channelFrameAtom wordSuperboxKernel 0 c s t v (wordMixAddEquiv x))

private theorem singleMask_mem : ∀ c i : Fin 4,
    maskBit (singleMask c) i = true ↔ i = c := by decide

/-- Literal singleton zero prescriptions for the same forward physical map. -/
theorem singleton_graph_iff (r z : Fin 4) (v : WordState) :
    graphPrescribed boundary (singleMask r) (singleMask z)
      (0 : WordState) 0 v ↔
      wordMixAddEquiv v r = 0 ∧ v z = 0 := by
  have hL : boundary v = wordMixAddEquiv v := by
    change AESPaper.GroupedRecurrence.boundary v = wordMixAddEquiv v
    rw [AESPaper.BoundaryZeros.boundary_eq_wordMixAddEquiv]
  constructor
  · intro h
    constructor
    · have hr := h.1 r ((singleMask_mem r r).mpr rfl)
      change boundary v r = 0 at hr
      rw [hL] at hr
      exact hr
    · exact h.2 z ((singleMask_mem z z).mpr rfl)
  · rintro ⟨hr, hz⟩
    constructor
    · intro i hi
      have hir : i = r := (singleMask_mem r i).mp hi
      subst i
      change boundary v r = 0
      rw [hL]
      exact hr
    · intro i hi
      have hiz : i = z := (singleMask_mem z i).mp hi
      subst i
      exact hz

abbrev LeftGraph (r c : Fin 4) := ZeroGraph (singleMask r) (singleMask c)
abbrev RightGraph (c z : Fin 4) := ZeroGraph (singleMask c) (singleMask z)

/-- The zero/zero middle frame gives a sum over the actual left graph.
The right argument is an explicit actual right-graph point, and the output
row has its stated fixed zero. All remaining coordinates stay joint. -/
theorem zeroFrame_entry_on_graph (r c z : Fin 4) (y : WordState)
    (hy : y r = 0) (x : RightGraph c z) :
    frameReturnKernel c false false y x.val =
      ∑ v : LeftGraph r c,
        parallelSuperboxKernel y (wordMixAddEquiv v.val) *
          channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) := by
  have hx : wordMixAddEquiv x.val c = 0 :=
    ((singleton_graph_iff c z x.val).mp x.property).1
  let p : WordState → Prop := fun v =>
    graphPrescribed boundary (singleMask r) (singleMask c) (0 : WordState) 0 v
  let w : WordState → ℝ := fun v =>
    parallelSuperboxKernel y (wordMixAddEquiv v) *
      channelTail wordSuperboxKernel 0 c v (wordMixAddEquiv x.val)
  have hs (v : WordState) :
      parallelSuperboxKernel y (wordMixAddEquiv v) *
        channelFrameAtom wordSuperboxKernel 0 c false false v (wordMixAddEquiv x.val) =
      (if p v then (1 : ℝ) else 0) * w v := by
    by_cases hp : p v
    · obtain ⟨_, hv⟩ := (singleton_graph_iff r c v).mp hp
      rw [channelFrameAtom_zero_frame, if_pos ⟨hv, hx⟩]
      simp only [hp, if_true, _root_.one_mul, w]
    · have hzterm : parallelSuperboxKernel y (wordMixAddEquiv v) *
          channelFrameAtom wordSuperboxKernel 0 c false false v (wordMixAddEquiv x.val) = 0 := by
        by_cases hv : v c = 0
        · have ho : wordMixAddEquiv v r ≠ 0 := by
            intro ho
            exact hp ((singleton_graph_iff r c v).mpr ⟨ho, hv⟩)
          have hzero : parallelSuperboxKernel y (wordMixAddEquiv v) = 0 :=
            coordinateChannel_zero_of_fixed_row wordSuperboxKernel 0
              word_superbox_pointed r y (wordMixAddEquiv v) hy ho
          rw [hzero, zero_mul]
        · rw [channelFrameAtom_zero_frame, if_neg (fun h => hv h.1), mul_zero]
      rw [hzterm]
      simp only [hp, if_false, zero_mul]
  unfold frameReturnKernel
  calc
    _ = ∑ v : WordState, (if p v then (1 : ℝ) else 0) * w v :=
      Finset.sum_congr rfl (fun v _ => hs v)
    _ = ∑ v : {v : WordState // p v}, w v.val := indicator_weight_subtype p w
    _ = _ := rfl

/-- Exact two-graph action identity for arbitrary signed right-graph input.
No incidence normalization, fiber constancy, or local norm premise occurs. -/
theorem zeroFrame_action_on_graph (r c z : Fin 4) (y : WordState)
    (hy : y r = 0) (f : RightGraph c z → ℝ) :
    action (fun y (x : RightGraph c z) => frameReturnKernel c false false y x.val) f y =
      ∑ v : LeftGraph r c,
        parallelSuperboxKernel y (wordMixAddEquiv v.val) *
          ∑ x : RightGraph c z,
            channelTail wordSuperboxKernel 0 c v.val (wordMixAddEquiv x.val) * f x := by
  unfold action
  simp_rw [zeroFrame_entry_on_graph r c z y hy, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end AES8.PhysicalZeroPattern
