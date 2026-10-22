/- Module role: Physical return factorization, shared frames and normalized domain transport.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.MarkedZeroOverlap
import AES8.Estimates.Source.OneSourceEventMoment
import AES8.Estimates.Transfer.SharpDegreeStep

/-!
# Four-middle overlap on the actual one-zero ordinary graphs

The row graph has the literal forward constraint `(L v)_r = 0`, and the
column graph has the literal input constraint `x_z = 0`. Rows are observed
at input positions (0,1,2), columns at forward-output positions (1,2,3).
The actual MDS information equivalences prove that these triples label
their graphs exactly. They are not assumptions about arbitrary code sizes.

The omitted row coordinate 3 depends on its whole triple; the omitted
column coordinate 0 depends on its whole triple. The four-factor kernel is
identified exactly with InformationOverlap at A=E=Unit and B=Fin 2.
Its squared energy bound is delta^2*nu^4 on every signed joint input.
The specialization uses the actual AES residual and existing local bounds.

This module supplies only the middle graph/code operator. It does not identify
an outside-projected return, cancel centering, apply the activity metric,
assemble support patterns, or discharge a return cell.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.ReturnFourMiddle
open AESMixing AESMixing.AES
open AES8.MDSFiberCollision AES8.MarkedZeroFiber
open AES8.MarkedZeroOverlap (singleMask inputObservedEquiv outputObservedEquiv)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

-- Only four POSITION names and four-bit masks enter the decidable proofs.
-- AES words, word states, and diffusion values are never enumerated.
private theorem singleMask_bit : ∀ r i : Fin 4,
    maskBit (singleMask r) i = true ↔ i = r := by decide

private theorem singleMask_size : ∀ r : Fin 4, maskSize (singleMask r) = 1 := by decide
private theorem zero_mask_bit : ∀ i : Fin 4, maskBit (0 : Fin 16) i = false := by decide
private theorem zero_mask_size : maskSize (0 : Fin 16) = 0 := by decide
private theorem row_mask_size : maskSize (7 : Fin 16) = 3 := by decide
private theorem column_mask_size : maskSize (14 : Fin 16) = 3 := by decide

private theorem disjoint_zero (m : Fin 16) : MaskDisjoint m 0 := by
  intro i _ hi
  rw [zero_mask_bit] at hi
  contradiction

private theorem zero_disjoint (m : Fin 16) : MaskDisjoint 0 m := by
  intro i hi _
  rw [zero_mask_bit] at hi
  contradiction

/-- The actual row graph: one prescribed forward output zero. -/
abbrev H_L (r : Fin 4) := ZeroGraph (singleMask r) 0

/-- The actual column graph: one prescribed input zero. -/
abbrev H_R (z : Fin 4) := ZeroGraph 0 (singleMask z)

/-- Identify only the named forward maps; do not expand concrete AES. -/
theorem boundary_apply_forward (v : WordState) : boundary v = wordMixAddEquiv v := by
  change AESPaper.GroupedRecurrence.boundary v = wordMixAddEquiv v
  rw [AESPaper.BoundaryZeros.boundary_eq_wordMixAddEquiv]

/-- The row domain is exactly the claimed forward one-zero hyperplane. -/
theorem left_graph_iff (r : Fin 4) (v : WordState) :
    graphPrescribed boundary (singleMask r) 0 (0 : WordState) 0 v ↔
      wordMixAddEquiv v r = 0 := by
  constructor
  · intro h
    have hr := h.1 r ((singleMask_bit r r).mpr rfl)
    change boundary v r = 0 at hr
    rwa [boundary_apply_forward] at hr
  · intro h
    constructor
    · intro i hi
      have hir : i = r := (singleMask_bit r i).mp hi
      subst i
      change boundary v r = 0
      rw [boundary_apply_forward]
      exact h
    · intro i hi
      rw [zero_mask_bit] at hi
      contradiction

/-- The column domain is exactly the claimed literal input-zero hyperplane. -/
theorem right_graph_iff (z : Fin 4) (x : WordState) :
    graphPrescribed boundary 0 (singleMask z) (0 : WordState) 0 x ↔ x z = 0 := by
  constructor
  · intro h
    exact h.2 z ((singleMask_bit z z).mpr rfl)
  · intro h
    constructor
    · intro i hi
      rw [zero_mask_bit] at hi
      contradiction
    · intro i hi
      have hiz : i = z := (singleMask_bit z i).mp hi
      subst i
      exact h

theorem left_constraint (r : Fin 4) (v : H_L r) : wordMixAddEquiv v.val r = 0 :=
  (left_graph_iff r v.val).mp v.property

theorem right_constraint (z : Fin 4) (x : H_R z) : x.val z = 0 :=
  (right_graph_iff z x.val).mp x.property

private def row0 : MaskCoordinates (7 : Fin 16) := ⟨0, by decide⟩
private def row1 : MaskCoordinates (7 : Fin 16) := ⟨1, by decide⟩
private def row2 : MaskCoordinates (7 : Fin 16) := ⟨2, by decide⟩

private def column1 : MaskCoordinates (14 : Fin 16) := ⟨1, by decide⟩
private def column2 : MaskCoordinates (14 : Fin 16) := ⟨2, by decide⟩
private def column3 : MaskCoordinates (14 : Fin 16) := ⟨3, by decide⟩

private theorem row_cover : ∀ i : MaskCoordinates (7 : Fin 16),
    i = row0 ∨ i = row1 ∨ i = row2 := by decide

private theorem column_cover : ∀ i : MaskCoordinates (14 : Fin 16),
    i = column1 ∨ i = column2 ∨ i = column3 := by decide

/-- Reorder the literal row triple as one created and two shared labels. -/
private def rowTupleEquiv (V : Type*) :
    (MaskCoordinates (7 : Fin 16) → V) ≃ ((Unit → V) × (Fin 2 → V)) where
  toFun f := (fun _ => f row0, ![f row1, f row2])
  invFun p i := if i.val = 0 then p.1 () else if i.val = 1 then p.2 0 else p.2 1
  left_inv f := by
    funext i
    rcases row_cover i with h | h | h <;> subst i <;> simp [row0, row1, row2]
  right_inv p := by
    apply Prod.ext
    · funext i
      cases i
      simp [row0, row1, row2]
    · funext i
      fin_cases i <;> simp [row0, row1, row2]

/-- Reorder the literal column triple as two shared and one contracted label. -/
private def columnTupleEquiv (V : Type*) :
    (MaskCoordinates (14 : Fin 16) → V) ≃ ((Fin 2 → V) × (Unit → V)) where
  toFun f := (![f column1, f column2], fun _ => f column3)
  invFun p i := if i.val = 1 then p.1 0 else if i.val = 2 then p.1 1 else p.2 ()
  left_inv f := by
    funext i
    rcases column_cover i with h | h | h <;> subst i <;>
      simp [column1, column2, column3]
  right_inv p := by
    apply Prod.ext
    · funext i
      fin_cases i <;> simp [column1, column2, column3]
    · funext i
      cases i
      simp [column1, column2, column3]

/-- Literal input positions (0,1,2) are information coordinates on H_L.
The fixed output coordinate r may be any of the four names. -/
def rowLabels (r : Fin 4) : H_L r ≃ ((Unit → AES.Word) × (Fin 2 → AES.Word)) :=
  (informationEquiv boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
    (singleMask r) 0 0 7 0 0 (disjoint_zero (singleMask r)) (zero_disjoint 7)
    (by rw [singleMask_size, zero_mask_size, row_mask_size])).trans
      ((inputObservedEquiv 7 AES.Word).trans (rowTupleEquiv AES.Word))

/-- Literal forward output positions (1,2,3) are information coordinates on H_R.
The fixed input coordinate z may be any of the four names. -/
def columnLabels (z : Fin 4) : H_R z ≃ ((Fin 2 → AES.Word) × (Unit → AES.Word)) :=
  (informationEquiv boundary AESPaper.ActivityKernel.aesBoundary_zeroMDS
    0 (singleMask z) 14 0 0 0 (zero_disjoint 14) (disjoint_zero (singleMask z))
    (by rw [singleMask_size, zero_mask_size, column_mask_size])).trans
      ((outputObservedEquiv 14 AES.Word).trans (columnTupleEquiv AES.Word))

@[simp] theorem rowLabels_first (r : Fin 4) (v : H_L r) :
    (rowLabels r v).1 () = v.val 0 := rfl

@[simp] theorem rowLabels_shared_zero (r : Fin 4) (v : H_L r) :
    (rowLabels r v).2 0 = v.val 1 := rfl

@[simp] theorem rowLabels_shared_one (r : Fin 4) (v : H_L r) :
    (rowLabels r v).2 1 = v.val 2 := rfl

@[simp] theorem columnLabels_shared_zero (z : Fin 4) (x : H_R z) :
    (columnLabels z x).1 0 = wordMixAddEquiv x.val 1 := by
  change boundary x.val 1 = wordMixAddEquiv x.val 1
  rw [boundary_apply_forward]

@[simp] theorem columnLabels_shared_one (z : Fin 4) (x : H_R z) :
    (columnLabels z x).1 1 = wordMixAddEquiv x.val 2 := by
  change boundary x.val 2 = wordMixAddEquiv x.val 2
  rw [boundary_apply_forward]

@[simp] theorem columnLabels_last (z : Fin 4) (x : H_R z) :
    (columnLabels z x).2 () = wordMixAddEquiv x.val 3 := by
  change boundary x.val 3 = wordMixAddEquiv x.val 3
  rw [boundary_apply_forward]

/-- The two shared labels refer literally to physical positions 1 and 2. -/
def sharedPosition (i : Fin 2) : Fin 4 := i.succ.castSucc

@[simp] theorem sharedPosition_zero : sharedPosition 0 = 1 := rfl
@[simp] theorem sharedPosition_one : sharedPosition 1 = 2 := rfl

/-- The actual physical four-middle kernel, with possibly different local maps. -/
def tensorKernel {r z : Fin 4} (K : Fin 4 → AES.Word → AES.Word → ℝ)
    (v : H_L r) (x : H_R z) : ℝ :=
  ∏ i : Fin 4, K i (v.val i) (wordMixAddEquiv x.val i)

-- Both reconstruction functions retain their WHOLE three-coordinate label.
def leftCode (z : Fin 4) (x : (Fin 2 → AES.Word) × (Unit → AES.Word))
    (_ : Unit) : AES.Word := wordMixAddEquiv ((columnLabels z).symm x).val 0

def rightCode (r : Fin 4) (y : (Unit → AES.Word) × (Fin 2 → AES.Word))
    (_ : Unit) : AES.Word := ((rowLabels r).symm y).val 3

/-- Exact four-factor identification; no code/kernel equality is an assumption. -/
theorem tensorKernel_eq_overlap (r z : Fin 4)
    (K : Fin 4 → AES.Word → AES.Word → ℝ)
    (y : (Unit → AES.Word) × (Fin 2 → AES.Word))
    (x : (Fin 2 → AES.Word) × (Unit → AES.Word)) :
    tensorKernel K ((rowLabels r).symm y) ((columnLabels z).symm x) =
      AES8.InformationOverlap.kernel (leftCode z) (rightCode r)
        (fun _ : Unit => K 0) (fun i : Fin 2 => K (sharedPosition i))
        (fun _ : Unit => K 3) y x := by
  have hY0 : ((rowLabels r).symm y).val 0 = y.1 () := by
    simpa only [rowLabels_first] using
      congrArg (fun p : (Unit → AES.Word) × (Fin 2 → AES.Word) => p.1 ())
        ((rowLabels r).apply_symm_apply y)
  have hY1 : ((rowLabels r).symm y).val 1 = y.2 0 := by
    simpa only [rowLabels_shared_zero] using
      congrArg (fun p : (Unit → AES.Word) × (Fin 2 → AES.Word) => p.2 0)
        ((rowLabels r).apply_symm_apply y)
  have hY2 : ((rowLabels r).symm y).val 2 = y.2 1 := by
    simpa only [rowLabels_shared_one] using
      congrArg (fun p : (Unit → AES.Word) × (Fin 2 → AES.Word) => p.2 1)
        ((rowLabels r).apply_symm_apply y)
  have hX1 : wordMixAddEquiv ((columnLabels z).symm x).val 1 = x.1 0 := by
    simpa only [columnLabels_shared_zero] using
      congrArg (fun p : (Fin 2 → AES.Word) × (Unit → AES.Word) => p.1 0)
        ((columnLabels z).apply_symm_apply x)
  have hX2 : wordMixAddEquiv ((columnLabels z).symm x).val 2 = x.1 1 := by
    simpa only [columnLabels_shared_one] using
      congrArg (fun p : (Fin 2 → AES.Word) × (Unit → AES.Word) => p.1 1)
        ((columnLabels z).apply_symm_apply x)
  have hX3 : wordMixAddEquiv ((columnLabels z).symm x).val 3 = x.2 () := by
    simpa only [columnLabels_last] using
      congrArg (fun p : (Fin 2 → AES.Word) × (Unit → AES.Word) => p.2 ())
        ((columnLabels z).apply_symm_apply x)
  simp only [tensorKernel, Fin.prod_univ_four, AES8.InformationOverlap.kernel,
    Fintype.prod_unique, Fin.prod_univ_two, sharedPosition_zero, sharedPosition_one,
    leftCode, rightCode]
  rw [hY0, hY1, hY2, hX1, hX2, hX3]
  ring

/-- Reindex the exact physical action, preserving arbitrary signed joint input. -/
theorem tensor_action_eq_overlap (r z : Fin 4)
    (K : Fin 4 → AES.Word → AES.Word → ℝ) (f : H_R z → ℝ)
    (y : (Unit → AES.Word) × (Fin 2 → AES.Word)) :
    action (tensorKernel K) f ((rowLabels r).symm y) =
      action (AES8.InformationOverlap.kernel (leftCode z) (rightCode r)
        (fun _ : Unit => K 0) (fun i : Fin 2 => K (sharedPosition i))
        (fun _ : Unit => K 3)) (fun x => f ((columnLabels z).symm x)) y := by
  unfold action
  rw [← (columnLabels z).symm.sum_comp (fun x : H_R z =>
    tensorKernel K ((rowLabels r).symm y) x * f x)]
  apply Finset.sum_congr rfl
  intro x _
  rw [tensorKernel_eq_overlap r z K y x]

/-- Four-middle graph energy: one column, two shared operators, one row.
There is no sign, product-law, independence, or fiber-constancy premise. -/
theorem tensor_energy (r z : Fin 4) (K : Fin 4 → AES.Word → AES.Word → ℝ)
    (delta nu : ℝ) (hd : 0 ≤ delta)
    (hA : ∀ x, (∑ y, K 0 y x ^ 2) ≤ delta)
    (hB : ∀ i : Fin 2, ∀ g, (∑ y, action (K (sharedPosition i)) g y ^ 2) ≤
      nu ^ 2 * ∑ x, g x ^ 2)
    (hE : ∀ y, (∑ x, K 3 y x ^ 2) ≤ delta) (f : H_R z → ℝ) :
    (∑ v : H_L r, action (tensorKernel K) f v ^ 2) ≤
      delta ^ 2 * nu ^ 4 * ∑ x : H_R z, f x ^ 2 := by
  let eX := columnLabels z
  let eY := rowLabels r
  rw [← eY.symm.sum_comp (fun v : H_L r => action (tensorKernel K) f v ^ 2)]
  change (∑ y, action (tensorKernel K) f ((rowLabels r).symm y) ^ 2) ≤ _
  simp_rw [tensor_action_eq_overlap r z K f]
  have hb := AES8.InformationOverlap.information_overlap_energy
    (leftCode z) (rightCode r)
    (fun _ : Unit => K 0) (fun i : Fin 2 => K (sharedPosition i))
    (fun _ : Unit => K 3) delta hd (fun _ : Fin 2 => nu)
    (fun _ x => hA x) (fun i g => hB i g) (fun _ y => hE y)
    (fun x => f (eX.symm x))
  have hp : (∏ _i : Fin 2, nu) ^ 2 = nu ^ 4 := by
    rw [Fin.prod_univ_two]
    ring
  simp only [Fintype.card_unique, hp] at hb
  rw [eX.symm.sum_comp (fun x => f x ^ 2)] at hb
  exact hb

theorem tensor_l2 (r z : Fin 4) (K : Fin 4 → AES.Word → AES.Word → ℝ)
    (delta nu : ℝ) (hd : 0 ≤ delta)
    (hA : ∀ x, (∑ y, K 0 y x ^ 2) ≤ delta)
    (hB : ∀ i : Fin 2, ∀ g, (∑ y, action (K (sharedPosition i)) g y ^ 2) ≤
      nu ^ 2 * ∑ x, g x ^ 2)
    (hE : ∀ y, (∑ x, K 3 y x ^ 2) ≤ delta) (f : H_R z → ℝ) :
    l2 (action (tensorKernel (r := r) (z := z) K) f) ≤
      (delta * nu ^ 2) * l2 f := by
  apply l2_le_of_energy _ f (delta * nu ^ 2) (mul_nonneg hd (sq_nonneg nu))
  rw [show (delta * nu ^ 2) ^ 2 = delta ^ 2 * nu ^ 4 by ring]
  exact tensor_energy r z K delta nu hd hA hB hE f

/-- Actual forward four-middle residual kernel on the exact graph domains. -/
def actualKernel {r z : Fin 4} : H_L r → H_R z → ℝ :=
  tensorKernel (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)

theorem actualKernel_eq_forward (r z : Fin 4) (v : H_L r) (x : H_R z) :
    actualKernel v x =
      ∏ i : Fin 4, residualMatrix AES.wordSuperboxKernel 0
        (v.val i) (wordMixAddEquiv x.val i) := rfl

theorem actualKernel_eq_wordMix (r z : Fin 4) (v : H_L r) (x : H_R z) :
    actualKernel v x =
      ∏ i : Fin 4, residualMatrix AES.wordSuperboxKernel 0
        (v.val i) (AES.wordMix x.val i) := by
  simpa only [AESConcrete.WordCrossZero.wordMixAddEquiv_apply] using
    actualKernel_eq_forward r z v x

/-- Actual AES energy, using already proved local resources rather than assumptions.
`columnCap = 2/(15*q)` and `rho = 10399/(1000*65536)`. -/
theorem actual_energy (r z : Fin 4) (f : H_R z → ℝ) :
    (∑ v : H_L r, action actualKernel f v ^ 2) ≤
      OneSourceEventMoment.columnCap ^ 2 * SharpWordNorm.rho ^ 4 *
        ∑ x : H_R z, f x ^ 2 := by
  exact tensor_energy r z
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    OneSourceEventMoment.columnCap SharpWordNorm.rho
    (by norm_num [OneSourceEventMoment.columnCap, AESPaper.StartingWord.q])
    OneSourceEventMoment.residual_column_le
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g)
    OneSourceEventMoment.residual_row_le f

theorem actual_l2 (r z : Fin 4) (f : H_R z → ℝ) :
    l2 (action (actualKernel (r := r) (z := z)) f) ≤
      (OneSourceEventMoment.columnCap * SharpWordNorm.rho ^ 2) * l2 f := by
  exact tensor_l2 r z
    (fun _ : Fin 4 => residualMatrix AES.wordSuperboxKernel 0)
    OneSourceEventMoment.columnCap SharpWordNorm.rho
    (by norm_num [OneSourceEventMoment.columnCap, AESPaper.StartingWord.q])
    OneSourceEventMoment.residual_column_le
    (fun _ g => SharpDegreeStep.word_superbox_residual_energy g)
    OneSourceEventMoment.residual_row_le f

end AES8.ReturnFourMiddle
