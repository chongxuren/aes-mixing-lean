import AES8.Math.PaperRestrictedSource
import Mathlib.Data.Finset.Sum

/-!
# Literal graph coordinates for additive diffusion

Inputs and outputs occupy the two distinct copies of the original coordinate
type. The prescribed graph coordinates are exactly the inactive input zeros
and the specified output zeros. This module proves their equivalence with
restrictions on actual input tuples, and the paper's exact cardinal arithmetic.
No source parameterization or marginal estimate is an assumption. Constructive
mathematics only; no attacks, manuscript edits, or numerical instantiation.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedDiffusion
open PaperMDSGram PaperMDSFiber

attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The actual additive diffusion graph, with physical input/output labels. -/
def graph (L : (I → V) →+ (I → V)) : AddSubgroup ((I ⊕ I) → V) where
  carrier := {c | L (fun i => c (Sum.inl i)) = fun i => c (Sum.inr i)}
  zero_mem' := by
    change L 0 = 0
    exact map_zero L
  add_mem' := by
    intro c d hc hd
    change L ((fun i => c (Sum.inl i)) + (fun i => d (Sum.inl i))) =
      (fun i => c (Sum.inr i)) + (fun i => d (Sum.inr i))
    rw [map_add, hc, hd]
  neg_mem' := by
    intro c hc
    change L (-(fun i => c (Sum.inl i))) = -(fun i => c (Sum.inr i))
    rw [map_neg, hc]

/-- The graph is equivalent to the original input tuples, by input projection. -/
def graphEquiv (L : (I → V) →+ (I → V)) : (I → V) ≃ graph L where
  toFun x := ⟨Sum.elim x (L x), rfl⟩
  invFun c := fun i => c.val (Sum.inl i)
  left_inv _ := rfl
  right_inv c := by
    apply Subtype.ext
    funext i
    cases i with
    | inl i => rfl
    | inr i => exact congrFun c.property i

/-- The fixed labels are inactive inputs and the specified output zeros. -/
def fixed (active zeros : Finset I) : Finset (I ⊕ I) := activeᶜ.disjSum zeros

/-- Only active original input laws supply probability factors. -/
def inputs (active : Finset I) : Finset (I ⊕ I) := active.disjSum ∅

/-- Physical output labels for the marked original output coordinates. -/
def outputs (observed : Finset I) : Finset (I ⊕ I) := (∅ : Finset I).disjSum observed

@[simp] theorem mem_fixed_inl (active zeros : Finset I) (i : I) :
    Sum.inl i ∈ fixed active zeros ↔ i ∉ active := by simp [fixed]

@[simp] theorem mem_fixed_inr (active zeros : Finset I) (i : I) :
    Sum.inr i ∈ fixed active zeros ↔ i ∈ zeros := by simp [fixed]

@[simp] theorem mem_inputs_inl (active : Finset I) (i : I) :
    Sum.inl i ∈ inputs active ↔ i ∈ active := by simp [inputs]

@[simp] theorem mem_inputs_inr (active : Finset I) (i : I) :
    Sum.inr i ∉ inputs active := by simp [inputs]

@[simp] theorem mem_outputs_inl (observed : Finset I) (i : I) :
    Sum.inl i ∉ outputs observed := by simp [outputs]

@[simp] theorem mem_outputs_inr (observed : Finset I) (i : I) :
    Sum.inr i ∈ outputs observed ↔ i ∈ observed := by simp [outputs]

@[simp] theorem inputs_card (active : Finset I) : (inputs active).card = active.card := by
  simp [inputs]

@[simp] theorem outputs_card (observed : Finset I) :
    (outputs observed).card = observed.card := by simp [outputs]

theorem fixed_card (active zeros : Finset I) :
    (fixed active zeros).card = Fintype.card I - active.card + zeros.card := by
  simp [fixed, Finset.card_compl]

theorem fixed_inputs_disjoint (active zeros : Finset I) :
    Disjoint (fixed active zeros) (inputs active) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  cases i with
  | inl i => exact (mem_fixed_inl active zeros i).mp hi ((mem_inputs_inl active i).mp hj)
  | inr i => exact mem_inputs_inr active i hj

theorem inputs_outputs_disjoint (active observed : Finset I) :
    Disjoint (inputs active) (outputs observed) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  cases i with
  | inl i => exact mem_outputs_inl observed i hj
  | inr i => exact mem_inputs_inr active i hi

theorem fixed_outputs_disjoint (active zeros observed : Finset I)
    (hd : Disjoint zeros observed) :
    Disjoint (fixed active zeros) (outputs observed) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  cases i with
  | inl i => exact mem_outputs_inl observed i hj
  | inr i =>
    exact Finset.disjoint_left.mp hd
      ((mem_fixed_inr active zeros i).mp hi) ((mem_outputs_inr observed i).mp hj)

/-- The actual original tuples retained by the zero event. -/
def admissible (L : (I → V) →+ (I → V)) (active zeros : Finset I) (x : I → V) : Prop :=
  (∀ i ∉ active, x i = 0) ∧ ∀ i ∈ zeros, L x i = 0

/-- Prescribing the graph coordinates is exactly prescribing the intended
input and output zeros on the original diffusion experiment. -/
def fiberEquiv (L : (I → V) →+ (I → V)) (active zeros : Finset I) :
    Fiber (graph L) (fixed active zeros) 0 ≃
      {x : I → V // admissible L active zeros x} where
  toFun c := ⟨fun i => c.val.val (Sum.inl i), by
    constructor
    · intro i hi
      exact c.property (Sum.inl i) (by simpa using hi)
    · intro i hi
      exact (congrFun c.val.property i).trans
        (c.property (Sum.inr i) (by simpa using hi))⟩
  invFun x := ⟨graphEquiv L x.val, by
    intro i hi
    cases i with
    | inl i => exact x.property.1 i (by simpa using hi)
    | inr i => exact x.property.2 i (by simpa using hi)⟩
  left_inv c := by
    apply Subtype.ext
    exact (graphEquiv L).apply_symm_apply c.val
  right_inv x := Subtype.ext rfl

/-- Original input tuple represented by a point of the actual graph fiber. -/
def original (L : (I → V) →+ (I → V)) (active zeros : Finset I)
    (c : Fiber (graph L) (fixed active zeros) 0) : I → V :=
  (fiberEquiv L active zeros c).val

@[simp] theorem original_apply (L : (I → V) →+ (I → V))
    (active zeros : Finset I) (c : Fiber (graph L) (fixed active zeros) 0) (i : I) :
    original L active zeros c i = c.val.val (Sum.inl i) := rfl

theorem original_output (L : (I → V) →+ (I → V)) (active zeros : Finset I)
    (c : Fiber (graph L) (fixed active zeros) 0) (i : I) :
    L (original L active zeros c) i = c.val.val (Sum.inr i) :=
  congrFun c.val.property i

/-- Exact shortened dimension and exactly `z` omitted source-law factors. -/
theorem cardinal_substitution (active zeros : Finset I) (hz : zeros.card ≤ active.card) :
    (fixed active zeros).card ≤ Fintype.card I ∧
    Fintype.card I - (fixed active zeros).card = active.card - zeros.card ∧
    active.card - (Fintype.card I - (fixed active zeros).card) = zeros.card := by
  have ha : active.card ≤ Fintype.card I := Finset.card_le_univ active
  rw [fixed_card]
  omega

/-- The MDS fiber cardinality now concerns actual original input tuples. -/
theorem actual_fiber_card (L : (I → V) →+ (I → V))
    (hMDS : IsMDS (graph L) (Fintype.card I)) (active zeros : Finset I)
    (hz : zeros.card ≤ active.card) :
    Fintype.card {x : I → V // admissible L active zeros x} =
      Fintype.card V ^ (active.card - zeros.card) := by
  have hc := cardinal_substitution active zeros hz
  rw [← Fintype.card_congr (fiberEquiv L active zeros)]
  rw [prescribed_card (graph L) (Fintype.card I) (by simp) hMDS
    (fixed active zeros) hc.1 0, hc.2.1]

end AES8.PaperRestrictedDiffusion
