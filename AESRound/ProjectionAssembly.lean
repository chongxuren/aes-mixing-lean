import AESRound.OperatorBridge

/-!
# Algebraic assembly of a projected evolution with memory

A finite family of continuous linear projections and a remainder resolve
the identity on the common ambient space. The remainder need not vanish:
it is enough that every observed projection kills its next update. These
pointwise identities construct the exact `OperatorBridge.ProjectionSystem`.

The Boolean flag `isLow j` partitions source indices. The return map passes
through the sum of the high projections between two updates. Its equality
with a sum of compositions of step blocks is proved separately below.

This is a generic candidate, not an AES instantiation. Completeness of the
actual AES projections, the actual zero component, and all operator norm
caps remain separate obligations. No restriction to a nonzero subspace,
pairwise orthogonality, or idempotence of the remainder is assumed.
Constructive mathematics only; no attacks or historical/manuscript edits.
-/

noncomputable section

namespace AESRound.ProjectionAssembly
open scoped BigOperators

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The algebraic data used by the assembly. The completeness law retains
the actual remainder; the invisibility law applies after one update. -/
structure Decomposition (ι E : Type*) [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] where
  project : ι → E →L[ℝ] E
  update : E →L[ℝ] E
  remainder : E →L[ℝ] E
  complete : ∀ v, (∑ i, project i v) + remainder v = v
  project_idempotent : ∀ i v, project i (project i v) = project i v
  remainder_invisible : ∀ v i, project i (update (remainder v)) = 0

namespace Decomposition

variable (G : Decomposition ι E)

def step (i j : ι) : E →L[ℝ] E :=
  (G.project i).comp (G.update.comp (G.project j))

/-- The flag is attached to the source index, as required by the low
matrix in the recurrence interface. -/
def low (isLow : ι → Bool) (i j : ι) : E →L[ℝ] E :=
  if isLow j then G.step i j else 0

def highProject (isLow : ι → Bool) : E →L[ℝ] E :=
  ∑ k, if isLow k then 0 else G.project k

def ret (isLow : ι → Bool) (i j : ι) : E →L[ℝ] E :=
  (G.project i).comp
    (G.update.comp ((G.highProject isLow).comp
      (G.update.comp (G.project j))))

@[simp] theorem step_apply (i j : ι) (v : E) :
    G.step i j v = G.project i (G.update (G.project j v)) := rfl

theorem low_apply (isLow : ι → Bool) (i j : ι) (v : E) :
    G.low isLow i j v =
      if isLow j then G.project i (G.update (G.project j v)) else 0 := by
  unfold low
  split_ifs <;> rfl

theorem highProject_apply (isLow : ι → Bool) (v : E) :
    G.highProject isLow v = ∑ k, if isLow k then 0 else G.project k v := by
  simp only [highProject, sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> rfl

@[simp] theorem ret_apply (isLow : ι → Bool) (i j : ι) (v : E) :
    G.ret isLow i j v =
      G.project i (G.update (G.highProject isLow (G.update (G.project j v)))) := rfl

/-- Any continuous linear observation which kills the updated remainder
admits this exact expansion. No norm inequality is a premise. -/
theorem observe_update_sum (observe : E →L[ℝ] E)
    (hobserve : ∀ v, observe (G.update (G.remainder v)) = 0) (v : E) :
    observe (G.update v) = ∑ j, observe (G.update (G.project j v)) := by
  calc
    observe (G.update v) =
        observe (G.update ((∑ j, G.project j v) + G.remainder v)) :=
      congrArg (fun w => observe (G.update w)) (G.complete v).symm
    _ = ∑ j, observe (G.update (G.project j v)) := by
      rw [map_add, map_add, hobserve, add_zero]
      simp only [map_sum]

theorem projected_update_sum (v : E) (i : ι) :
    G.project i (G.update v) =
      ∑ j, G.project i (G.update (G.project j v)) :=
  G.observe_update_sum (G.project i) (fun w => G.remainder_invisible w i) v

/-- Reapplying the source projection changes no block, by its own
idempotence. Pairwise orthogonality is not needed. -/
theorem step_identity (v : E) (i : ι) :
    G.project i (G.update v) = ∑ j, G.step i j (G.project j v) := by
  simpa only [step_apply, G.project_idempotent] using G.projected_update_sum v i

theorem highProject_update_remainder_zero (isLow : ι → Bool) (v : E) :
    G.highProject isLow (G.update (G.remainder v)) = 0 := by
  rw [G.highProject_apply]
  apply Finset.sum_eq_zero
  intro k _
  split_ifs
  · rfl
  · exact G.remainder_invisible v k

theorem highProject_update_sum (isLow : ι → Bool) (v : E) :
    G.highProject isLow (G.update v) =
      ∑ j, G.highProject isLow (G.update (G.project j v)) :=
  G.observe_update_sum (G.highProject isLow)
    (G.highProject_update_remainder_zero isLow) v

/-- Partition the current projected update into low source blocks and
the actual update of the high projection sum. -/
theorem low_high_identity (isLow : ι → Bool) (v : E) (i : ι) :
    G.project i (G.update v) =
      (∑ j, G.low isLow i j (G.project j v)) +
        G.project i (G.update (G.highProject isLow v)) := by
  rw [G.projected_update_sum v i]
  symm
  rw [G.highProject_apply]
  simp only [map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases h : isLow j <;>
    simp [low_apply, h, G.project_idempotent]

/-- The updated remainder contributes no high return. This is where the
invisibility law is used a second time in the memory decomposition. -/
theorem return_sum_identity (isLow : ι → Bool) (v : E) (i : ι) :
    G.project i (G.update (G.highProject isLow (G.update v))) =
      ∑ j, G.ret isLow i j (G.project j v) := by
  rw [G.highProject_update_sum isLow v]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [ret_apply, G.project_idempotent]

theorem memory_identity (isLow : ι → Bool) (v : E) (i : ι) :
    G.project i (G.update (G.update v)) =
      (∑ j, G.low isLow i j (G.project j (G.update v))) +
        ∑ j, G.ret isLow i j (G.project j v) := by
  rw [G.low_high_identity isLow (G.update v) i]
  rw [G.return_sum_identity isLow v i]

/-- Exact high-index expansion of a return. The middle source projection
appears only once on the left and twice in the composed step blocks;
its idempotence supplies that equality. -/
theorem ret_apply_eq_sum_steps (isLow : ι → Bool) (i j : ι) (v : E) :
    G.ret isLow i j v =
      ∑ k, if isLow k then 0 else G.step i k (G.step k j v) := by
  rw [ret_apply, G.highProject_apply]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  cases h : isLow k <;>
    simp [h, step_apply, G.project_idempotent]

theorem ret_eq_sum_step_comp_step (isLow : ι → Bool) (i j : ι) :
    G.ret isLow i j =
      ∑ k, if isLow k then 0 else (G.step i k).comp (G.step k j) := by
  ext v
  rw [G.ret_apply_eq_sum_steps]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  cases h : isLow k <;>
    simp [h, ContinuousLinearMap.comp_apply]

/-- The exact algebraic assembly. Numerical step, low, and return caps
are deliberately absent and must be proved for an actual instantiation. -/
def toProjectionSystem (isLow : ι → Bool) : OperatorBridge.ProjectionSystem ι E where
  project := G.project
  update := G.update
  step := G.step
  low := G.low isLow
  ret := G.ret isLow
  step_identity := G.step_identity
  memory_identity := G.memory_identity isLow

end Decomposition
end AESRound.ProjectionAssembly
