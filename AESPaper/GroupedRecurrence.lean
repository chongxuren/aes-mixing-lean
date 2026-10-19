import AESPaper.GroupedLaw

/-!
# Exact recurrence of the concrete grouped AES difference law

`groupedLaw n a` is the physical difference law after `2*n+2` rounds,
in the output coordinates fixed by `GroupedLaw`.  `H` is the actual four-word
parallel superbox channel.  `Pi` pushes a law forward by the inter-word
boundary permutation.  Its action therefore evaluates the old law at the
INVERSE permutation; both directions are stated explicitly below.

Dependencies: this project's `GroupedLaw.grouped_superbox_formula`, and the
shared concrete `AES.superboxLaw_columns`, physical law operations and
ShiftRows/MixColumns/transpose additive equivalences imported by GroupedLaw.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000
noncomputable section

namespace AESPaper.GroupedRecurrence
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (groupedLaw grouped_superbox_formula)

/-- Reindex a physical-state function into the four column-word coordinates. -/
def columns (f : AES.State → ℝ) : AES.WordState → ℝ := fun x => f (transposeState x)

/-- Forward boundary map, in execution order: transpose, SR, MC, SR, untranspose. -/
def boundary : AES.WordState ≃+ AES.WordState :=
  transposeState.trans (shiftRowsEquiv.trans
    (mixColumnsEquiv.trans (shiftRowsEquiv.trans transposeState.symm)))

theorem boundary_apply (x : AES.WordState) :
    boundary x = transposeState.symm
      (shiftRowsEquiv (mixColumnsEquiv (shiftRowsEquiv (transposeState x)))) := rfl

theorem boundary_symm_apply (x : AES.WordState) :
    boundary.symm x = transposeState.symm
      (shiftRowsEquiv.symm (mixColumnsEquiv.symm (shiftRowsEquiv.symm (transposeState x)))) := rfl

theorem boundary_transpose_symm (x : AES.WordState) :
    transposeState (boundary.symm x) =
      shiftRowsEquiv.symm (mixColumnsEquiv.symm (shiftRowsEquiv.symm (transposeState x))) := by
  rw [boundary_symm_apply, transposeState.apply_symm_apply]

/-- The actual word-parallel superbox channel, on arbitrary joint functions. -/
def H : (AES.WordState → ℝ) → (AES.WordState → ℝ) :=
  action AES.parallelSuperboxKernel

/-- Forward transport of laws uses the inverse of the forward boundary map. -/
def Pi : (AES.WordState → ℝ) → (AES.WordState → ℝ) :=
  lawRelabel boundary.toEquiv

theorem Pi_apply (f : AES.WordState → ℝ) (x : AES.WordState) :
    Pi f x = f (boundary.symm x) := rfl

theorem superbox_columns (f : AES.State → ℝ) :
    columns (superboxLaw f) = H (columns f) := by
  funext x
  exact superboxLaw_columns f x

theorem interSuperbox_columns (f : AES.State → ℝ) :
    columns (interSuperboxLaw f) = Pi (columns f) := by
  funext x
  change f (shiftRowsEquiv.symm (mixColumnsEquiv.symm
      (shiftRowsEquiv.symm (transposeState x)))) = f (transposeState (boundary.symm x))
  rw [boundary_transpose_symm]

theorem differencePoint_columns (a : AES.State) :
    columns (differencePoint a) = differencePoint (transposeState.symm a) := by
  funext x
  have he : transposeState x = a ↔ x = transposeState.symm a := by
    constructor
    · intro h
      apply transposeState.injective
      simpa only [transposeState.apply_symm_apply] using h
    · rintro rfl
      exact transposeState.apply_symm_apply a
  have he' : a = transposeState x ↔ transposeState.symm a = x := by
    simpa only [eq_comm] using he
  simp only [columns, differencePoint, he']

/-- The physical-state expression already proved by the grouping identity. -/
def stage (n : ℕ) (a : AES.State) : AES.State → ℝ :=
  ((interSuperboxLaw ∘ superboxLaw)^[n]) (differencePoint (shiftRows a))

theorem stage_succ (n : ℕ) (a : AES.State) :
    stage (n+1) a = interSuperboxLaw (superboxLaw (stage n a)) := by
  unfold stage
  rw [Function.iterate_succ_apply', Function.comp_apply]

theorem groupedLaw_eq_columns (n : ℕ) (a : AES.State) :
    groupedLaw n a = columns (superboxLaw (stage n a)) := by
  funext x
  exact grouped_superbox_formula n a x

/-- Exact starting law after two physical rounds, including the input ShiftRows. -/
theorem groupedLaw_initial (a : AES.State) :
    groupedLaw 0 a = H (differencePoint (transposeState.symm (shiftRows a))) := by
  rw [groupedLaw_eq_columns]
  change columns (superboxLaw (differencePoint (shiftRows a))) = _
  rw [superbox_columns, differencePoint_columns]

/-- Appending two rounds acts by the actual `H Pi`, in this order. -/
theorem groupedLaw_succ (n : ℕ) (a : AES.State) :
    groupedLaw (n+1) a = H (Pi (groupedLaw n a)) := by
  rw [groupedLaw_eq_columns (n+1) a, stage_succ,
    superbox_columns, interSuperbox_columns, ← groupedLaw_eq_columns n a]

def step : (AES.WordState → ℝ) → (AES.WordState → ℝ) := H ∘ Pi

theorem groupedLaw_step (n : ℕ) (a : AES.State) :
    groupedLaw (n+1) a = step (groupedLaw n a) := by
  unfold step
  rw [Function.comp_apply, groupedLaw_succ]

/-- Appending four rounds retains both boundary permutations. -/
theorem groupedLaw_add_two (n : ℕ) (a : AES.State) :
    groupedLaw (n+2) a = H (Pi (H (Pi (groupedLaw n a)))) := by
  rw [show n+2 = (n+1)+1 by omega, groupedLaw_succ, groupedLaw_succ]

theorem groupedLaw_four_round_step (n : ℕ) (a : AES.State) :
    groupedLaw (n+2) a = (step^[2]) (groupedLaw n a) := by
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    step, Function.comp_apply] using groupedLaw_add_two n a

/-- Arbitrarily many grouped extensions, derived solely from the one-step identity. -/
theorem groupedLaw_add (n m : ℕ) (a : AES.State) :
    groupedLaw (n+m) a = (step^[m]) (groupedLaw n a) := by
  induction m with
  | zero => simp only [Nat.add_zero, Function.iterate_zero_apply]
  | succ m ih =>
      rw [Nat.add_succ, groupedLaw_step, Function.iterate_succ_apply', ih]

theorem groupedLaw_iterate (n : ℕ) (a : AES.State) :
    groupedLaw n a = (step^[n])
      (H (differencePoint (transposeState.symm (shiftRows a)))) := by
  simpa only [Nat.zero_add, groupedLaw_initial] using groupedLaw_add 0 n a

/- The stationary law is transported through exactly the same coordinates as
the physical law.  Subtraction below therefore acts on the actual grouped
error, rather than on a separately postulated centered trajectory. -/

theorem columns_uniform :
    columns (uniformExcept (0 : AES.State)) = uniformExcept (0 : AES.WordState) := by
  funext x
  have hz : transposeState x = 0 ↔ x = 0 :=
    map_eq_zero_iff transposeState transposeState.injective
  simp only [columns, uniformExcept, hz]

theorem substituteLaw_uniform :
    substituteLaw (uniformExcept (0 : AES.State)) = uniformExcept 0 :=
  differenceChannel_stationary subBytesPerm

theorem mixLaw_uniform :
    mixLaw (uniformExcept (0 : AES.State)) = uniformExcept 0 :=
  lawRelabel_uniformExcept mixColumnsEquiv.toEquiv 0 (map_zero mixColumnsEquiv)

theorem shiftLaw_uniform :
    shiftLaw (uniformExcept (0 : AES.State)) = uniformExcept 0 :=
  lawRelabel_uniformExcept shiftRowsEquiv.toEquiv 0 (map_zero shiftRowsEquiv)

theorem superboxLaw_uniform :
    superboxLaw (uniformExcept (0 : AES.State)) = uniformExcept 0 := by
  rw [superboxLaw_apply, substituteLaw_uniform, mixLaw_uniform, substituteLaw_uniform]

theorem H_uniform :
    H (uniformExcept (0 : AES.WordState)) = uniformExcept 0 := by
  simpa only [superboxLaw_uniform, columns_uniform] using
    (superbox_columns (uniformExcept (0 : AES.State))).symm

theorem Pi_uniform :
    Pi (uniformExcept (0 : AES.WordState)) = uniformExcept 0 :=
  lawRelabel_uniformExcept boundary.toEquiv 0 (map_zero boundary)

theorem step_uniform :
    step (uniformExcept (0 : AES.WordState)) = uniformExcept 0 := by
  unfold step
  rw [Function.comp_apply, Pi_uniform, H_uniform]

theorem H_sub (f g : AES.WordState → ℝ) : H (f-g) = H f-H g :=
  action_sub AES.parallelSuperboxKernel f g

theorem Pi_sub (f g : AES.WordState → ℝ) : Pi (f-g) = Pi f-Pi g := rfl

theorem step_sub (f g : AES.WordState → ℝ) : step (f-g) = step f-step g := by
  unfold step
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply, Pi_sub, H_sub]

open AESPaper.GroupedLaw (error)

theorem error_eq_sub (n : ℕ) (a : AES.State) :
    error n a = groupedLaw n a-uniformExcept (0 : AES.WordState) := rfl

/-- The actual grouped centered error obeys the same two-round operator. -/
theorem error_step (n : ℕ) (a : AES.State) :
    error (n+1) a = step (error n a) := by
  rw [error_eq_sub (n+1) a, groupedLaw_step, error_eq_sub n a,
    step_sub, step_uniform]

theorem error_add (n m : ℕ) (a : AES.State) :
    error (n+m) a = (step^[m]) (error n a) := by
  induction m with
  | zero => simp only [Nat.add_zero, Function.iterate_zero_apply]
  | succ m ih =>
      rw [Nat.add_succ, error_step, Function.iterate_succ_apply', ih]

/-- Exact four-round recurrence on the same error used by `GroupedLaw.grouped_tv`. -/
theorem error_four_round_step (n : ℕ) (a : AES.State) :
    error (n+2) a = (step^[2]) (error n a) := error_add n 2 a

theorem error_add_two (n : ℕ) (a : AES.State) :
    error (n+2) a = H (Pi (H (Pi (error n a)))) := by
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    step, Function.comp_apply] using error_four_round_step n a

end AESPaper.GroupedRecurrence
