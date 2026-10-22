import AES8.Math.PaperOrthogonalBlockLift
import AES8.Math.PaperActivityArrayBlocks
import AESMixing.DegreeMatrixNorm
import AESMixing.DegreeProjectionBounds

/-!
# Residual-position multiplicity for the actual four-coordinate degree block

Candidate source; diagnostic and review status is recorded in adjacent receipts. The projections and degree components below are the
existing physical definitions. Their orthogonality and the generic block lift
are imported. Only the finite mask regrouping and count are added here.
The alphabet and signed kernel are arbitrary; no AES enumeration is performed.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators

namespace AES8.PaperActivityArrayResidual
open AESMixing PaperActivityArrayBlocks PaperKernelBounds

/-- Residual positions among four coordinates, at the selected degree. -/
abbrev Position (i : Fin 5) := {a : Fin 4 → Bool // degreeIndex a = i}

theorem position_count (i : Fin 5) : Fintype.card (Position i) = Nat.choose 4 i.val := by
  fin_cases i <;> decide

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem component_positions (z : V) (f : (Fin 4 → V) → ℝ) (i : Fin 5) :
    degreeComponent z i f = fun x => ∑ p : Position i, action (productProjection z p.val) f x := by
  classical
  funext x
  unfold degreeComponent groupedFamily
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Physical block with both specified residual-position projections. -/
def positionBlock (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (a b : Fin 4 → Bool) :=
  kernelCompose (productProjection z a) (kernelCompose K (productProjection z b))

def degreeBlock (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5) :=
  kernelCompose (degreeKernel z i) (kernelCompose K (degreeKernel z j))

theorem degreeBlock_action (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (i j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    action (degreeBlock z K i j) f = degreeComponent z i (action K (degreeComponent z j f)) := by
  rw [degreeBlock, kernelCompose_action, kernelCompose_action, degreeKernel_action,
    degreeKernel_action]

theorem block_expansion (z : V) (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (i j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z i (action K (degreeComponent z j f)) =
      fun y => ∑ p : Position i, ∑ q : Position j,
        action (productProjection z p.val) (action K (action (productProjection z q.val) f)) y := by
  rw [component_positions, component_positions, action_sum_family]
  simp_rw [action_sum_family]

/-- The exact square-root binomial factor from actual orthogonal position spaces. -/
theorem degree_l2_bound (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5)
    (c : ℝ) (hc : 0 ≤ c) (f : (Fin 4 → V) → ℝ)
    (hblock : ∀ (p : Position i) (q : Position j),
      l2 (action (productProjection z p.val) (action K (action (productProjection z q.val) f))) ≤
        c * l2 (action (productProjection z q.val) f)) :
    l2 (degreeComponent z i (action K (degreeComponent z j f))) ≤
      c * Real.sqrt ((Nat.choose 4 i.val : ℝ) * Nat.choose 4 j.val) *
        l2 (degreeComponent z j f) := by
  let v := fun q : Position j => action (productProjection z q.val) f
  let w := fun (p : Position i) (q : Position j) =>
    action (productProjection z p.val) (action K (v q))
  have hin (q r : Position j) (hqr : q ≠ r) : (∑ x, v q x * v r x) = 0 :=
    productProjection_orthogonal z hq q.val r.val (fun h => hqr (Subtype.ext h)) f f
  have he (p : Position i) :
      (fun y => ∑ q, w p q y) =
        action (productProjection z p.val) (action K (degreeComponent z j f)) := by
    rw [component_positions, action_sum_family, action_sum_family]
  have hout (p r : Position i) (hpr : p ≠ r) :
      (∑ y, (∑ q, w p q y) * (∑ q, w r q y)) = 0 := by
    have h := productProjection_orthogonal z hq p.val r.val
      (fun h => hpr (Subtype.ext h)) (action K (degreeComponent z j f))
        (action K (degreeComponent z j f))
    rw [← he p, ← he r] at h
    exact h
  have h := PaperOrthogonalBlockLift.norm_le v w c hc hblock hin hout
  rw [position_count, position_count] at h
  rw [block_expansion, component_positions]
  exact h

/-- Operator-norm endpoint for the complete physical degree block. Each premise
is the actual block with fixed input/output residual positions. -/
theorem degree_block_norm (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5)
    (c : ℝ) (hc : 0 ≤ c)
    (hblock : ∀ (p : Position i) (q : Position j),
      ‖kernelOperator (positionBlock z K p.val q.val)‖ ≤ c) :
    ‖kernelOperator (degreeBlock z K i j)‖ ≤
      c * Real.sqrt ((Nat.choose 4 i.val : ℝ) * Nat.choose 4 j.val) := by
  apply norm_le_of_energyBound _ _ (mul_nonneg hc (Real.sqrt_nonneg _))
  intro f
  have hp (q : Position j) :
      action (productProjection z q.val) (action (productProjection z q.val) f) =
        action (productProjection z q.val) f := by
    rw [← kernelCompose_action, productProjection_compose z hq]
    simp
  have hb (p : Position i) (q : Position j) :
      l2 (action (productProjection z p.val) (action K (action (productProjection z q.val) f))) ≤
        c * l2 (action (productProjection z q.val) f) := by
    have h := l2_le_of_energy _ _ c hc
      (energyBound_of_norm (positionBlock z K p.val q.val) c hc (hblock p q)
        (action (productProjection z q.val) f))
    simpa only [positionBlock, kernelCompose_action, hp q] using h
  have hd : l2 (degreeComponent z j f) ≤ l2 f := by
    simpa only [one_mul] using l2_le_of_energy (degreeComponent z j f) f 1
      (by norm_num) (by simpa using degreeComponent_energy_le z hq j f)
  have h := (degree_l2_bound z hq K i j c hc f hb).trans
    (mul_le_mul_of_nonneg_left hd (mul_nonneg hc (Real.sqrt_nonneg _)))
  have hs := (sq_le_sq₀ (l2_nonneg _)
    (mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _)) (l2_nonneg _))).mpr h
  simpa only [l2_sq, mul_pow, degreeBlock_action] using hs

end AES8.PaperActivityArrayResidual
