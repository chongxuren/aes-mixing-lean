import AES8.Math.PaperOrthogonalBlockLift
import AES8.Reductions.Support.PaperSupportProjectionLaws
import AESMixing.DegreeMatrixNorm

/-!
# Orthogonal block assembly for the paper's actual support projections

The index type contains only valid residual/support masks with the requested
counts. Orthogonality and projection decomposition are proved for these
literal masks; only the per-position operator cap is supplied by the caller.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSupportBlockLift
open AESMixing PaperSupportProjection
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev BlockLabel (n i t : ℕ) :=
  {p : Label n // Valid p ∧ residualCount p.1 = i ∧ supportCount p.2 = t}

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

theorem component_labels (z : V) (f : (Fin n → V) → ℝ) (i t : ℕ) :
    component z f i t = fun x => ∑ p : BlockLabel n i t, raw z p.val f x := by
  classical
  funext x
  unfold component
  calc
    _ = ∑ p : Label n, if Valid p ∧ residualCount p.1 = i ∧ supportCount p.2 = t
        then raw z p f x else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : Valid p
      · simp [hp]
      · simp [hp, raw_invalid z p hp f]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

theorem raw_sum {J : Type*} [Fintype J] (z : V) (p : Label n)
    (f : J → (Fin n → V) → ℝ) :
    raw z p (fun x => ∑ j, f j x) = fun y => ∑ j, raw z p (f j) y :=
  action_sum_family _ _

/-- Exact two-sided decomposition of the literal grouped support block. -/
theorem block_expansion (z : V) (K : (Fin n → V) → (Fin n → V) → ℝ)
    (f : (Fin n → V) → ℝ) (i t j u : ℕ) :
    component z (action K (component z f j u)) i t =
      fun y => ∑ p : BlockLabel n i t, ∑ q : BlockLabel n j u,
        raw z p.val (action K (raw z q.val f)) y := by
  rw [component_labels, component_labels, action_sum_family]
  simp_rw [raw_sum]

/-- The paper's square-root block-count factor for the actual projections. -/
theorem norm_le (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin n → V) → (Fin n → V) → ℝ)
    (f : (Fin n → V) → ℝ) (i t j u : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (hblock : ∀ (p : BlockLabel n i t) (q : BlockLabel n j u),
      l2 (raw z p.val (action K (raw z q.val f))) ≤ c * l2 (raw z q.val f)) :
    l2 (component z (action K (component z f j u)) i t) ≤
      c * Real.sqrt ((Fintype.card (BlockLabel n i t) : ℝ) *
        Fintype.card (BlockLabel n j u)) * l2 (component z f j u) := by
  classical
  let v := fun q : BlockLabel n j u => raw z q.val f
  let w := fun (p : BlockLabel n i t) (q : BlockLabel n j u) =>
    raw z p.val (action K (raw z q.val f))
  have hin (q r : BlockLabel n j u) (hqr : q ≠ r) :
      (∑ x, v q x * v r x) = 0 :=
    raw_orthogonal z hq q.val r.val (fun h => hqr (Subtype.ext h)) f f
  have he (p : BlockLabel n i t) :
      (fun y => ∑ q, w p q y) = raw z p.val (action K (component z f j u)) := by
    rw [component_labels, action_sum_family, raw_sum]
  have hout (p r : BlockLabel n i t) (hpr : p ≠ r) :
      (∑ y, (∑ q, w p q y) * (∑ q, w r q y)) = 0 := by
    have h := raw_orthogonal z hq p.val r.val (fun h => hpr (Subtype.ext h))
      (action K (component z f j u)) (action K (component z f j u))
    rw [← he p, ← he r] at h
    exact h
  have h := PaperOrthogonalBlockLift.norm_le v w c hc hblock hin hout
  rw [block_expansion, component_labels]
  exact h

/-- Fixed four-word mask count; no byte/word values are enumerated. -/
theorem four_word_count (i t : Fin 5) :
    Fintype.card (BlockLabel 4 i.val t.val) = Nat.choose 4 t.val * Nat.choose t.val i.val := by
  fin_cases i <;> fin_cases t <;> decide

/-- Actual AES-width support multiplicities, with empty types covered. -/
theorem four_word_norm_le (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (f : (Fin 4 → V) → ℝ) (i t j u : Fin 5) (c : ℝ) (hc : 0 ≤ c)
    (hblock : ∀ (p : BlockLabel 4 i.val t.val) (q : BlockLabel 4 j.val u.val),
      l2 (raw z p.val (action K (raw z q.val f))) ≤ c * l2 (raw z q.val f)) :
    l2 (component z (action K (component z f j.val u.val)) i.val t.val) ≤
      c * Real.sqrt (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
        (Nat.choose 4 u.val * Nat.choose u.val j.val)) * l2 (component z f j.val u.val) := by
  simpa only [four_word_count, Nat.cast_mul] using norm_le z hq K f i.val t.val j.val u.val c hc hblock

end AES8.PaperSupportBlockLift
