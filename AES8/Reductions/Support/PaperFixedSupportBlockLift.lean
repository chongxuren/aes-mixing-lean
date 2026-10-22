import AES8.Reductions.Support.PaperSupportBlockLift

/-!
# Exact-support lifting with a fixed input support

The input zero mask is fixed while residual positions vary inside its
complement. The output still ranges over all supports of the requested size.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperFixedSupportBlockLift
open AESMixing PaperSupportProjection PaperSupportBlockLift
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

abbrev FixedLabel {n : ℕ} (j : ℕ) (s : Fin n → Bool) :=
  {r : Fin n → Bool // Valid (r,s) ∧ residualCount r = j}

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

/-- The actual tensor projection at a fixed input support. -/
def fixedComponent (z : V) (f : (Fin n → V) → ℝ) (j : ℕ)
    (s : Fin n → Bool) (x : Fin n → V) : ℝ :=
  ∑ r : FixedLabel j s, raw z (r.val,s) f x

theorem block_expansion (z : V) (K : (Fin n → V) → (Fin n → V) → ℝ)
    (f : (Fin n → V) → ℝ) (i t j : ℕ) (s : Fin n → Bool) :
    component z (action K (fixedComponent z f j s)) i t =
      fun y => ∑ p : BlockLabel n i t, ∑ r : FixedLabel j s,
        raw z p.val (action K (raw z (r.val,s) f)) y := by
  rw [component_labels]
  unfold fixedComponent
  rw [action_sum_family]
  simp_rw [raw_sum]

/-- Orthogonality removes the count of choices of input support. -/
theorem norm_le (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin n → V) → (Fin n → V) → ℝ)
    (f : (Fin n → V) → ℝ) (i t j : ℕ) (s : Fin n → Bool)
    (c : ℝ) (hc : 0 ≤ c)
    (hblock : ∀ (p : BlockLabel n i t) (r : FixedLabel j s),
      l2 (raw z p.val (action K (raw z (r.val,s) f))) ≤
        c * l2 (raw z (r.val,s) f)) :
    l2 (component z (action K (fixedComponent z f j s)) i t) ≤
      c * Real.sqrt ((Fintype.card (BlockLabel n i t) : ℝ) *
        Fintype.card (FixedLabel j s)) * l2 (fixedComponent z f j s) := by
  classical
  let v := fun r : FixedLabel j s => raw z (r.val,s) f
  let w := fun (p : BlockLabel n i t) (r : FixedLabel j s) =>
    raw z p.val (action K (raw z (r.val,s) f))
  have hin (r u : FixedLabel j s) (hru : r ≠ u) :
      (∑ x, v r x * v u x) = 0 :=
    raw_orthogonal z hq (r.val,s) (u.val,s)
      (fun h => hru (Subtype.ext (Prod.mk.inj h).1)) f f
  have he (p : BlockLabel n i t) :
      (fun y => ∑ r, w p r y) = raw z p.val (action K (fixedComponent z f j s)) := by
    unfold fixedComponent
    rw [action_sum_family, raw_sum]
  have hout (p u : BlockLabel n i t) (hpu : p ≠ u) :
      (∑ y, (∑ r, w p r y) * (∑ r, w u r y)) = 0 := by
    have h := raw_orthogonal z hq p.val u.val (fun h => hpu (Subtype.ext h))
      (action K (fixedComponent z f j s)) (action K (fixedComponent z f j s))
    rw [← he p, ← he u] at h
    exact h
  have h := PaperOrthogonalBlockLift.norm_le v w c hc hblock hin hout
  rw [block_expansion]
  exact h

/-- Only the sixteen masks are enumerated, never word values. -/
theorem four_word_count (j : Fin 5) (s : Fin 4 → Bool) :
    Fintype.card (FixedLabel j.val s) = Nat.choose (supportCount s) j.val := by
  exact (by decide : ∀ (j : Fin 5) (s : Fin 4 → Bool),
    Fintype.card (FixedLabel j.val s) = Nat.choose (supportCount s) j.val) j s

theorem four_word_norm_le (z : V) (hq : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (f : (Fin 4 → V) → ℝ) (i t j : Fin 5) (s : Fin 4 → Bool)
    (c : ℝ) (hc : 0 ≤ c)
    (hblock : ∀ (p : BlockLabel 4 i.val t.val) (r : FixedLabel j.val s),
      l2 (raw z p.val (action K (raw z (r.val,s) f))) ≤
        c * l2 (raw z (r.val,s) f)) :
    l2 (component z (action K (fixedComponent z f j.val s)) i.val t.val) ≤
      c * Real.sqrt (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
        Nat.choose (supportCount s) j.val) * l2 (fixedComponent z f j.val s) := by
  simpa only [PaperSupportBlockLift.four_word_count, four_word_count, Nat.cast_mul] using
    norm_le z hq K f i.val t.val j.val s c hc hblock

end AES8.PaperFixedSupportBlockLift
