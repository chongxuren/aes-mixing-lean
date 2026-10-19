import AESConcrete.WordColumnGram

/-!
# A probability-box bound retaining the complementary mass

The unlisted probability is exactly one minus the sum of the listed
probabilities. Replacing each listed probability by its cap is justified
by a factorization of the whole quadratic difference. It does not assume
that the objective is monotone inside the box. The caps and their match
to actual AES zero events are separate caller obligations.

Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityCollisionBox

variable {I : Type*} [Fintype I]

def collisionObjective (w p : I → ℝ) : ℝ :=
  (1 - ∑ i, p i)^2 + ∑ i, w i * p i^2

/-- The exact complementary mass is retained. No bound on the sum of caps
is needed; nonnegative caps and the endpoint condition suffice. -/
theorem collisionObjective_le_caps (w p b : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i)
    (hpb : ∀ i, p i ≤ b i) (hend : ∀ i, 2 ≤ (w i + 1) * b i) :
    collisionObjective w p ≤ collisionObjective w b := by
  classical
  have hb : ∀ i, 0 ≤ b i := fun i => (hp i).trans (hpb i)
  have hB (i : I) : b i ≤ ∑ k, b k :=
    Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ i)
  have hP (i : I) : p i ≤ ∑ k, p k :=
    Finset.single_le_sum (fun k _ => hp k) (Finset.mem_univ i)
  have hterm (i : I) : 0 ≤ (b i - p i) *
      ((∑ k, b k) + (∑ k, p k) - 2 + w i * (b i + p i)) := by
    apply mul_nonneg (sub_nonneg.mpr (hpb i))
    have hwp : 0 ≤ (w i + 1) * p i := mul_nonneg (by linarith [hw i]) (hp i)
    nlinarith [hB i, hP i, hend i]
  have he : collisionObjective w b - collisionObjective w p =
      ∑ i, (b i - p i) *
        ((∑ k, b k) + (∑ k, p k) - 2 + w i * (b i + p i)) := by
    unfold collisionObjective
    calc
      _ = ((∑ i, b i) - ∑ i, p i) * ((∑ i, b i) + (∑ i, p i) - 2) +
          ∑ i, w i * (b i^2 - p i^2) := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        ring
      _ = ∑ i, ((b i - p i) * ((∑ k, b k) + (∑ k, p k) - 2) +
          w i * (b i^2 - p i^2)) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_add_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [← he] at hn
  linarith

/-- Probability interpretation, with exact mass accounting as a premise. -/
theorem collision_with_complement_le (w p b : I → ℝ) (p0 : ℝ)
    (hmass : p0 + ∑ i, p i = 1)
    (hw : ∀ i, 0 ≤ w i) (hp : ∀ i, 0 ≤ p i)
    (hpb : ∀ i, p i ≤ b i) (hend : ∀ i, 2 ≤ (w i + 1) * b i) :
    p0^2 + ∑ i, w i * p i^2 ≤ collisionObjective w b := by
  have hp0 : p0 = 1 - ∑ i, p i := by linarith
  rw [hp0]
  exact collisionObjective_le_caps w p b hw hp hpb hend

end AESConcrete.ActivityCollisionBox
