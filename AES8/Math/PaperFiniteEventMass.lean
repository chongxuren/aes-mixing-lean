import Mathlib.Algebra.BigOperators.Field
import AES8.Math.Imports

/-! Finite event masses under the original normalized law. The union bound
requires nonnegativity and does not condition or renormalize the law. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperFiniteEventMass
set_option autoImplicit false
variable {X I : Type*} [Fintype X] [Fintype I]
attribute [local instance] Classical.propDecidable

def mass (f : X → ℝ) (event : X → Prop) : ℝ :=
  ∑ x, if event x then f x else 0

theorem nonneg (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (event : X → Prop) :
    0 ≤ mass f event := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs <;> first | exact hf x | exact le_rfl

theorem le_total (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (event : X → Prop) :
    mass f event ≤ ∑ x, f x := by
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> first | exact le_rfl | exact hf x

theorem complement (f : X → ℝ) (event : X → Prop) :
    mass f (fun x => ¬ event x) = (∑ x, f x) - mass f event := by
  unfold mass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : event x <;> simp [he]

theorem union_le_sum (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (event : I → X → Prop) :
    mass f (fun x => ∃ i, event i x) ≤ ∑ i, mass f (event i) := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases he : ∃ i, event i x
  · obtain ⟨i, hi⟩ := he
    rw [if_pos ⟨i, hi⟩]
    have h := Finset.single_le_sum
      (f := fun j => if event j x then f x else 0)
      (fun j (_ : j ∈ (Finset.univ : Finset I)) => by
        split_ifs <;> first | exact hf x | exact le_rfl)
      (Finset.mem_univ i)
    simpa only [if_pos hi] using h
  · rw [if_neg he]
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> first | exact hf x | exact le_rfl

theorem complement_union_lower (f : X → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hmass : (∑ x, f x) = 1) (event : I → X → Prop) (B : ℝ)
    (hB : ∀ i, mass f (event i) ≤ B) :
    1-(Fintype.card I : ℝ)*B ≤ mass f (fun x => ∀ i, ¬ event i x) := by
  have h := (union_le_sum f hf event).trans (Finset.sum_le_sum (fun i _ => hB i))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have he : (fun x => ∀ i, ¬ event i x) = (fun x => ¬ ∃ i, event i x) := by
    funext x
    simp only [not_exists]
  rw [he, complement, hmass]
  linarith

end AES8.PaperFiniteEventMass
