import AESPaper.RectangularBounds
import AESMixing.DegreeMatrixNorm
import Mathlib.Tactic.FinCases

/-!
# Orthogonal aggregation of residual positions

The block hypothesis applies to every signed joint input. We apply it to
the input position projection itself, using its idempotence. Cauchy--Schwarz
over input masks and orthogonality over both mask families give the exact
factor sqrt(choose(4,i) * choose(4,j)). Only the sixteen Boolean masks are
counted; the arbitrary alphabet and its word-state space are not enumerated.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.PositionAggregation
open AESMixing AESPaper.RectangularFourier

/-- The residual-position masks in one of the five degree spaces. -/
def masks (j : Fin 5) : Finset (Fin 4 → Bool) :=
  Finset.univ.filter (fun a => degreeIndex a = j)

theorem mem_masks (j : Fin 5) (a : Fin 4 → Bool) :
    a ∈ masks j ↔ degreeIndex a = j := by
  simp only [masks, Finset.mem_filter, Finset.mem_univ, true_and]

/-- An exact finite count of masks, independent of the alphabet. -/
theorem masks_card (j : Fin 5) : (masks j).card = Nat.choose 4 j.val := by
  fin_cases j <;> decide

section FiniteSum
variable {A X Y : Type*} [Fintype X] [Fintype Y]

/-- Transport a finite family sum through a kernel. -/
theorem action_finset_sum (K : Y → X → ℝ) (s : Finset A) (F : A → X → ℝ) :
    action K (fun x => ∑ a ∈ s, F a x) =
      fun y => ∑ a ∈ s, action K (F a) y := by
  funext y
  simp only [action, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Finite Cauchy--Schwarz, summed over the output coordinate. -/
theorem finite_sum_energy (s : Finset A) (F : A → X → ℝ) :
    (∑ x, (∑ a ∈ s, F a x) ^ 2) ≤
      (s.card : ℝ) * ∑ a ∈ s, ∑ x, F a x ^ 2 := by
  calc
    _ ≤ ∑ x, (s.card : ℝ) * ∑ a ∈ s, F a x ^ 2 := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
        (Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun a => F a x))
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]

end FiniteSum

section Positions
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem component_eq_sum (z : V) (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z j f =
      fun x => ∑ a ∈ masks j, action (productProjection z a) f x := by
  funext x
  simp only [degreeComponent, groupedFamily, masks, Finset.sum_filter]

/-- Both sides retain the actual counting-measure energies. -/
theorem component_energy_eq_sum (z : V) (hn : 1 < Fintype.card V)
    (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeComponent z j f x ^ 2) =
      ∑ a ∈ masks j, ∑ x, action (productProjection z a) f x ^ 2 := by
  simpa only [masks, Finset.sum_filter] using degreeComponent_energy z hn j f

/-- The fixed-position block bound is used on the projected input, so its
right side is that input component's energy rather than the full energy. -/
theorem projected_block_energy (z : V) (hn : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (a b : Fin 4 → Bool)
    (c : ℝ)
    (hblock : EnergyBound
      (kernelCompose (productProjection z a) (kernelCompose K (productProjection z b))) c)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (productProjection z a)
      (action K (action (productProjection z b) f)) y ^ 2) ≤
      c ^ 2 * ∑ x, action (productProjection z b) f x ^ 2 := by
  have hid : action (productProjection z b) (action (productProjection z b) f) =
      action (productProjection z b) f := by
    rw [← kernelCompose_action, productProjection_compose z hn]
    simp only [if_true]
  have he := hblock (action (productProjection z b) f)
  change (∑ y, action
    (kernelCompose (productProjection z a) (kernelCompose K (productProjection z b)))
    (action (productProjection z b) f) y ^ 2) ≤ _ at he
  rw [kernelCompose_action, kernelCompose_action, hid] at he
  exact he

/-- Exact squared-energy aggregation. No centering, input independence or
tensor-product representation is required. -/
theorem degree_energy (z : V) (hn : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5) (c : ℝ)
    (hblocks : ∀ (a b : Fin 4 → Bool),
      residualDegree a = i.val → residualDegree b = j.val →
      EnergyBound
        (kernelCompose (productProjection z a) (kernelCompose K (productProjection z b))) c)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, degreeComponent z i (action K (degreeComponent z j f)) y ^ 2) ≤
      ((Nat.choose 4 i.val : ℝ) * (Nat.choose 4 j.val : ℝ) * c ^ 2) *
        ∑ x, degreeComponent z j f x ^ 2 := by
  have hrow (a : Fin 4 → Bool) (ha : a ∈ masks i) :
      (∑ y, action (productProjection z a) (action K (degreeComponent z j f)) y ^ 2) ≤
        ((Nat.choose 4 j.val : ℝ) * c ^ 2) * ∑ x, degreeComponent z j f x ^ 2 := by
    have had : residualDegree a = i.val := congrArg Fin.val ((mem_masks i a).mp ha)
    have hex : action (productProjection z a) (action K (degreeComponent z j f)) =
        fun y => ∑ b ∈ masks j,
          action (productProjection z a) (action K (action (productProjection z b) f)) y := by
      rw [component_eq_sum z j f, action_finset_sum, action_finset_sum]
    rw [hex]
    calc
      _ ≤ ((masks j).card : ℝ) * ∑ b ∈ masks j, ∑ y,
          action (productProjection z a) (action K (action (productProjection z b) f)) y ^ 2 :=
        finite_sum_energy (masks j) _
      _ ≤ ((masks j).card : ℝ) * ∑ b ∈ masks j,
          c ^ 2 * ∑ x, action (productProjection z b) f x ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro b hb
        have hbd : residualDegree b = j.val :=
          congrArg Fin.val ((mem_masks j b).mp hb)
        exact projected_block_energy z hn K a b c (hblocks a b had hbd) f
      _ = _ := by
        rw [← Finset.mul_sum, ← component_energy_eq_sum z hn j f, masks_card]
        ring
  rw [component_energy_eq_sum z hn i (action K (degreeComponent z j f))]
  calc
    _ ≤ ∑ a ∈ masks i,
        ((Nat.choose 4 j.val : ℝ) * c ^ 2) * ∑ x, degreeComponent z j f x ^ 2 :=
      Finset.sum_le_sum (fun a ha => hrow a ha)
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, masks_card]
      ring

/-- The position factor is multiplied once, after the per-position block
bound; the input is the actual degree projection of an arbitrary signed f. -/
theorem degree_norm (z : V) (hn : 1 < Fintype.card V)
    (K : (Fin 4 → V) → (Fin 4 → V) → ℝ) (i j : Fin 5) (c : ℝ) (hc : 0 ≤ c)
    (hblocks : ∀ (a b : Fin 4 → Bool),
      residualDegree a = i.val → residualDegree b = j.val →
      EnergyBound
        (kernelCompose (productProjection z a) (kernelCompose K (productProjection z b))) c)
    (f : (Fin 4 → V) → ℝ) :
    l2 (degreeComponent z i (action K (degreeComponent z j f))) ≤
      (Real.sqrt ((Nat.choose 4 i.val : ℝ) * (Nat.choose 4 j.val : ℝ)) * c) *
        l2 (degreeComponent z j f) := by
  apply l2_le_of_energy _ _
    (Real.sqrt ((Nat.choose 4 i.val : ℝ) * (Nat.choose 4 j.val : ℝ)) * c)
    (mul_nonneg (Real.sqrt_nonneg _) hc)
  simpa only [mul_pow, Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
    using degree_energy z hn K i j c hblocks f

end Positions
end AESPaper.PositionAggregation
