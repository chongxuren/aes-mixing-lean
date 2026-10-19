import AESConcrete.SurvivorRelabel

/-!
# Exact inverse-frame coefficients from Boolean Hamming distance

Each equal Boolean coordinate contributes 256/255 and each unequal one
contributes (256/255)*(-1/16). The resulting signed and absolute product
formulas preserve the actual frame. A separate count identity supplies
the parity relation with false-coordinate counts.

Constructive mathematics only; no attacks, manuscript changes, numerical
cube enumeration or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.FrameHamming
open AESConcrete.ActivityFrame (frameInverse byteInverse)
open AESConcrete.SurvivorRelabel (falseCount)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

variable {I J : Type*} [Fintype I] [Fintype J]

def distance (s t : I → Bool) : ℕ := Fintype.card {i : I // s i ≠ t i}

def bothFalseCount (s t : I → Bool) : ℕ :=
  Fintype.card {i : I // s i = false ∧ t i = false}

theorem distance_comp (e : I ≃ J) (s t : J → Bool) :
    distance (fun i => s (e i)) (fun i => t (e i)) = distance s t := by
  exact Fintype.card_congr (e.subtypeEquiv (fun i => Iff.rfl))

theorem distance_le_card (s t : I → Bool) : distance s t ≤ Fintype.card I :=
  Fintype.card_subtype_le (fun i : I => s i ≠ t i)

theorem distance_symmetric (s t : I → Bool) : distance s t = distance t s := by
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => ne_comm))

theorem distance_self (s : I → Bool) : distance s s = 0 := by
  simp [distance, Fintype.card_subtype]

/-- Exact signed coefficient of the actual tensor inverse frame. -/
theorem frameInverse_eq_distance (s t : I → Bool) :
    frameInverse s t = (256 / 255 : ℝ) ^ Fintype.card I *
      (-(1 / 16 : ℝ)) ^ distance s t := by
  unfold frameInverse
  simp only [byteInverse]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]
  congr 1
  simp only [Finset.prod_ite, Finset.prod_const_one, one_mul,
    Finset.prod_const, distance, Fintype.card_subtype]

theorem abs_frameInverse_eq_distance (s t : I → Bool) :
    |frameInverse s t| = (256 / 255 : ℝ) ^ Fintype.card I *
      (1 / 16 : ℝ) ^ distance s t := by
  rw [frameInverse_eq_distance, abs_mul]
  simp only [abs_pow, abs_neg,
    abs_of_nonneg (by norm_num : 0 ≤ (256 / 255 : ℝ)),
    abs_of_nonneg (by norm_num : 0 ≤ (1 / 16 : ℝ))]

theorem distance_eq_sum (s t : I → Bool) :
    distance s t = ∑ i : I, if s i ≠ t i then 1 else 0 := by
  unfold distance
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem bothFalseCount_eq_sum (s t : I → Bool) :
    bothFalseCount s t = ∑ i : I, if s i = false ∧ t i = false then 1 else 0 := by
  simp [bothFalseCount, Fintype.card_subtype]

theorem falseCount_eq_sum (s : I → Bool) :
    falseCount s = ∑ i : I, if s i = false then 1 else 0 := by
  simp [falseCount, Fintype.card_subtype]

/-- The common false coordinates contribute twice to the two false counts. -/
theorem distance_add_twice_bothFalse (s t : I → Bool) :
    distance s t + 2 * bothFalseCount s t = falseCount s + falseCount t := by
  have hp (i : I) :
      (if s i ≠ t i then 1 else 0) +
          2 * (if s i = false ∧ t i = false then 1 else 0) =
        (if s i = false then 1 else 0) + (if t i = false then 1 else 0) := by
    cases hs : s i <;> cases ht : t i <;> simp [hs, ht]
  calc
    _ = (∑ i : I, if s i ≠ t i then 1 else 0) +
        2 * (∑ i : I, if s i = false ∧ t i = false then 1 else 0) := by
      rw [distance_eq_sum, bothFalseCount_eq_sum]
    _ = ∑ i : I, ((if s i ≠ t i then 1 else 0) +
        2 * (if s i = false ∧ t i = false then 1 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = ∑ i : I, ((if s i = false then 1 else 0) +
        (if t i = false then 1 else 0)) := Finset.sum_congr rfl (fun i _ => hp i)
    _ = _ := by rw [Finset.sum_add_distrib, falseCount_eq_sum, falseCount_eq_sum]

theorem distance_mod_two (s t : I → Bool) :
    distance s t % 2 = (falseCount s + falseCount t) % 2 := by
  have h := distance_add_twice_bothFalse s t
  omega

theorem neg_one_pow_distance (s t : I → Bool) :
    (-1 : ℝ) ^ distance s t = (-1 : ℝ) ^ (falseCount s + falseCount t) := by
  rw [← distance_add_twice_bothFalse s t, pow_add, pow_mul]
  norm_num

end AESConcrete.FrameHamming
