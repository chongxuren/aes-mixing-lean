import AESMixing.IncidenceComparison
import AESMixing.DiagonalComparison

/-! Euclidean energy bounds for the three small incidence comparisons.
These specialize the general diagonal Schur lemma to the checked exact
rational witnesses. The support-to-operator correspondence is separate. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem incidenceSupportRaw_nonneg (i j a b : ℕ) :
    0 ≤ incidenceSupportRaw i j a b := by
  unfold incidenceSupportRaw
  apply Finset.sum_nonneg
  intro d _
  split_ifs <;> positivity

theorem incidenceSupportRaw_symm (i j a b : ℕ) :
    incidenceSupportRaw i j a b = incidenceSupportRaw j i b a := by
  unfold incidenceSupportRaw
  rw [Nat.add_comm j i]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.add_comm b a,Nat.add_comm (min j d) (min i d)]
  have h : a+b-i-j = a+b-j-i := by omega
  rw [h]

def incidenceComparison (i j : ℕ) (a : Fin (5-i)) (b : Fin (5-j)) : ℝ :=
  Real.sqrt (incidenceSupportWeight i (a.val+i) : ℝ) *
    (incidenceSupportRaw i j (a.val+i) (b.val+j) : ℝ) *
      Real.sqrt (incidenceSupportWeight j (b.val+j) : ℝ)

theorem incidence_comparison_11_energy (f : Fin 4 → ℝ) :
    (∑ a, action (incidenceComparison 1 1) f a^2) ≤
      (27/8000 : ℝ)^2 * ∑ b, f b^2 := by
  apply diagonal_comparison_energy
    (fun a b => (incidenceSupportRaw 1 1 (a.val+1) (b.val+1) : ℝ))
    (fun a => (incidenceSupportWeight 1 (a.val+1) : ℝ))
    (fun b => (incidenceSupportWeight 1 (b.val+1) : ℝ))
    (fun a => (incidenceWitness11 a : ℝ)) (fun b => (incidenceWitness11 b : ℝ))
    (27/8000) (by norm_num)
  · intro a b
    exact_mod_cast incidenceSupportRaw_nonneg 1 1 (a.val+1) (b.val+1)
  · intro a
    fin_cases a <;> norm_num [incidenceSupportWeight,Nat.choose]
  · intro b
    fin_cases b <;> norm_num [incidenceSupportWeight,Nat.choose]
  · intro a
    exact_mod_cast incidence_witnesses_positive.1 a
  · intro b
    exact_mod_cast incidence_witnesses_positive.1 b
  · intro a
    have h := (Rat.cast_le (K := ℝ)).mpr (le_of_lt (incidence_comparison_11_rows a))
    norm_num only [Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at h
    exact h
  · intro b
    simp_rw [incidenceSupportRaw_symm 1 1 _ (b.val+1)]
    have h := (Rat.cast_le (K := ℝ)).mpr (le_of_lt (incidence_comparison_11_rows b))
    norm_num only [Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at h
    exact h

theorem incidence_comparison_12_energy (f : Fin 3 → ℝ) :
    (∑ a, action (incidenceComparison 1 2) f a^2) ≤
      (43/500 : ℝ)^2 * ∑ b, f b^2 := by
  apply diagonal_comparison_energy
    (fun a b => (incidenceSupportRaw 1 2 (a.val+1) (b.val+2) : ℝ))
    (fun a => (incidenceSupportWeight 1 (a.val+1) : ℝ))
    (fun b => (incidenceSupportWeight 2 (b.val+2) : ℝ))
    (fun a => (incidenceWitness12Out a : ℝ)) (fun b => (incidenceWitness12In b : ℝ))
    (43/500) (by norm_num)
  · intro a b
    exact_mod_cast incidenceSupportRaw_nonneg 1 2 (a.val+1) (b.val+2)
  · intro a
    fin_cases a <;> norm_num [incidenceSupportWeight,Nat.choose]
  · intro b
    fin_cases b <;> norm_num [incidenceSupportWeight,Nat.choose]
  · intro a
    exact_mod_cast incidence_witnesses_positive.2.1 a
  · intro b
    exact_mod_cast incidence_witnesses_positive.2.2.1 b
  · intro a
    have h := (Rat.cast_le (K := ℝ)).mpr (le_of_lt (incidence_comparison_12_rows a))
    norm_num only [Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at h
    exact h
  · intro b
    have h := (Rat.cast_le (K := ℝ)).mpr (le_of_lt (incidence_comparison_12_columns b))
    norm_num only [Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at h
    exact h

theorem incidence_comparison_22_energy (f : Fin 3 → ℝ) :
    (∑ a, action (incidenceComparison 2 2) f a^2) ≤
      (9/10 : ℝ)^2 * ∑ b, f b^2 := by
  apply diagonal_comparison_energy
    (fun a b => (incidenceSupportRaw 2 2 (a.val+2) (b.val+2) : ℝ))
    (fun a => (incidenceSupportWeight 2 (a.val+2) : ℝ))
    (fun b => (incidenceSupportWeight 2 (b.val+2) : ℝ))
    (fun a => (incidenceWitness22 a : ℝ)) (fun b => (incidenceWitness22 b : ℝ))
    (9/10) (by norm_num)
  · intro a b
    exact_mod_cast incidenceSupportRaw_nonneg 2 2 (a.val+2) (b.val+2)
  · intro a
    fin_cases a <;> norm_num [incidenceSupportWeight,Nat.choose]
  · intro b
    fin_cases b <;> norm_num [incidenceSupportWeight,Nat.choose]
  · intro a
    exact_mod_cast incidence_witnesses_positive.2.2.2 a
  · intro b
    exact_mod_cast incidence_witnesses_positive.2.2.2 b
  · intro a
    have h := (Rat.cast_le (K := ℝ)).mpr (le_of_lt (incidence_comparison_22_rows a))
    norm_num only [Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at h
    exact h
  · intro b
    simp_rw [incidenceSupportRaw_symm 2 2 _ (b.val+2)]
    have h := (Rat.cast_le (K := ℝ)).mpr (le_of_lt (incidence_comparison_22_rows b))
    norm_num only [Rat.cast_sum,Rat.cast_mul,Rat.cast_div,Rat.cast_ofNat] at h
    exact h

end AESMixing
