import AESPaper.BiasTensorEnergy

/-!
# Conditional pure J/Z energy from joint zero-event caps

The absolute signed bias moment is bounded by the expectation of the product
of `1 + card * indicator_zero` at its selected positions. Expansion over the
sixteen Boolean choices preserves every joint zero-event mass. The cap
`(20/card)^|D|` for all subsets gives a moment cap `21^|S|`, and hence the
pure J/Z energy cap `card^(-4) * (441/(card-1))^|S|`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

namespace AESPaper.PureBiasBounds
open AESMixing AESPaper.BiasTensorEnergy

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Q" => (Fintype.card V : ℝ)

def selected (d : Fin 4 → Bool) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => d i = true)

def positiveWeight (z : V) (S : Finset (Fin 4)) (x : Fin 4 → V) : ℝ :=
  ∏ i : Fin 4, (1 + (if i ∈ S then Q * (if x i=z then 1 else 0) else 0))

theorem basis_eq_indicator (z x : V) :
    basis z x = Q * (if x=z then 1 else 0) - 1 := by
  by_cases hx : x=z <;> simp [basis, hx]

/-- Exact signed-moment expectation, with every selected zero indicator kept. -/
theorem moment_eq_indicator (z : V) (S : Finset (Fin 4)) (g : (Fin 4 → V) → ℝ) :
    moment z S g = ∑ x, g x *
      ∏ i : Fin 4, if i ∈ S then Q * (if x i=z then 1 else 0) - 1 else 1 := by
  simp only [moment, basisProduct, basis_eq_indicator]

theorem selection_product (z : V) (S : Finset (Fin 4)) (x : Fin 4 → V)
    (d : Fin 4 → Bool) :
    (∏ i : Fin 4, if d i then
      (if i ∈ S then Q * (if x i=z then 1 else 0) else 0) else 1) =
      if selected d ⊆ S then Q ^ (selected d).card *
        (if (∀ i ∈ selected d, x i=z) then 1 else 0) else 0 := by
  by_cases hs : selected d ⊆ S
  · rw [if_pos hs]
    have ht (i : Fin 4) :
        (if d i then (if i ∈ S then Q * (if x i=z then 1 else 0) else 0) else 1) =
        (if i ∈ selected d then Q else 1) *
          (if i ∈ selected d then (if x i=z then 1 else 0) else 1) := by
      by_cases hd : d i = true
      · have hi : i ∈ selected d := by simp [selected, hd]
        have hS := hs hi
        simp [hd, hi, hS]
      · have hi : i ∉ selected d := by simp [selected, hd]
        simp [hd, hi]
    have hq : (∏ i : Fin 4, if i ∈ selected d then Q else 1) = Q ^ (selected d).card := by
      simpa only [one_mul, one_pow] using constant_product (selected d) 1 Q
    have hz : (∏ i : Fin 4,
        if i ∈ selected d then (if x i=z then (1 : ℝ) else 0) else 1) =
        if (∀ i ∈ selected d, x i=z) then 1 else 0 := by
      by_cases hzero : ∀ i ∈ selected d, x i=z
      · rw [if_pos hzero]
        apply Finset.prod_eq_one
        intro i _
        by_cases hi : i ∈ selected d
        · simp [hi, hzero i hi]
        · simp [hi]
      · rw [if_neg hzero]
        push_neg at hzero
        obtain ⟨i,hi,hxi⟩ := hzero
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi, hxi])
    simp_rw [ht]
    rw [Finset.prod_mul_distrib, hq, hz]
  · rw [if_neg hs]
    have hw : ∃ i, i ∈ selected d ∧ i ∉ S := by
      by_contra h
      push_neg at h
      exact hs (fun i hi => h i hi)
    obtain ⟨i,hi,hS⟩ := hw
    have hd : d i = true := by simpa only [selected, Finset.mem_filter,
      Finset.mem_univ, true_and] using hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hd, hS])

theorem positiveWeight_expansion (z : V) (S : Finset (Fin 4)) (x : Fin 4 → V) :
    positiveWeight z S x = ∑ d : Fin 4 → Bool,
      if selected d ⊆ S then Q ^ (selected d).card *
        (if (∀ i ∈ selected d, x i=z) then 1 else 0) else 0 := by
  have h := Fintype.prod_sum (fun (i : Fin 4) (t : Bool) =>
    if t then (if i ∈ S then Q * (if x i=z then (1 : ℝ) else 0) else 0) else 1)
  have hi (i : Fin 4) :
      (∑ t : Bool, if t then (if i ∈ S then Q * (if x i=z then (1 : ℝ) else 0)
        else 0) else 1) =
      1 + (if i ∈ S then Q * (if x i=z then 1 else 0) else 0) := by
    simp [add_comm]
  simp_rw [hi] at h
  change positiveWeight z S x = _ at h
  exact h.trans (Finset.sum_congr rfl (fun d _ => selection_product z S x d))

theorem positive_expectation (z : V) (S : Finset (Fin 4)) (g : (Fin 4 → V) → ℝ) :
    (∑ x, g x * positiveWeight z S x) = ∑ d : Fin 4 → Bool,
      if selected d ⊆ S then Q ^ (selected d).card * jointZeroMass z g (selected d) else 0 := by
  simp_rw [positiveWeight_expansion, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hs : selected d ⊆ S
  · simp only [if_pos hs]
    unfold jointZeroMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hz : ∀ i ∈ selected d, x i=z <;> simp [hz] <;> ring
  · simp [hs]

theorem basis_abs_le (z : V) (hn : 1 < Fintype.card V) (x : V) :
    |basis z x| ≤ 1 + Q * (if x=z then 1 else 0) := by
  have hQ : (1 : ℝ) < Q := by exact_mod_cast hn
  by_cases hx : x=z
  · simp only [basis, hx, if_true, mul_one, abs_of_pos (sub_pos.mpr hQ)]
    linarith
  · simp [basis, hx]

theorem basisProduct_abs_le (z : V) (hn : 1 < Fintype.card V)
    (S : Finset (Fin 4)) (x : Fin 4 → V) :
    |basisProduct z S x| ≤ positiveWeight z S x := by
  unfold basisProduct positiveWeight
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro i _
  by_cases hi : i ∈ S
  · simpa only [if_pos hi] using basis_abs_le z hn (x i)
  · simp [hi]

/-- Only the sixteen position masks and their natural coefficients are checked. -/
theorem selection_weight_sum : ∀ S : Finset (Fin 4),
    (∑ d : Fin 4 → Bool, if selected d ⊆ S then (20 : ℕ) ^ (selected d).card else 0) =
      (21 : ℕ) ^ S.card := by decide

theorem selection_weight_sum_real (S : Finset (Fin 4)) :
    (∑ d : Fin 4 → Bool, if selected d ⊆ S then (20 : ℝ) ^ (selected d).card else 0) =
      (21 : ℝ) ^ S.card := by
  exact_mod_cast selection_weight_sum S

/-- Every joint event remains explicit until its own cap is applied. -/
theorem moment_abs_le (z : V) (hn : 1 < Fintype.card V)
    (S : Finset (Fin 4)) (g : (Fin 4 → V) → ℝ) (hg : ∀ x, 0 ≤ g x)
    (he : ∀ D : Finset (Fin 4), D ⊆ S → jointZeroMass z g D ≤ (20/Q) ^ D.card) :
    |moment z S g| ≤ (21 : ℝ) ^ S.card := by
  have hQ : (0 : ℝ) < Q := by exact_mod_cast (lt_trans Nat.zero_lt_one hn)
  have hcancel : Q * (20/Q) = 20 := by field_simp [ne_of_gt hQ] <;> ring
  calc
    _ ≤ ∑ x, |g x * basisProduct z S x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, g x * |basisProduct z S x| := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (hg x)]
    _ ≤ ∑ x, g x * positiveWeight z S x :=
      Finset.sum_le_sum (fun x _ =>
        mul_le_mul_of_nonneg_left (basisProduct_abs_le z hn S x) (hg x))
    _ = ∑ d : Fin 4 → Bool, if selected d ⊆ S then
        Q ^ (selected d).card * jointZeroMass z g (selected d) else 0 :=
      positive_expectation z S g
    _ ≤ ∑ d : Fin 4 → Bool, if selected d ⊆ S then
        (20 : ℝ) ^ (selected d).card else 0 := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hs : selected d ⊆ S
      · rw [if_pos hs, if_pos hs]
        calc
          _ ≤ Q ^ (selected d).card * (20/Q) ^ (selected d).card :=
            mul_le_mul_of_nonneg_left (he (selected d) hs) (pow_nonneg (le_of_lt hQ) _)
          _ = _ := by rw [← mul_pow, hcancel]
      · simp [hs]
    _ = _ := selection_weight_sum_real S

/-- Conditional pure J/Z energy cap, before any actual AES event integration. -/
theorem energy_le (z : V) (hn : 1 < Fintype.card V)
    (S : Finset (Fin 4)) (g : (Fin 4 → V) → ℝ) (hg : ∀ x, 0 ≤ g x)
    (he : ∀ D : Finset (Fin 4), D ⊆ S → jointZeroMass z g D ≤ (20/Q) ^ D.card) :
    (∑ y, action (kernel z S) g y ^ 2) ≤
      (1 / Q ^ 4) * (441 / (Q-1)) ^ S.card := by
  have hQ : (1 : ℝ) < Q := by exact_mod_cast hn
  have h0 : Q ≠ 0 := by linarith
  have h1 : Q-1 ≠ 0 := by linarith
  have hd : 0 < Q ^ 4 * (Q-1) ^ S.card :=
    mul_pos (pow_pos (by linarith) _) (pow_pos (sub_pos.mpr hQ) _)
  have hs : moment z S g ^ 2 ≤ ((21 : ℝ) ^ S.card) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (moment z S g))
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 21) S.card)).2 (moment_abs_le z hn S g hg he)
    simpa only [sq_abs] using h
  have hnumer : ((21 : ℝ) ^ S.card) ^ 2 = (441 : ℝ) ^ S.card := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [energy_eq z hn S g]
  calc
    _ ≤ ((21 : ℝ) ^ S.card) ^ 2 / (Q ^ 4 * (Q-1) ^ S.card) :=
      div_le_div_of_nonneg_right hs (le_of_lt hd)
    _ = _ := by
      rw [hnumer, div_pow]
      field_simp [h0, h1] <;> ring

end AESPaper.PureBiasBounds
