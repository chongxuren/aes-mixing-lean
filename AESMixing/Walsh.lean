import AESMixing.Gram

/-! Unnormalized real Fourier matrices on Boolean cubes. Orthogonality is
proved for every dimension by factorization into one-bit sums. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

abbrev BooleanCube (n : ℕ) := Fin n → Bool

def bitCharacter (a x : Bool) : ℝ := if a && x then -1 else 1

def walsh {n : ℕ} (a x : BooleanCube n) : ℝ := ∏ i, bitCharacter (a i) (x i)

theorem bitCharacter_symmetric (a x : Bool) : bitCharacter a x = bitCharacter x a := by
  cases a <;> cases x <;> rfl

theorem bitCharacter_orthogonal (a b : Bool) :
    (∑ x : Bool, bitCharacter a x * bitCharacter b x) = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [bitCharacter, Fintype.sum_bool]

theorem walsh_symmetric {n : ℕ} (a x : BooleanCube n) : walsh a x = walsh x a := by
  simp only [walsh, bitCharacter_symmetric]

theorem walsh_orthogonal {n : ℕ} (a b : BooleanCube n) :
    (∑ x : BooleanCube n, walsh a x * walsh b x) =
      if a = b then (2 : ℝ) ^ n else 0 := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (x : Bool) => bitCharacter (a i) x * bitCharacter (b i) x)]
  simp_rw [bitCharacter_orthogonal]
  by_cases hab : a = b
  · subst b; simp
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem walsh_gram {n : ℕ} (a b : BooleanCube n) :
    gram (@walsh n) a b = if a = b then (2 : ℝ) ^ n else 0 := by
  unfold gram
  simp_rw [walsh_symmetric (a := _) (x := a), walsh_symmetric (a := _) (x := b)]
  exact walsh_orthogonal a b

theorem walsh_energy {n : ℕ} (f : BooleanCube n → ℝ) :
    (∑ a, (∑ x, walsh a x * f x) ^ 2) = (2 : ℝ) ^ n * ∑ x, f x ^ 2 := by
  rw [gram_quadratic]
  simp_rw [walsh_gram, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

def cubeXor {n : ℕ} (a b : BooleanCube n) : BooleanCube n := fun i => xor (a i) (b i)

theorem bitCharacter_xor (a x y : Bool) :
    bitCharacter a (xor x y) = bitCharacter a x * bitCharacter a y := by
  cases a <;> cases x <;> cases y <;> norm_num [bitCharacter]

theorem walsh_xor {n : ℕ} (a x y : BooleanCube n) :
    walsh a (cubeXor x y) = walsh a x * walsh a y := by
  simp only [walsh, cubeXor, bitCharacter_xor, Finset.prod_mul_distrib]

theorem bitCharacter_sq (a x : Bool) : bitCharacter a x ^ 2 = 1 := by
  cases a <;> cases x <;> norm_num [bitCharacter]

theorem walsh_sq {n : ℕ} (a x : BooleanCube n) : walsh a x ^ 2 = 1 := by
  simp only [walsh, ← Finset.prod_pow, bitCharacter_sq, Finset.prod_const_one]

theorem walsh_zero {n : ℕ} (x : BooleanCube n) : walsh (fun _ => false) x = 1 := by
  simp [walsh, bitCharacter]

theorem walsh_involution {n : ℕ} (f : BooleanCube n → ℝ) (a : BooleanCube n) :
    (∑ x, walsh a x * ∑ b, walsh x b * f b) = (2 : ℝ)^n * f a := by
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hc (b : BooleanCube n) : (∑ x, walsh a x * walsh x b) =
      if a = b then (2 : ℝ)^n else 0 := by
    simp_rw [walsh_symmetric (a := _) (x := b)]
    exact walsh_orthogonal a b
  simp_rw [hc]
  simp

end AESMixing
