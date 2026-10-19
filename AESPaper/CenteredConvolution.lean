import AESMixing.Convolution

/-!
# Full-uniform centered convolution on a finite additive group

The reference is uniform on the entire group, including zero. Counting-measure
centered energy therefore equals collision minus `1/card` for a unit-mass law.
Signed unit-mass laws satisfy the centered convolution product estimate;
nonnegative unit-mass laws additionally contract centered energy. The product
estimate uses the frozen signed Cauchy--Schwarz convolution bound directly.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators

namespace AESPaper.CenteredConvolution
open AESMixing

variable {V : Type*} [Fintype V] [AddCommGroup V]

/-- Full-group uniform law; this includes the distinguished zero element. -/
def uniform : V → ℝ := fun _ => 1 / (Fintype.card V : ℝ)

def centered (f : V → ℝ) (x : V) : ℝ := f x - uniform x

def centeredEnergy (f : V → ℝ) : ℝ := ∑ x, centered f x ^ 2

theorem real_card_pos : 0 < (Fintype.card V : ℝ) := by
  exact_mod_cast Fintype.card_pos

theorem real_card_ne_zero : (Fintype.card V : ℝ) ≠ 0 :=
  ne_of_gt real_card_pos

theorem uniform_mass : (∑ x : V, uniform x) = 1 := by
  simp [uniform, nsmul_eq_mul, real_card_ne_zero]

theorem uniform_nonnegative (x : V) : 0 ≤ uniform x := by
  exact div_nonneg (by norm_num) (le_of_lt real_card_pos)

theorem centered_mass (f : V → ℝ) (hm : ∑ x, f x = 1) :
    (∑ x, centered f x) = 0 := by
  simp only [centered, Finset.sum_sub_distrib, hm, uniform_mass, sub_self]

theorem centeredEnergy_nonnegative (f : V → ℝ) : 0 ≤ centeredEnergy f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Unit mass is the only hypothesis; source-law nonnegativity is unnecessary. -/
theorem centeredEnergy_eq_collision_sub (f : V → ℝ) (hm : ∑ x, f x = 1) :
    centeredEnergy f = (∑ x, f x ^ 2) - 1 / (Fintype.card V : ℝ) := by
  unfold centeredEnergy centered uniform
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hm]
  field_simp [real_card_ne_zero] <;> ring

theorem convolution_mass (p q : V → ℝ) :
    (∑ y, convolution p q y) = (∑ x, p x) * ∑ x, q x := by
  have ht (x : V) : (∑ y, q (y - x)) = ∑ y, q y :=
    Equiv.sum_comp (Equiv.subRight x) q
  unfold convolution
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ht]
  exact (Finset.sum_mul ..).symm

theorem convolution_unit_mass (p q : V → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    (∑ y, convolution p q y) = 1 := by
  rw [convolution_mass, hp, hq, mul_one]

theorem convolution_nonnegative (p q : V → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x) (y : V) :
    0 ≤ convolution p q y :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (hq (y - x)))

theorem convolution_comm (p q : V → ℝ) : convolution p q = convolution q p := by
  funext y
  have h := Equiv.sum_comp (Equiv.subLeft y) (fun x => p x * q (y - x))
  change (∑ x, p (y - x) * q (y - (y - x))) =
    ∑ x, p x * q (y - x) at h
  have hs (x : V) : y - (y - x) = x := by abel
  simp_rw [hs] at h
  unfold convolution
  calc
    _ = ∑ x, p (y - x) * q x := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- A unit-mass left law preserves the full-uniform reference. -/
theorem centered_convolution_of_left_mass (p q : V → ℝ)
    (hp : ∑ x, p x = 1) :
    centered (convolution p q) = convolution p (centered q) := by
  funext y
  change (∑ x, p x * q (y - x)) - 1 / (Fintype.card V : ℝ) =
    ∑ x, p x * (q (y - x) - 1 / (Fintype.card V : ℝ))
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]

/-- For unit-mass laws, centering both factors centers their convolution. -/
theorem centered_convolution (p q : V → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    centered (convolution p q) = convolution (centered p) (centered q) := by
  funext y
  have hshift : (∑ x, q (y - x)) = 1 :=
    (Equiv.sum_comp (Equiv.subLeft y) q).trans hq
  change (∑ x, p x * q (y - x)) - 1 / (Fintype.card V : ℝ) =
    ∑ x, (p x - 1 / (Fintype.card V : ℝ)) *
      (q (y - x) - 1 / (Fintype.card V : ℝ))
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hp, hshift]
  field_simp [real_card_ne_zero] <;> ring

/-- Summing the frozen pointwise signed convolution estimate gives the
cardinality loss, with full-uniform centering on both sides. -/
theorem centeredEnergy_convolution_le (p q : V → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    centeredEnergy (convolution p q) ≤
      (Fintype.card V : ℝ) * centeredEnergy p * centeredEnergy q := by
  change (∑ y, centered (convolution p q) y ^ 2) ≤ _
  rw [centered_convolution p q hp hq]
  calc
    _ ≤ ∑ _y : V, centeredEnergy p * centeredEnergy q :=
      Finset.sum_le_sum (fun y _ => convolution_atom_sq_le (centered p) (centered q) y)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Averaging translated copies contracts the other factor's centered energy. -/
theorem centeredEnergy_convolution_le_right (p q : V → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hm : ∑ x, p x = 1) :
    centeredEnergy (convolution p q) ≤ centeredEnergy q := by
  change (∑ y, centered (convolution p q) y ^ 2) ≤ _
  rw [centered_convolution_of_left_mass p q hm]
  exact convolution_collision_le p (centered q) hp hm

theorem centeredEnergy_convolution_le_left (p q : V → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hm : ∑ x, q x = 1) :
    centeredEnergy (convolution p q) ≤ centeredEnergy p := by
  rw [convolution_comm p q]
  exact centeredEnergy_convolution_le_right q p hq hm

end AESPaper.CenteredConvolution
