import AESMixing.L2Sums

/-!
# The common three/four factor inequality (eq:thin-holder-sum)

Counting measure throughout. Repeated Cauchy--Schwarz avoids fractional powers,
including at zero moment caps. No AES instances or numerical resources are assumed.
This leaf supplies raw scalar sums; fiber normalization and overlap operators
belong to separate components. Constructive proofs only; no attacks.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperThinHolder
variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Cauchy--Schwarz with a common squared-moment cap. -/
theorem common_second (f g : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : (∑ x, f x ^ 2) ≤ B) (hg : (∑ x, g x ^ 2) ≤ B) :
    (∑ x, f x * g x) ≤ B := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have hb := mul_le_mul hf hg
    (Finset.sum_nonneg (fun x _ => sq_nonneg (g x))) hB
  nlinarith [sq_nonneg ((∑ x, f x * g x) - B)]

/-- Two fourth moments bound the squared energy of a product. -/
theorem pair_energy (f g : X → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : (∑ x, f x ^ 4) ≤ B) (hg : (∑ x, g x ^ 4) ≤ B) :
    (∑ x, (f x * g x) ^ 2) ≤ B := by
  have h := common_second (fun x => f x ^ 2) (fun x => g x ^ 2) B hB
    (by simpa only [← pow_mul] using hf)
    (by simpa only [← pow_mul] using hg)
  simpa only [mul_pow] using h

/-- Three factors: only the first second moment and last two fourth moments
are needed. In particular the manuscript's uniform hypotheses suffice. -/
theorem three (f g h : X → ℝ) (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p)
    (hf : (∑ x, f x ^ 2) ≤ H)
    (hg : (∑ x, g x ^ 4) ≤ p ^ 2 * H)
    (hh : (∑ x, h x ^ 4) ≤ p ^ 2 * H) :
    (∑ x, f x * g x * h x) ≤ H * p := by
  have he := pair_energy g h (p ^ 2 * H) (mul_nonneg (sq_nonneg p) hH) hg hh
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f (fun x => g x * h x)
  have hb := mul_le_mul hf he
    (Finset.sum_nonneg (fun x _ => sq_nonneg (g x * h x))) hH
  have hn : 0 ≤ H * p := mul_nonneg hH hp
  simp only [← mul_assoc] at hcs
  nlinarith [sq_nonneg ((∑ x, f x * g x * h x) - H * p)]

/-- Four factors: second moments are unnecessary once fourth moments are given. -/
theorem four (f g h l : X → ℝ) (H p : ℝ) (hH : 0 ≤ H)
    (hf : (∑ x, f x ^ 4) ≤ p ^ 2 * H)
    (hg : (∑ x, g x ^ 4) ≤ p ^ 2 * H)
    (hh : (∑ x, h x ^ 4) ≤ p ^ 2 * H)
    (hl : (∑ x, l x ^ 4) ≤ p ^ 2 * H) :
    (∑ x, f x * g x * h x * l x) ≤ H * p ^ 2 := by
  have hB := mul_nonneg (sq_nonneg p) hH
  have hbound := common_second (fun x => f x * g x) (fun x => h x * l x)
    (p ^ 2 * H) hB (pair_energy f g _ hB hf hg) (pair_energy h l _ hB hh hl)
  simpa only [← mul_assoc, mul_comm H] using hbound

/-- Exact moment transport: no cardinality multiplier occurs. -/
theorem moment_transport (e : X ≃ Y) (f : Y → ℝ) (n : ℕ) :
    (∑ x, f (e x) ^ n) = ∑ y, f y ^ n :=
  e.sum_comp (fun y => f y ^ n)

/-- Different coordinate bijections and different local maps are allowed. -/
theorem three_transport (e : Fin 3 → X ≃ Y) (f : Fin 3 → Y → ℝ)
    (H p : ℝ) (hH : 0 ≤ H) (hp : 0 ≤ p)
    (h2 : ∀ j, (∑ y, f j y ^ 2) ≤ H)
    (h4 : ∀ j, (∑ y, f j y ^ 4) ≤ p ^ 2 * H) :
    (∑ x, f 0 (e 0 x) * f 1 (e 1 x) * f 2 (e 2 x)) ≤ H * p := by
  apply three _ _ _ H p hH hp
  · simpa only [moment_transport] using h2 0
  · simpa only [moment_transport] using h4 1
  · simpa only [moment_transport] using h4 2

theorem four_transport (e : Fin 4 → X ≃ Y) (f : Fin 4 → Y → ℝ)
    (H p : ℝ) (hH : 0 ≤ H)
    (h4 : ∀ j, (∑ y, f j y ^ 4) ≤ p ^ 2 * H) :
    (∑ x, f 0 (e 0 x) * f 1 (e 1 x) * f 2 (e 2 x) * f 3 (e 3 x))
      ≤ H * p ^ 2 := by
  apply four _ _ _ _ H p hH
  · simpa only [moment_transport] using h4 0
  · simpa only [moment_transport] using h4 1
  · simpa only [moment_transport] using h4 2
  · simpa only [moment_transport] using h4 3
end AES8.PaperThinHolder
