import AESConcrete.ByteLineBounds

/-!
# Same-flag overlap of actual three-leg byte lines

The finite counting is proved here: for a fixed nonzero first parameter,
coordinate equality singles out one nonzero second parameter per slope ratio.
Three distinct ratios give three distinct points; a nonconstant triple has at
most a double point. The resulting spike sums are exact finite-sum identities.
The actual byte Gram diagonal and off-diagonal resources are then applied.

This file treats ordinary input flags only. Each leg has one fixed permitted
AES orientation, shared by the two line responses. Fourier transport, MDS
shortening geometry, and the activity-frame word bound are separate obligations.
Constructive proof support only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.LineOverlap
open AESMixing
open AESConcrete.ByteGramCore
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.DampedLineGram

section SpikeSums
variable {X : Type*} [Fintype X] [DecidableEq X]

def spike (d g : ℝ) (p z : X) : ℝ := if z = p then d else g

omit [Fintype X] in
private theorem spike_nonnegative (d g : ℝ) (hd : 0 ≤ d) (hg : 0 ≤ g)
    (p z : X) : 0 ≤ spike d g p z := by
  unfold spike
  split_ifs <;> assumption

/-- Three distinct equality points contribute three diagonal/off-diagonal
products. This is an exact sum identity, not an assumed cardinality. -/
theorem sum_three_spikes_distinct (d g : ℝ) (p₀ p₁ p₂ : X)
    (h₀₁ : p₀ ≠ p₁) (h₀₂ : p₀ ≠ p₂) (h₁₂ : p₁ ≠ p₂) :
    (∑ z, spike d g p₀ z * spike d g p₁ z * spike d g p₂ z) =
      3 * d * g^2 + ((Fintype.card X : ℝ) - 3) * g^3 := by
  have ht (z : X) : spike d g p₀ z * spike d g p₁ z * spike d g p₂ z =
      g^3 + (if z = p₀ then d*g^2-g^3 else 0) +
        (if z = p₁ then d*g^2-g^3 else 0) +
        (if z = p₂ then d*g^2-g^3 else 0) := by
    by_cases h₀ : z = p₀
    · subst z
      simp [spike, h₀₁, h₀₂]
      ring
    by_cases h₁ : z = p₁
    · subst z
      simp [spike, Ne.symm h₀₁, h₁₂]
      ring
    by_cases h₂ : z = p₂
    · subst z
      simp [spike, Ne.symm h₀₂, Ne.symm h₁₂]
      ring
    · simp [spike, h₀, h₁, h₂]
      ring
  simp_rw [ht, Finset.sum_add_distrib]
  simp
  ring

/-- A double equality point and a distinct single point give the exact
two-plus-one count needed for eta2. -/
theorem sum_three_spikes_double (d g : ℝ) (p q : X) (hpq : p ≠ q) :
    (∑ z, spike d g p z * spike d g p z * spike d g q z) =
      d^2*g + d*g^2 + ((Fintype.card X : ℝ) - 2)*g^3 := by
  have ht (z : X) : spike d g p z * spike d g p z * spike d g q z =
      g^3 + (if z = p then d^2*g-g^3 else 0) +
        (if z = q then d*g^2-g^3 else 0) := by
    by_cases hp : z = p
    · subst z
      -- Retain a ring equality rather than simplifying products into disjunctions.
      simp only [spike, if_pos rfl, if_neg hpq, add_zero, if_true]
      ring
    by_cases hq : z = q
    · subst z
      simp [spike, Ne.symm hpq]
      ring
    · simp [spike, hp, hq]
      ring
  simp_rw [ht, Finset.sum_add_distrib]
  simp
  ring

/-- A nonconstant triple of equality points has either three distinct
points or a double point and a single point. No triple point is admitted. -/
theorem sum_three_spikes_le_double (d g : ℝ) (hg : 0 ≤ g)
    (p₀ p₁ p₂ : X) (hnot : ¬ (p₀ = p₁ ∧ p₁ = p₂)) :
    (∑ z, spike d g p₀ z * spike d g p₁ z * spike d g p₂ z) ≤
      d^2*g + d*g^2 + ((Fintype.card X : ℝ) - 2)*g^3 := by
  by_cases h₀₁ : p₀ = p₁
  · subst p₁
    have h₀₂ : p₀ ≠ p₂ := by
      intro h
      exact hnot ⟨rfl, h⟩
    rw [sum_three_spikes_double d g p₀ p₂ h₀₂]
  by_cases h₀₂ : p₀ = p₂
  · subst p₂
    have he : (∑ z, spike d g p₀ z * spike d g p₁ z * spike d g p₀ z) =
        ∑ z, spike d g p₀ z * spike d g p₀ z * spike d g p₁ z := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    rw [he, sum_three_spikes_double d g p₀ p₁ h₀₁]
  by_cases h₁₂ : p₁ = p₂
  · subst p₂
    have he : (∑ z, spike d g p₀ z * spike d g p₁ z * spike d g p₁ z) =
        ∑ z, spike d g p₁ z * spike d g p₁ z * spike d g p₀ z := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    rw [he, sum_three_spikes_double d g p₁ p₀ (Ne.symm h₀₁)]
  rw [sum_three_spikes_distinct d g p₀ p₁ p₂ h₀₁ h₀₂ h₁₂]
  have hgap : 0 ≤ g * (d-g)^2 := mul_nonneg hg (sq_nonneg _)
  nlinarith [hgap]

theorem abs_triple_sum_le_spikes (d g : ℝ) (hd : 0 ≤ d) (hg : 0 ≤ g)
    (f₀ f₁ f₂ : X → ℝ) (p₀ p₁ p₂ : X)
    (h₀ : ∀ z, |f₀ z| ≤ spike d g p₀ z)
    (h₁ : ∀ z, |f₁ z| ≤ spike d g p₁ z)
    (h₂ : ∀ z, |f₂ z| ≤ spike d g p₂ z) :
    |∑ z, f₀ z * f₁ z * f₂ z| ≤
      ∑ z, spike d g p₀ z * spike d g p₁ z * spike d g p₂ z := by
  calc
    _ ≤ ∑ z, |f₀ z * f₁ z * f₂ z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro z _
      simp only [abs_mul]
      exact mul_le_mul
        (mul_le_mul (h₀ z) (h₁ z) (abs_nonneg _) (spike_nonnegative d g hd hg p₀ z))
        (h₂ z) (abs_nonneg _)
        (mul_nonneg (spike_nonnegative d g hd hg p₀ z)
          (spike_nonnegative d g hd hg p₁ z))

end SpikeSums

def delta : ℝ := 16766 / 4177920
def offdiag : ℝ := 319 / 4177920
def eta1 : ℝ := 65536 * 255 * (3*delta*offdiag^2 + 252*offdiag^3)
def eta2 : ℝ := 65536 * 255 *
  (delta^2*offdiag + delta*offdiag^2 + 253*offdiag^3)

theorem eta1_le_eta2 : eta1 ≤ eta2 := by
  have hg : 0 ≤ offdiag := by norm_num [offdiag]
  have hgap : 0 ≤ offdiag * (delta-offdiag)^2 := mul_nonneg hg (sq_nonneg _)
  unfold eta1 eta2
  nlinarith [hgap]

/-- Every actual nonzero column has the exact diagonal spike; all other
entries use the signed Gram interval, enlarged only to its absolute cap. -/
theorem actual_gram_spike (o : Orientation) (u v : Byte) (hu : u ≠ 0) :
    |residualGram (channel o) u v| ≤ if u = v then delta else offdiag := by
  by_cases huv : u = v
  · subst v
    rw [ByteGramDiagonal.actual_gram_diagonal, if_neg hu]
    norm_num [delta]
  · rw [if_neg huv]
    apply abs_le.mpr
    have h := ByteGramResources.actual_gram_offdiagonal o u v huv
    constructor
    · exact h.1
    · exact h.2.trans (by norm_num [offdiag])

/-- The coordinate equality is an actual field equation. -/
theorem slope_equality (a b x z : Byte) (hb : b ≠ 0) :
    a*x = b*z ↔ z = (a/b)*x := by
  constructor
  · intro h
    apply mul_left_cancel₀ hb
    calc
      b*z = a*x := h.symm
      _ = b*((a/b)*x) := by field_simp [hb]
  · intro h
    rw [h]
    field_simp [hb]

def ratioPoint (a b : Fin 3 → Byte) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (x : NonzeroByte) (i : Fin 3) : NonzeroByte :=
  ⟨(a i / b i)*x.val, mul_ne_zero (div_ne_zero (ha i) (hb i)) x.property⟩

def rowKernel (o : Fin 3 → Orientation) (a b : Fin 3 → Byte)
    (x z : NonzeroByte) : ℝ :=
  ∏ i : Fin 3, residualGram (channel (o i)) (a i*x.val) (b i*z.val)

theorem row_factor_spike (o : Fin 3 → Orientation) (a b : Fin 3 → Byte)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (x z : NonzeroByte) (i : Fin 3) :
    |residualGram (channel (o i)) (a i*x.val) (b i*z.val)| ≤
      spike delta offdiag (ratioPoint a b ha hb x i) z := by
  have heq : a i*x.val = b i*z.val ↔ z = ratioPoint a b ha hb x i := by
    constructor
    · intro h
      apply Subtype.ext
      exact (slope_equality (a i) (b i) x.val z.val (hb i)).mp h
    · intro h
      apply (slope_equality (a i) (b i) x.val z.val (hb i)).mpr
      exact congrArg Subtype.val h
  simpa only [spike, heq] using
    actual_gram_spike (o i) (a i*x.val) (b i*z.val) (mul_ne_zero (ha i) x.property)

theorem row_overlap_eta1 (o : Fin 3 → Orientation) (a b : Fin 3 → Byte)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hr : Function.Injective (fun i => a i / b i)) (x : NonzeroByte) :
    |∑ z : NonzeroByte, rowKernel o a b x z| ≤
      3*delta*offdiag^2 + 252*offdiag^3 := by
  let p := ratioPoint a b ha hb x
  have hp : Function.Injective p := by
    intro i j h
    apply hr
    exact mul_right_cancel₀ x.property (congrArg Subtype.val h)
  have hs := abs_triple_sum_le_spikes delta offdiag
    (by norm_num [delta]) (by norm_num [offdiag])
    (fun z : NonzeroByte => residualGram (channel (o 0)) (a 0*x.val) (b 0*z.val))
    (fun z : NonzeroByte => residualGram (channel (o 1)) (a 1*x.val) (b 1*z.val))
    (fun z : NonzeroByte => residualGram (channel (o 2)) (a 2*x.val) (b 2*z.val))
    (p 0) (p 1) (p 2)
    (fun z => row_factor_spike o a b ha hb x z 0)
    (fun z => row_factor_spike o a b ha hb x z 1)
    (fun z => row_factor_spike o a b ha hb x z 2)
  rw [sum_three_spikes_distinct delta offdiag (p 0) (p 1) (p 2)
    (hp.ne (by decide)) (hp.ne (by decide)) (hp.ne (by decide))] at hs
  norm_num [NonzeroByte, BinaryWord.card] at hs
  simpa [rowKernel, Fin.prod_univ_succ, mul_assoc] using hs

theorem row_overlap_eta2 (o : Fin 3 → Orientation) (a b : Fin 3 → Byte)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hr : ¬ (a 0 / b 0 = a 1 / b 1 ∧ a 1 / b 1 = a 2 / b 2)) (x : NonzeroByte) :
    |∑ z : NonzeroByte, rowKernel o a b x z| ≤
      delta^2*offdiag + delta*offdiag^2 + 253*offdiag^3 := by
  let p := ratioPoint a b ha hb x
  have hp : ¬ (p 0 = p 1 ∧ p 1 = p 2) := by
    intro h
    apply hr
    exact ⟨mul_right_cancel₀ x.property (congrArg Subtype.val h.1),
      mul_right_cancel₀ x.property (congrArg Subtype.val h.2)⟩
  have hs := abs_triple_sum_le_spikes delta offdiag
    (by norm_num [delta]) (by norm_num [offdiag])
    (fun z : NonzeroByte => residualGram (channel (o 0)) (a 0*x.val) (b 0*z.val))
    (fun z : NonzeroByte => residualGram (channel (o 1)) (a 1*x.val) (b 1*z.val))
    (fun z : NonzeroByte => residualGram (channel (o 2)) (a 2*x.val) (b 2*z.val))
    (p 0) (p 1) (p 2)
    (fun z => row_factor_spike o a b ha hb x z 0)
    (fun z => row_factor_spike o a b ha hb x z 1)
    (fun z => row_factor_spike o a b ha hb x z 2)
  have hc := sum_three_spikes_le_double delta offdiag (by norm_num [offdiag])
    (p 0) (p 1) (p 2) hp
  have ht := hs.trans hc
  norm_num [NonzeroByte, BinaryWord.card] at ht
  simpa [rowKernel, Fin.prod_univ_succ, mul_assoc] using ht

def rawOverlap (o : Fin 3 → Orientation) (a b : Fin 3 → Byte) : ℝ :=
  ∑ x : Byte, ∑ z : Byte,
    ∏ i : Fin 3, residualGram (channel (o i)) (a i*x) (b i*z)

theorem rawOverlap_nonzero (o : Fin 3 → Orientation) (a b : Fin 3 → Byte) :
    rawOverlap o a b = ∑ x : NonzeroByte, ∑ z : NonzeroByte, rowKernel o a b x z := by
  let F (x z : Byte) := ∏ i : Fin 3, residualGram (channel (o i)) (a i*x) (b i*z)
  have hx (z : Byte) : F 0 z = 0 := by
    simp [F, ByteGramDiagonal.actual_gram_zero_row, Fin.prod_univ_succ]
  have hz (x : Byte) : F x 0 = 0 := by
    simp [F, ByteGramDiagonal.actual_gram_zero_column, Fin.prod_univ_succ]
  change (∑ x : Byte, ∑ z : Byte, F x z) = _
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun x : Byte => ∑ z : Byte, F x z) 0]
  simp only [hx, Finset.sum_const_zero, zero_add]
  apply Finset.sum_congr rfl
  intro x _
  change (∑ z : Byte, F x.val z) = ∑ z : NonzeroByte, F x.val z.val
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun z : Byte => F x.val z) 0, hz, zero_add]

private theorem nonzero_sum_const (c : ℝ) : (∑ _ : NonzeroByte, c) = 255*c := by
  norm_num [NonzeroByte, BinaryWord.card]

theorem rawOverlap_eta1 (o : Fin 3 → Orientation) (a b : Fin 3 → Byte)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hr : Function.Injective (fun i => a i / b i)) :
    |rawOverlap o a b| ≤ 255 * (3*delta*offdiag^2 + 252*offdiag^3) := by
  rw [rawOverlap_nonzero]
  calc
    _ ≤ ∑ x : NonzeroByte, |∑ z : NonzeroByte, rowKernel o a b x z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : NonzeroByte, (3*delta*offdiag^2 + 252*offdiag^3) :=
      Finset.sum_le_sum (fun x _ => row_overlap_eta1 o a b ha hb hr x)
    _ = _ := nonzero_sum_const _

theorem rawOverlap_eta2 (o : Fin 3 → Orientation) (a b : Fin 3 → Byte)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hr : ¬ (a 0 / b 0 = a 1 / b 1 ∧ a 1 / b 1 = a 2 / b 2)) :
    |rawOverlap o a b| ≤ 255 *
      (delta^2*offdiag + delta*offdiag^2 + 253*offdiag^3) := by
  rw [rawOverlap_nonzero]
  calc
    _ ≤ ∑ x : NonzeroByte, |∑ z : NonzeroByte, rowKernel o a b x z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : NonzeroByte, (delta^2*offdiag + delta*offdiag^2 + 253*offdiag^3) :=
      Finset.sum_le_sum (fun x _ => row_overlap_eta2 o a b ha hb hr x)
    _ = _ := nonzero_sum_const _

def slopeEquiv (a : Fin 3 → Byte) (ha : ∀ i, a i ≠ 0) : Fin 3 → Equiv.Perm Byte :=
  fun i => Equiv.mulLeft₀ (a i) (ha i)

/-- Actual q-scaled ordinary-flag line pair with three distinct slope ratios.
The response normalization is exactly 1/256 and q is exactly 2^32. -/
theorem actual_line_pair_eta1 (o : Fin 3 → Orientation) (a b : Fin 3 → Byte)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hr : Function.Injective (fun i => a i / b i)) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineResponse (fun i => leg (o i) false) (slopeEquiv a ha) y *
      lineResponse (fun i => leg (o i) false) (slopeEquiv b hb) y| ≤ eta1 := by
  rw [lineResponse_inner]
  change (4294967296 : ℝ) * |rawOverlap o a b / (Fintype.card Byte : ℝ)^2| ≤ eta1
  rw [abs_div, abs_of_nonneg (sq_nonneg (Fintype.card Byte : ℝ))]
  have h := rawOverlap_eta1 o a b ha hb hr
  norm_num [BinaryWord.card] at *
  unfold eta1
  linarith

/-- Actual q-scaled ordinary-flag pair of distinct lines. A double slope
ratio is allowed, but a common ratio in all three legs is excluded. -/
theorem actual_line_pair_eta2 (o : Fin 3 → Orientation) (a b : Fin 3 → Byte)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hr : ¬ (a 0 / b 0 = a 1 / b 1 ∧ a 1 / b 1 = a 2 / b 2)) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineResponse (fun i => leg (o i) false) (slopeEquiv a ha) y *
      lineResponse (fun i => leg (o i) false) (slopeEquiv b hb) y| ≤ eta2 := by
  rw [lineResponse_inner]
  change (4294967296 : ℝ) * |rawOverlap o a b / (Fintype.card Byte : ℝ)^2| ≤ eta2
  rw [abs_div, abs_of_nonneg (sq_nonneg (Fintype.card Byte : ℝ))]
  have h := rawOverlap_eta2 o a b ha hb hr
  norm_num [BinaryWord.card] at *
  unfold eta2
  linarith

end AESConcrete.LineOverlap
