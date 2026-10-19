import AESConcrete.ByteGramFourier
import AESConcrete.Generated.ByteGramFinite

/-!
# Signed actual byte Gram resources

The finite numerator is connected to the actual inversion residual Gram
before its finite row sums are used. Actual AES orientations are then
transported by proved additive relabelings. All sums use counting measure;
the cube sum is over all ordered byte pairs. This is a local prerequisite
for the damped degree-three word proof, not that word bound itself.
Constructive proof support only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ByteGramResources
open AESMixing
open AESConcrete.ByteGramCore
open AESConcrete.ByteGramFourier
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteOrientations (Orientation channel)

def squareNumerator : ℝ := 16766^2 + 70 * 191^2 + 112 * 64^2 + 72 * 319^2
def cubeNumerator : ℝ := 16766^3 + 70 * 191^3 + 112 * 64^3 + 72 * 319^3

theorem traceSign_cast (c : Byte) :
    (ByteGramFinite.traceSign c.bits : ℝ) = byteCharacter c := by
  unfold ByteGramFinite.traceSign byteCharacter
  split_ifs <;> norm_num

theorem traceSign_inv_cast (c : Byte) :
    (ByteGramFinite.traceSign (AES.invLookup c.bits) : ℝ) = byteCharacter c⁻¹ := by
  rw [AES.invLookup_correct]
  unfold ByteGramFinite.traceSign byteCharacter
  rw [BinaryWord.inv_bits]
  split_ifs <;> norm_num

/-- Real form of the integer profile. The factor two in the finite
certificate is removed over the reals, without integer truncation. -/
theorem numerator_real_formula (c : Byte) (hc : c ≠ 0) :
    (ByteGramFinite.numerator c.bits : ℝ) =
      -64 + (255 / 2 : ℝ) * (byteCharacter c + byteCharacter c⁻¹) +
        16575 * (if c = 1 then 1 else 0) := by
  have hc0 : c.bits ≠ 0 := by
    intro h
    exact hc (BinaryWord.ext h)
  have hc1 : c.bits = 1 ↔ c = 1 := by
    constructor
    · exact fun h => BinaryWord.ext h
    · rintro rfl
      rfl
  have h := congrArg (fun z : ℤ => (z : ℝ)) (ByteGramFinite.numerator_twice c.bits hc0)
  push_cast at h
  rw [traceSign_cast, traceSign_inv_cast] at h
  simp only [hc1] at h
  linarith

/-- Every actual inversion-Gram entry is the checked numerator at its
multiplicative ratio. Total field division also handles the zero row. -/
theorem inversion_gram_ratio (a b : Byte) :
    inversionGram a b = (ByteGramFinite.numerator (b / a).bits : ℝ) / 4177920 := by
  by_cases ha : a = 0
  · subst a
    rw [inversion_gram_zero_row, div_zero]
    change 0 = (ByteGramFinite.numerator 0 : ℝ) / 4177920
    rw [ByteGramFinite.numerator_zero]
    norm_num
  by_cases hb : b = 0
  · subst b
    rw [inversion_gram_zero_column, zero_div]
    change 0 = (ByteGramFinite.numerator 0 : ℝ) / 4177920
    rw [ByteGramFinite.numerator_zero]
    norm_num
  have hc : b / a ≠ 0 := div_ne_zero hb ha
  have hc1 : b / a = 1 ↔ a = b := by
    constructor
    · intro h
      exact ((div_eq_one_iff_eq ha).mp h).symm
    · rintro rfl
      exact div_self ha
  have hinv : (b / a)⁻¹ = a / b := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  rw [inversion_gram_nonzero a b ha hb, numerator_real_formula _ hc, hinv]
  simp only [hc1]
  split_ifs <;> ring

theorem inversion_gram_offdiagonal (a b : Byte) (hab : a ≠ b) :
    -(319 / 4177920 : ℝ) ≤ inversionGram a b ∧
      inversionGram a b ≤ (191 / 4177920 : ℝ) := by
  by_cases ha : a = 0
  · subst a
    rw [inversion_gram_zero_row]
    norm_num
  by_cases hb : b = 0
  · subst b
    rw [inversion_gram_zero_column]
    norm_num
  have hc0 : (b / a).bits ≠ 0 := by
    intro h
    exact div_ne_zero hb ha (BinaryWord.ext h)
  have hc1 : (b / a).bits ≠ 1 := by
    intro h
    have hdiv : b / a = 1 := BinaryWord.ext h
    exact hab ((div_eq_one_iff_eq ha).mp hdiv).symm
  rw [inversion_gram_ratio]
  rcases ByteGramFinite.numerator_offdiagonal_values (b / a).bits hc0 hc1 with h | h | h
  · rw [h]
    norm_num
  · rw [h]
    norm_num
  · rw [h]
    norm_num

theorem actual_gram_offdiagonal (o : Orientation) (a b : Byte) (hab : a ≠ b) :
    -(319 / 4177920 : ℝ) ≤ residualGram (channel o) a b ∧
      residualGram (channel o) a b ≤ (191 / 4177920 : ℝ) := by
  rw [actual_gram_relabel]
  apply inversion_gram_offdiagonal
  intro h
  exact hab ((gramRelabel o).injective h)

private theorem numerator_square_sum_real :
    (∑ c : Byte, (ByteGramFinite.numerator c.bits : ℝ) ^ 2) = squareNumerator := by
  have h := Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun c : Byte => (ByteGramFinite.numerator c.bits : ℝ) ^ 2)
  rw [← h]
  have hf : (∑ c : Fin 256, (ByteGramFinite.numeratorFin c : ℝ) ^ 2) =
      (16766 : ℝ)^2 + 70 * 191^2 + 112 * 64^2 + 72 * 319^2 := by
    exact_mod_cast ByteGramFinite.numerator_square_sum
  exact hf

private theorem numerator_cube_sum_real :
    (∑ c : Byte, |(ByteGramFinite.numerator c.bits : ℝ)| ^ 3) = cubeNumerator := by
  have h := Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun c : Byte => |(ByteGramFinite.numerator c.bits : ℝ)| ^ 3)
  rw [← h]
  have hf : (∑ c : Fin 256, ((ByteGramFinite.numeratorFin c).natAbs : ℝ) ^ 3) =
      (16766 : ℝ)^3 + 70 * 191^3 + 112 * 64^3 + 72 * 319^3 := by
    exact_mod_cast ByteGramFinite.numerator_abs_cube_sum
  have habs (n : ℤ) : (n.natAbs : ℝ) = |(n : ℝ)| := by
    cases n <;> simp
    rename_i n
    rw [abs_of_nonpos (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)]
    ring
  simp only [habs] at hf
  exact hf

theorem inversion_gram_row_square (a : Byte) (ha : a ≠ 0) :
    (∑ b, inversionGram a b ^ 2) = squareNumerator / 4177920^2 := by
  have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha) (fun b => inversionGram a b ^ 2)
  calc
    _ = ∑ c : Byte, inversionGram a (a * c) ^ 2 := he.symm
    _ = _ := ?_
  have hr (c : Byte) : inversionGram a (a * c) =
      (ByteGramFinite.numerator c.bits : ℝ) / 4177920 := by
    rw [inversion_gram_ratio]
    have hquot : (a * c) / a = c := by field_simp [ha]
    rw [hquot]
  simp_rw [hr, div_pow]
  rw [← Finset.sum_div, numerator_square_sum_real]

theorem inversion_gram_row_cube (a : Byte) (ha : a ≠ 0) :
    (∑ b, |inversionGram a b| ^ 3) = cubeNumerator / 4177920^3 := by
  have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha) (fun b => |inversionGram a b| ^ 3)
  calc
    _ = ∑ c : Byte, |inversionGram a (a * c)| ^ 3 := he.symm
    _ = _ := ?_
  have hr (c : Byte) : inversionGram a (a * c) =
      (ByteGramFinite.numerator c.bits : ℝ) / 4177920 := by
    rw [inversion_gram_ratio]
    have hquot : (a * c) / a = c := by field_simp [ha]
    rw [hquot]
  simp_rw [hr, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4177920), div_pow]
  rw [← Finset.sum_div, numerator_cube_sum_real]

private theorem nonzero_sum_const (c : ℝ) : (∑ _ : NonzeroByte, c) = 255 * c := by
  have h := Fintype.sum_eq_add_sum_subtype_ne (fun _ : Byte => c) 0
  norm_num only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, BinaryWord.card] at h ⊢
  linarith

theorem inversion_gram_square_moment :
    (∑ a, ∑ b, inversionGram a b ^ 2) = (571447 / 2^27 : ℝ) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun a => ∑ b, inversionGram a b ^ 2) 0]
  simp only [inversion_gram_zero_row, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_add]
  have hr (a : NonzeroByte) : (∑ b, inversionGram a.val b ^ 2) =
      squareNumerator / 4177920^2 := inversion_gram_row_square a.val a.property
  simp_rw [hr]
  rw [nonzero_sum_const]
  norm_num [squareNumerator]

theorem inversion_gram_absolute_cube :
    (∑ a, ∑ b, |inversionGram a b| ^ 3) =
      (255 : ℝ) * cubeNumerator / 4177920^3 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun a => ∑ b, |inversionGram a b| ^ 3) 0]
  simp only [inversion_gram_zero_row, abs_zero, zero_pow (by decide : 3 ≠ 0),
    Finset.sum_const_zero, zero_add]
  have hr (a : NonzeroByte) : (∑ b, |inversionGram a.val b| ^ 3) =
      cubeNumerator / 4177920^3 := inversion_gram_row_cube a.val a.property
  simp_rw [hr]
  rw [nonzero_sum_const]
  ring

/-- The full ordered-pair second Gram moment; Gram symmetry identifies it
with Tr(G^2). The exact value follows from the checked finite row. -/
theorem actual_gram_square_moment (o : Orientation) :
    (∑ a, ∑ b, residualGram (channel o) a b ^ 2) = (571447 / 2^27 : ℝ) := by
  simp_rw [actual_gram_relabel]
  have hi (a : Byte) : (∑ b, inversionGram (gramRelabel o a) (gramRelabel o b) ^ 2) =
      ∑ b, inversionGram (gramRelabel o a) b ^ 2 :=
    Equiv.sum_comp (gramRelabel o).toEquiv (fun b => inversionGram (gramRelabel o a) b ^ 2)
  simp_rw [hi]
  exact (Equiv.sum_comp (gramRelabel o).toEquiv
    (fun a => ∑ b, inversionGram a b ^ 2)).trans inversion_gram_square_moment

/-- Global absolute-cube resource, including each diagonal and both orders
of every pair. A different fixed orientation may be chosen on each leg. -/
theorem actual_gram_absolute_cube (o : Orientation) :
    (∑ a, ∑ b, |residualGram (channel o) a b| ^ 3) =
      (255 : ℝ) * cubeNumerator / 4177920^3 := by
  simp_rw [actual_gram_relabel]
  have hi (a : Byte) : (∑ b, |inversionGram (gramRelabel o a) (gramRelabel o b)| ^ 3) =
      ∑ b, |inversionGram (gramRelabel o a) b| ^ 3 :=
    Equiv.sum_comp (gramRelabel o).toEquiv (fun b => |inversionGram (gramRelabel o a) b| ^ 3)
  simp_rw [hi]
  exact (Equiv.sum_comp (gramRelabel o).toEquiv
    (fun a => ∑ b, |inversionGram a b| ^ 3)).trans inversion_gram_absolute_cube

theorem actual_gram_square_moment_le (o : Orientation) :
    (∑ a, ∑ b, residualGram (channel o) a b ^ 2) ≤ (571447 / 2^27 : ℝ) :=
  le_of_eq (actual_gram_square_moment o)

theorem actual_gram_absolute_cube_le (o : Orientation) :
    (∑ a, ∑ b, |residualGram (channel o) a b| ^ 3) ≤
      (255 : ℝ) * (16766^3 + 70 * 191^3 + 112 * 64^3 + 72 * 319^3) / 4177920^3 := by
  exact le_of_eq (actual_gram_absolute_cube o)

end AESConcrete.ByteGramResources
