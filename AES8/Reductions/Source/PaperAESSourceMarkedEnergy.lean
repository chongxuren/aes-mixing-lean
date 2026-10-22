import AES8.Reductions.Source.PaperAESSourceResidual
import AESConcrete.ActualPositiveColumnDegrees

/-!
# Combined positive residual energy by marked positions

Section 11 pays for two residual positions if there are no prescribed zeros,
and for one ordered zero/residual pair otherwise. The remaining positions
have two or three choices. We reuse the established orthogonal physical
support decomposition and its exact support cardinalities. No legacy
per-degree numerical table or final column majorant is assumed.
Constructive verification only; no attacks or searches.
-/

noncomputable section
set_option maxRecDepth 100000
open scoped BigOperators

namespace AES8.PaperAESSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.ColumnSupportAggregation (supportCap)

attribute [local instance] Classical.propDecidable

def X : ℝ := 255 * (65 / 8192) * (9 / 128)^2
def Y : ℝ := 255 * ((65 / 8192) - 1 / 255)
def C : ℝ := 255 * (1 / 64)^2

theorem marked_scalars : 0 ≤ X ∧ 0 ≤ Y ∧ 0 ≤ C ∧ X ≤ Y := by
  norm_num [X, Y, C]

theorem nonzero_of_two_active (a : Word) (ht : 2 ≤ (active a).card) : a ≠ 0 := by
  apply AESConcrete.ActualZeroEventProbabilities.input_nonzero_of_active_count a
    (AESConcrete.AllColumnBound.inputZeroMask a)
    (fun i => (AESConcrete.AllColumnBound.inputZeroMask_bit a i).symm)
  rw [active_card] at ht
  omega

/-- The zero-free branch marks a residual pair (except at degree one).
The branch with zeros marks an ordered zero/residual pair. -/
def markedWeight (x y c : ℝ) (z j : ℕ) : ℝ :=
  if z = 0 then (if j = 1 then x else x^2 * y^(j-2))
  else c^z * x * y^(j-1)

theorem markedWeight_nonneg (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c)
    (z j : ℕ) : 0 ≤ markedWeight x y c z j := by
  unfold markedWeight
  split_ifs <;> positivity

/-- Replacing some operator factors by column factors only increases the
nonnegative monomial when `x ≤ y`. -/
theorem mixed_monomial_le (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y)
    (j k m : ℕ) (hm : m ≤ k) (hk : k ≤ j) :
    x^k * y^(j-k) ≤ x^m * y^(j-m) := by
  have hy : 0 ≤ y := hx.trans hxy
  have he : k = m + (k-m) := by omega
  have hj : j-m = (k-m) + (j-k) := by omega
  have hp := pow_le_pow_left₀ hx hxy (k-m)
  calc
    x^k * y^(j-k) = x^m * x^(k-m) * y^(j-k) := by rw [← pow_add, ← he]
    _ ≤ x^m * y^(k-m) * y^(j-k) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (pow_nonneg hx _))
        (pow_nonneg hy _)
    _ = _ := by rw [hj, pow_add]; ring

/-- Clearing the physical constant-coordinate normalization leaves one
factor 255 for every zero or residual position. -/
theorem supportCap_eq_scaled (t z j : ℕ) (h : z+j ≤ 4) :
    supportCap t z j =
      if z < t then C^z * X^(min (t-z) j) * Y^(j-min (t-z) j) / 255^4 else 0 := by
  unfold supportCap
  split_ifs with hz
  · let k := min (t-z) j
    have hk : k ≤ j := Nat.min_le_right _ _
    have hp : (255 : ℝ)^4 =
        255^z * 255^k * 255^(j-k) * 255^(4-(z+j)) := by
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    change _ = C^z * X^k * Y^(j-k) / 255^4
    have hd : AESConcrete.MultibyteColumnNumbers.delta = (65 / 8192 : ℝ) - 1 / 255 := by
      norm_num [AESConcrete.MultibyteColumnNumbers.delta]
    rw [hd]
    dsimp [C, X, Y, AESConcrete.MultibyteColumnNumbers.atom,
      AESConcrete.MultibyteColumnNumbers.rho, AESConcrete.MultibyteColumnNumbers.nu]
    rw [hp]
    simp only [mul_pow, ← pow_mul]
    field_simp
    ring
  · rfl

/-- Every possible support has at least the marked free-source factors.
The impossible branch contributes zero. -/
theorem supportCap_le_marked (t z j : ℕ) (ht : 2 ≤ t) (hj : 1 ≤ j)
    (h : z+j ≤ 4) :
    supportCap t z j ≤ markedWeight X Y C z j / 255^4 := by
  obtain ⟨hx,hy,hc,hxy⟩ := marked_scalars
  rw [supportCap_eq_scaled t z j h]
  by_cases hz : z < t
  · rw [if_pos hz]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    by_cases hz0 : z = 0
    · subst z
      simp only [pow_zero, one_mul, markedWeight, if_true, Nat.sub_zero]
      by_cases hj1 : j = 1
      · subst j
        simp only [Nat.min_eq_right (by omega : 1 ≤ t), Nat.sub_self, pow_one,
          pow_zero, mul_one, if_true]
        exact le_rfl
      · rw [if_neg hj1]
        exact mixed_monomial_le X Y hx hxy j (min t j) 2
          (Nat.le_min.mpr ⟨ht, by omega⟩) (Nat.min_le_right _ _)
    · rw [markedWeight, if_neg hz0]
      simpa only [pow_one, mul_assoc] using mul_le_mul_of_nonneg_left
        (mixed_monomial_le X Y hx hxy j (min (t-z) j) 1
          (Nat.le_min.mpr ⟨by omega, hj⟩) (Nat.min_le_right _ _)) (pow_nonneg hc _)
  · rw [if_neg hz]
    exact div_nonneg (markedWeight_nonneg X Y C hx hy hc z j) (by norm_num)

/-- This bound on the physical support component uses the current source
route above; the existing forbidden-support theorem supplies its zero branch. -/
theorem support_component_energy_le_current
    (left right : Orientation) (inverse : Bool) (a : Word) (ha0 : a ≠ 0)
    (r out : Fin 16) (hr : MaskDisjoint r out) :
    (∑ y : Word, action (supportProduct (0 : Byte) (maskBit out) (maskBit r))
      (fun v => wordKernel left right inverse v a) y^2) ≤
      supportCap (active a).card (maskSize r) (maskSize out) := by
  rw [AESConcrete.ColumnSupportResponse.column_support_energy left right inverse a r out hr]
  by_cases hz : maskSize r < (active a).card
  · have h := full_residual_energy_le left right inverse a r out hr (by omega)
      (AESConcrete.ColumnSupportResponse.nonzeroOutside inverse r)
    -- The generic adapter is classical; the pre-existing physical identity
    -- installs its explicit event decider. These data are subsingletons.
    have hdec : (fun x => Classical.propDecidable
        (AESConcrete.ColumnSupportResponse.nonzeroOutside inverse r x)) =
        AESConcrete.ColumnSupportResponse.instDecidablePredWordNonzeroOutside inverse r :=
      Subsingleton.elim _ _
    rw [hdec] at h
    calc
      _ ≤ ((1 / 64 : ℝ) ^ (2 * maskSize r) *
          ((65 / 8192 : ℝ) * (9 / 128)^2) ^
            min ((active a).card - maskSize r) (maskSize out) *
          ((65 / 8192 : ℝ) - 1 / 255) ^
            (maskSize out - min ((active a).card - maskSize r) (maskSize out))) /
              255^(4-(maskSize r+maskSize out)) :=
        div_le_div_of_nonneg_right h (by positivity)
      _ = _ := by
        simp only [supportCap, if_pos hz, AESConcrete.MultibyteColumnNumbers.atom,
          AESConcrete.MultibyteColumnNumbers.rho, AESConcrete.MultibyteColumnNumbers.nu,
          AESConcrete.MultibyteColumnNumbers.delta]
        norm_num
        ring
  · have hhigh : 4 ≤ maskSize r + maskSize (AESConcrete.AllColumnBound.inputZeroMask a) := by
      rw [active_card] at hz
      have h := maskSize_le_four (AESConcrete.AllColumnBound.inputZeroMask a)
      omega
    rw [AESConcrete.ActualPositiveColumnDegrees.forbidden_response_zero
      left right inverse a ha0 r (AESConcrete.AllColumnBound.inputZeroMask a) out
      hhigh
      (fun i => (AESConcrete.AllColumnBound.inputZeroMask_bit a i).symm)
      (AESConcrete.ColumnSupportResponse.nonzeroOutside inverse r)]
    simp only [Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
      zero_div, supportCap, if_neg hz, le_refl]

/-- Exact support multiplicities, grouped only by their number of constant
positions. This reuses the established physical support counting theorem. -/
theorem markedWeight_sum (j : Fin 5) (x y c : ℝ) :
    (∑ p : SupportIndex j.val, markedWeight x y c (maskSize p.val.2) j.val) =
      ∑ a : Fin (5-j.val), (Nat.choose 4 j.val * Nat.choose (4-j.val) a.val : ℕ) *
        markedWeight x y c (4-j.val-a.val) j.val := by
  have he (p : SupportIndex j.val) : maskSize p.val.2 = 4-j.val-(supportIndexSize p).val := by
    have h := supportIndexSize_eq p
    have hz := maskSize_le_four p.val.2
    omega
  simp_rw [he]
  exact supportIndex_sum_by_size j (fun a => markedWeight x y c (4-j.val-a.val) j.val)

/-- Marking a residual pair counts each zero-free configuration at least
once. Marking an ordered zero/residual pair counts a configuration `z*j`
times, hence at least once. The nonnegative remainder records the overcount. -/
theorem marked_configuration_sum_le (x y c : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c) :
    (∑ j : Fin 5, if 0 < j.val then
      ∑ p : SupportIndex j.val, markedWeight x y c (maskSize p.val.2) j.val else 0) ≤
      4*x + 6*x^2*(1+y)^2 + 12*c*x*(1+c+y)^2 := by
  simp_rw [markedWeight_sum]
  have he : (∑ j : Fin 5, if 0 < j.val then
      ∑ a : Fin (5-j.val), (Nat.choose 4 j.val * Nat.choose (4-j.val) a.val : ℕ) *
        markedWeight x y c (4-j.val-a.val) j.val else 0) =
      4*x + 6*x^2 + 4*x^2*y + x^2*y^2 + 12*c*x + 12*c^2*x +
        4*c^3*x + 12*c*x*y + 6*c^2*x*y + 4*c*x*y^2 := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_four]
    change 0 + ((∑ a : Fin 4, (4 * Nat.choose 3 a.val : ℕ) *
        markedWeight x y c (3-a.val) 1) +
      (∑ a : Fin 3, (6 * Nat.choose 2 a.val : ℕ) *
        markedWeight x y c (2-a.val) 2) +
      (∑ a : Fin 2, (4 * Nat.choose 1 a.val : ℕ) *
        markedWeight x y c (1-a.val) 3) +
      (∑ a : Fin 1, (1 * Nat.choose 0 a.val : ℕ) *
        markedWeight x y c (0-a.val) 4)) = _
    rw [Fin.sum_univ_four, Fin.sum_univ_three, Fin.sum_univ_two, Fin.sum_univ_one]
    norm_num [markedWeight, Nat.choose]
    ring
  rw [he]
  have hr : 0 ≤ 8*x^2*y + 5*x^2*y^2 + 12*c^2*x + 8*c^3*x +
      12*c*x*y + 18*c^2*x*y + 8*c*x*y^2 := by positivity
  nlinarith

/-- The combined positive residual degree energy in Section 11, with no
numerical comparison to the later `1/12` or full-column constants. -/
theorem positive_residual_energy_le_marked
    (left right : Orientation) (inverse : Bool) (a : Word)
    (ht : 2 ≤ (active a).card) :
    (∑ j : Fin 5, if 0 < j.val then
      ∑ y : Word, degreeComponent (0 : Byte) j
        (fun v => wordKernel left right inverse v a) y ^ 2 else 0) ≤
      (4*X + 6*X^2*(1+Y)^2 + 12*C*X*(1+C+Y)^2) / 255^4 := by
  have ha0 := nonzero_of_two_active a ht
  calc
    _ ≤ ∑ j : Fin 5, if 0 < j.val then
        ∑ p : SupportIndex j.val, markedWeight X Y C (maskSize p.val.2) j.val / 255^4
        else 0 := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs with hj
      · rw [supportIndex_degree_energy 0 (by norm_num [Byte, BinaryWord.card])]
        apply Finset.sum_le_sum
        intro p _
        have h := support_component_energy_le_current left right inverse a ha0
          p.val.2 p.val.1 p.property.1
        have hcount := disjoint_mask_size_le_four p.val.2 p.val.1 p.property.1
        have hs : (∑ y : Word, supportIndexComponent (0 : Byte) p
            (fun v => wordKernel left right inverse v a) y^2) ≤
            supportCap (active a).card (maskSize p.val.2) j.val := by
          simpa only [supportIndexComponent, p.property.2] using h
        exact hs.trans (supportCap_le_marked (active a).card (maskSize p.val.2) j.val ht
          (by omega) (by simpa only [p.property.2] using hcount))
      · exact le_rfl
    _ = (∑ j : Fin 5, if 0 < j.val then
        ∑ p : SupportIndex j.val, markedWeight X Y C (maskSize p.val.2) j.val else 0) /
          255^4 := by
      simp_rw [← Finset.sum_div]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (marked_configuration_sum_le X Y C marked_scalars.1 marked_scalars.2.1
        marked_scalars.2.2.1) (by norm_num)

end AES8.PaperAESSource
