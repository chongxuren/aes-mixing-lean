import AES8.Math.Imports
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Mul

/-!
# The frozen paper's exceptional convex envelope

Paper f902bb94, `localres:exceptional-moments`, uses endpoints 33^2 and 16^2.
This new leaf proves that route without changing the earlier, weaker moment
proof. The reusable finite convex cap is separate from its exceptional-block
instantiation. Actual AES entry, energy, zero-sum and cardinality hypotheses
are supplied by separate resource modules. Constructive only; no attacks.
-/

noncomputable section
open scoped BigOperators
open Set
namespace AES8.ExceptionalConvexEnvelope
set_option autoImplicit false
set_option maxHeartbeats 4000000

section ConvexCap
variable {I : Type*} {f : ℝ → ℝ} {A : ℝ}

private theorem chord (hf : ConvexOn ℝ (Icc 0 A) f) (hf0 : f 0 = 0)
    {x t : ℝ} (hx : 0 ≤ x) (hxt : x ≤ t) (htA : t ≤ A) (ht : 0 < t) :
    f x ≤ x / t * f t := by
  have ha : 0 ≤ 1 - x / t := by
    have h := (div_le_one ht).mpr hxt
    linarith
  have hb : 0 ≤ x / t := div_nonneg hx ht.le
  have h := hf.2 ⟨le_rfl, ht.le.trans htA⟩ ⟨ht.le, htA⟩ ha hb (by ring)
  have hp : (1 - x / t) * 0 + x / t * t = x := by
    field_simp
    ring
  simp only [smul_eq_mul] at h
  rw [hp, hf0] at h
  simpa only [mul_zero, zero_add] using h

private theorem convex_add (hf : ConvexOn ℝ (Icc 0 A) f) (hf0 : f 0 = 0)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x + y ≤ A) :
    f x + f y ≤ f (x + y) := by
  by_cases hz : x + y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0, hf0]
  · have hp : 0 < x + y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hz)
    have h1 := chord hf hf0 hx (by linarith : x ≤ x + y) hxy hp
    have h2 := chord hf hf0 hy (by linarith : y ≤ x + y) hxy hp
    have hs : x / (x + y) + y / (x + y) = 1 := by field_simp
    calc
      f x + f y ≤ x / (x + y) * f (x + y) + y / (x + y) * f (x + y) :=
        add_le_add h1 h2
      _ = f (x + y) := by rw [← add_mul, hs, one_mul]

private theorem sum_map_le (s : Finset I) (t : I → ℝ)
    (hf : ConvexOn ℝ (Icc 0 A) f) (hf0 : f 0 = 0)
    (hnonneg : ∀ i ∈ s, 0 ≤ t i) (hsum : (∑ i ∈ s, t i) ≤ A) :
    (∑ i ∈ s, f (t i)) ≤ f (∑ i ∈ s, t i) := by
  classical
  revert hnonneg hsum
  induction s using Finset.induction_on with
  | empty => intro _ _; simp [hf0]
  | @insert i s hi ih =>
      intro hn hs
      have hi0 := hn i (Finset.mem_insert_self _ _)
      have hr0 : ∀ j ∈ s, 0 ≤ t j := fun j hj => hn j (Finset.mem_insert_of_mem hj)
      have hrest0 : 0 ≤ ∑ j ∈ s, t j := Finset.sum_nonneg hr0
      rw [Finset.sum_insert hi] at hs
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (add_le_add (le_refl _) (ih hr0 (by linarith))).trans
        (convex_add hf hf0 (x := t i) (y := ∑ j ∈ s, t j) hi0 hrest0 hs)

private theorem pair_endpoints (hf : ConvexOn ℝ (Icc 0 A) f)
    {B x : ℝ} (hB0 : 0 ≤ B) (hBx : B ≤ x) (hxA : x ≤ A) :
    f x + f (A + B - x) ≤ f A + f B := by
  by_cases hAB : A = B
  · have hx : x = B := by linarith
    simp [hAB, hx]
  · have hBA : B < A := lt_of_le_of_ne (hBx.trans hxA) (Ne.symm hAB)
    let a := (A - x) / (A - B)
    let b := (x - B) / (A - B)
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hxA) (by linarith)
    have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hBx) (by linarith)
    have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
    have hp : a * B + b * A = x := by dsimp [a, b]; field_simp; ring
    have hq : b * B + a * A = A + B - x := by dsimp [a, b]; field_simp; ring
    have h1 := hf.2 ⟨hB0, hBx.trans hxA⟩ ⟨hB0.trans (hBx.trans hxA), le_rfl⟩ ha hb hab
    have h2 := hf.2 ⟨hB0, hBx.trans hxA⟩ ⟨hB0.trans (hBx.trans hxA), le_rfl⟩ hb ha (by linarith)
    simp only [smul_eq_mul, hp] at h1
    simp only [smul_eq_mul, hq] at h2
    calc
      _ ≤ (a * f B + b * f A) + (b * f B + a * f A) := add_le_add h1 h2
      _ = (a + b) * (f A + f B) := by ring
      _ = _ := by rw [hab, one_mul]

/-- Increasing convex functions attain this cap at one full coordinate and
one remainder. The proof separates a chord regime from a two-point transfer;
no maximizer existence or bound on the number of coordinates is needed. -/
theorem finite_convex_cap (s : Finset I) (t : I → ℝ) (B : ℝ)
    (hf : ConvexOn ℝ (Icc 0 A) f) (hmono : MonotoneOn f (Icc 0 A))
    (hf0 : f 0 = 0) (hB0 : 0 ≤ B) (hBA : B ≤ A)
    (hnonneg : ∀ i ∈ s, 0 ≤ t i) (hcap : ∀ i ∈ s, t i ≤ A)
    (hsum : (∑ i ∈ s, t i) ≤ A + B) :
    (∑ i ∈ s, f (t i)) ≤ f A + f B := by
  classical
  have hA0 := hB0.trans hBA
  have hfA : 0 ≤ f A := by simpa [hf0] using hmono ⟨le_rfl, hA0⟩ ⟨hA0, le_rfl⟩ hA0
  have hfB : 0 ≤ f B := by simpa [hf0] using hmono ⟨le_rfl, hA0⟩ ⟨hB0, hBA⟩ hB0
  by_cases hsmall : ∀ i ∈ s, t i ≤ B
  · by_cases hB : B = 0
    · have ht0 : ∀ i ∈ s, t i = 0 := fun i hi => le_antisymm (by simpa [hB] using hsmall i hi) (hnonneg i hi)
      have hs0 : (∑ i ∈ s, f (t i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [ht0 i hi, hf0]
      simpa [hs0, hB, hf0] using hfA
    · have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hB)
      have hAp : 0 < A := hBp.trans_le hBA
      have hch := chord hf hf0 hB0 hBA le_rfl hAp
      have hslope : A * f B ≤ B * f A := by
        calc
          A * f B ≤ A * (B / A * f A) := mul_le_mul_of_nonneg_left hch hA0
          _ = B * f A := by field_simp
      have hscale : A * (f B / B) ≤ f A := by
        rw [← mul_div_assoc]
        exact (div_le_iff₀ hBp).mpr (by nlinarith [hslope])
      calc
        (∑ i ∈ s, f (t i)) ≤ ∑ i ∈ s, f B / B * t i := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            _ ≤ t i / B * f B := chord hf hf0 (hnonneg i hi) (hsmall i hi) hBA hBp
            _ = _ := by ring
        _ = f B / B * ∑ i ∈ s, t i := (Finset.mul_sum _ _ _).symm
        _ ≤ f B / B * (A + B) := mul_le_mul_of_nonneg_left hsum (div_nonneg hfB hB0)
        _ = A * (f B / B) + f B := by field_simp
        _ ≤ f A + f B := add_le_add hscale (le_refl _)
  · obtain ⟨j, hj, hjB⟩ : ∃ j, j ∈ s ∧ B < t j := by
      push Not at hsmall
      exact hsmall
    have hr0 : ∀ i ∈ s.erase j, 0 ≤ t i := fun i hi => hnonneg i (Finset.mem_of_mem_erase hi)
    have hw0 : 0 ≤ ∑ i ∈ s.erase j, t i := Finset.sum_nonneg hr0
    have hsplit : (∑ i ∈ s.erase j, t i) + t j = ∑ i ∈ s, t i := Finset.sum_erase_add _ _ hj
    have hw : (∑ i ∈ s.erase j, t i) ≤ A + B - t j := by linarith
    have hrem0 : 0 ≤ A + B - t j := hw0.trans hw
    have hremA : A + B - t j ≤ A := by linarith
    calc
      (∑ i ∈ s, f (t i)) = f (t j) + ∑ i ∈ s.erase j, f (t i) := by
        rw [← Finset.sum_erase_add _ _ hj]
        ring
      _ ≤ f (t j) + f (∑ i ∈ s.erase j, t i) :=
        add_le_add (le_refl _) (sum_map_le _ t hf hf0 hr0 (hw.trans hremA))
      _ ≤ f (t j) + f (A + B - t j) :=
        add_le_add (le_refl _) (hmono ⟨hw0, hw.trans hremA⟩ ⟨hrem0, hremA⟩ hw)
      _ ≤ f A + f B := pair_endpoints hf hB0 hjB.le (hcap j hj)

end ConvexCap

/-- The single increasing convex envelope printed in the paper. -/
def envelope (c t : ℝ) : ℝ := t ^ 2 + 4 * c * Real.rpow t (3 / 2) + 6 * c ^ 2 * t

theorem envelope_zero (c : ℝ) : envelope c 0 = 0 := by
  norm_num [envelope, Real.zero_rpow]

theorem envelope_convex (c : ℝ) (hc : 0 ≤ c) : ConvexOn ℝ (Ici 0) (envelope c) := by
  have h2 : ConvexOn ℝ (Ici 0) (fun t : ℝ => t ^ 2) := convexOn_pow 2
  have h3 : ConvexOn ℝ (Ici 0) (fun t : ℝ => 4 * c * Real.rpow t (3 / 2)) := by
    exact ConvexOn.smul (by positivity : 0 ≤ 4 * c) (convexOn_rpow (by norm_num : (1 : ℝ) ≤ 3 / 2))
  have h1 : ConvexOn ℝ (Ici 0) (fun t : ℝ => 6 * c ^ 2 * t) :=
    ConvexOn.smul (by positivity : 0 ≤ 6 * c ^ 2) (convexOn_id (convex_Ici (0 : ℝ)))
  exact h2.add h3 |>.add h1

theorem envelope_monotone (c : ℝ) (hc : 0 ≤ c) : MonotoneOn (envelope c) (Ici 0) := by
  intro x hx y hy hxy
  unfold envelope
  have h2 : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx hy).mpr hxy
  have h3 := Real.rpow_le_rpow hx hxy (by norm_num : (0 : ℝ) ≤ 3 / 2)
  exact add_le_add (add_le_add h2 (mul_le_mul_of_nonneg_left h3 (by positivity)))
    (mul_le_mul_of_nonneg_left hxy (by positivity))

theorem square_three_halves (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow (x ^ 2) (3 / 2) = x ^ 3 := by
  calc
    _ = Real.rpow (Real.rpow x 2) (3 / 2) := by
      exact congrArg (fun z : ℝ => Real.rpow z (3 / 2))
        (Real.rpow_natCast x 2).symm
    _ = Real.rpow x (2 * (3 / 2)) := (Real.rpow_mul hx _ _).symm
    _ = x ^ 3 := by norm_num [Real.rpow_eq_pow]

section Exceptional
variable {I : Type*} [Fintype I]

/-- The exact two-endpoint envelope estimate used by the frozen manuscript. -/
theorem sum_envelope_le (u : I → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hentry : ∀ i, |u i| ≤ 33) (henergy : (∑ i : I, u i ^ 2) ≤ 1344) :
    (∑ i : I, envelope c (u i ^ 2)) ≤ envelope c (33 ^ 2) + envelope c (16 ^ 2) := by
  have hf := (envelope_convex c hc).subset (fun _ h => h.1) (convex_Icc 0 ((33 : ℝ) ^ 2))
  have hm : MonotoneOn (envelope c) (Icc 0 ((33 : ℝ) ^ 2)) :=
    fun _ hx _ hy hxy => envelope_monotone c hc hx.1 hy.1 hxy
  apply finite_convex_cap Finset.univ (fun i => u i ^ 2) ((16 : ℝ) ^ 2) hf hm
    (envelope_zero c) (by norm_num) (by norm_num) (fun i _ => sq_nonneg (u i))
  · intro i _
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (u i)) (by norm_num : (0 : ℝ) ≤ 33)).mpr (hentry i)
  · linarith

/-- This is the paper's cubic endpoint expression, 33^3+16^3=40033.
It is a consequence of the same convex cap, not the stale constant 40017. -/
theorem cubic_sum_le_40033 (u : I → ℝ)
    (hentry : ∀ i, |u i| ≤ 33) (henergy : (∑ i : I, u i ^ 2) ≤ 1344) :
    (∑ i : I, |u i| ^ 3) ≤ 40033 := by
  have hf := (convexOn_rpow (by norm_num : (1 : ℝ) ≤ 3 / 2)).subset
    (fun _ h => h.1) (convex_Icc 0 ((33 : ℝ) ^ 2))
  have hm : MonotoneOn (fun t : ℝ => Real.rpow t (3 / 2)) (Icc 0 ((33 : ℝ) ^ 2)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow hx.1 hxy (by norm_num)
  have h := finite_convex_cap Finset.univ (fun i => u i ^ 2) ((16 : ℝ) ^ 2)
    hf hm (by norm_num) (by norm_num) (by norm_num)
    (fun i _ => sq_nonneg (u i))
    (fun i _ => by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (u i)) (by norm_num : (0 : ℝ) ≤ 33)).mpr (hentry i))
    (by linarith)
  have hp (i : I) : Real.rpow (u i ^ 2) (3 / 2) = |u i| ^ 3 := by
    rw [← sq_abs]
    exact square_three_halves _ (abs_nonneg _)
  change (∑ i : I, Real.rpow (u i ^ 2) (3 / 2)) ≤
    Real.rpow ((33 : ℝ) ^ 2) (3 / 2) + Real.rpow ((16 : ℝ) ^ 2) (3 / 2) at h
  simp only [hp, square_three_halves 33 (by norm_num), square_three_halves 16 (by norm_num)] at h
  norm_num at h
  exact h

theorem translated_sum_le_envelope (u : I → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hzero : (∑ i : I, u i) = 0) :
    (∑ i : I, (u i - c) ^ 4) ≤ (∑ i : I, envelope c (u i ^ 2)) +
      (Fintype.card I : ℝ) * c ^ 4 := by
  have hpoint (i : I) : (u i - c) ^ 4 ≤ envelope c (u i ^ 2) - 4 * c ^ 3 * u i + c ^ 4 := by
    have hp : Real.rpow (u i ^ 2) (3 / 2) = |u i| ^ 3 := by
      rw [← sq_abs]
      exact square_three_halves _ (abs_nonneg _)
    have hab : -(u i ^ 3) ≤ |u i| ^ 3 := by
      have hn := neg_le_abs (u i ^ (3 : ℕ))
      rw [abs_pow] at hn
      exact hn
    have hh := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 4 * c)
    rw [envelope, hp]
    nlinarith only [hh]
  calc
    _ ≤ ∑ i : I, (envelope c (u i ^ 2) - 4 * c ^ 3 * u i + c ^ 4) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hzero, mul_zero, sub_zero]

/-- The stronger printed 1623000 allowance, from the single convex envelope.
Nonstrict input caps suffice; rounding gives the strict conclusion. -/
theorem translated_fourth_sum_lt_1623000 (u : I → ℝ) (c : ℝ)
    (hcard : Fintype.card I = 255) (hentry : ∀ i, |u i| ≤ 33)
    (henergy : (∑ i : I, u i ^ 2) ≤ 1344) (hzero : (∑ i : I, u i) = 0)
    (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ i : I, (u i - c) ^ 4) < 1623000 := by
  have hb := (translated_sum_le_envelope u c hc0 hzero).trans
    (add_le_add (sum_envelope_le u c hc0 hentry henergy) (le_refl _))
  rw [hcard] at hb
  simp only [envelope, square_three_halves 33 (by norm_num), square_three_halves 16 (by norm_num)] at hb
  have hc2 : c ^ 2 ≤ (33 / 16 : ℝ) ^ 2 :=
    (sq_le_sq₀ hc0 (by norm_num)).mpr hc
  have hc4 : c ^ 4 ≤ (33 / 16 : ℝ) ^ 4 := by
    have h := (sq_le_sq₀ (sq_nonneg c) (sq_nonneg (33 / 16 : ℝ))).mpr hc2
    nlinarith only [h]
  have h4 : (33 : ℝ) ^ 4 + 16 ^ 4 < 1252000 := by norm_num
  have h3 : 4 * c * ((33 : ℝ) ^ 3 + 16 ^ 3) < 331000 := by nlinarith only [hc]
  have h2 : 6 * c ^ 2 * ((33 : ℝ) ^ 2 + 16 ^ 2) < 35000 := by nlinarith only [hc2]
  have h0 : 255 * c ^ 4 < (5000 : ℝ) := by nlinarith only [hc4]
  norm_num at hb
  nlinarith only [hb, h4, h3, h2, h0]

/-- The paper's scaled block endpoint, now obtained through its printed
convex envelope and the stronger 1623000 intermediate. -/
theorem scaled_fourth_sum_lt (u : I → ℝ) (c : ℝ)
    (hcard : Fintype.card I = 255) (hentry : ∀ i, |u i| ≤ 33)
    (henergy : (∑ i : I, u i ^ 2) ≤ 1344) (hzero : (∑ i : I, u i) = 0)
    (hc0 : 0 ≤ c) (hc : c ≤ 33 / 16) :
    (∑ i : I, ((128 : ℝ) * (u i - c)) ^ 4) < 25 * 2 ^ 44 := by
  have h := translated_fourth_sum_lt_1623000 u c hcard hentry henergy hzero hc0 hc
  calc
    _ = (128 : ℝ) ^ 4 * ∑ i : I, (u i - c) ^ 4 := by
      simp only [mul_pow, Finset.mul_sum]
    _ < (128 : ℝ) ^ 4 * 1623000 := mul_lt_mul_of_pos_left h (by norm_num)
    _ < 25 * 2 ^ 44 := by norm_num

end Exceptional
end AES8.ExceptionalConvexEnvelope
