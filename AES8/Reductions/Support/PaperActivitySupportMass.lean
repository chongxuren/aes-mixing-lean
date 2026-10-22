import AES8.Reductions.Support.PaperSupportBlockLift
import AESMixing.SupportRepresentation
import AESConcrete.WordColumnGram

/-! Exact support masses and activity energy. Restrictions keep their original
mass; no conditional probability or independence premise is introduced. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivitySupportMass
open AESMixing
set_option autoImplicit false
set_option maxRecDepth 10000
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V] {n : ℕ}

def indicator (s : Fin n → Bool) (x : Fin n → V) : ℝ :=
  ∏ i, supportConstant (s i) (x i)

def volume (s : Fin n → Bool) : ℝ :=
  ((Fintype.card V : ℝ)-1)^PaperSupportProjection.supportCount s

def mass (s : Fin n → Bool) (f : (Fin n → V) → ℝ) : ℝ :=
  ∑ x, indicator s x * f x

theorem constant_sq (b : Bool) (x : V) :
    supportConstant b x^2 = supportConstant b x := by
  cases b <;> by_cases hx : x = 0 <;> simp [supportConstant, identityKernel, hx]

theorem constant_nonneg (b : Bool) (x : V) : 0 ≤ supportConstant b x := by
  cases b <;> by_cases hx : x = 0 <;> simp [supportConstant, identityKernel, hx]

theorem indicator_nonneg (s : Fin n → Bool) (x : Fin n → V) :
    0 ≤ indicator s x := Finset.prod_nonneg (fun _ _ => constant_nonneg _ _)

theorem indicator_sq (s : Fin n → Bool) (x : Fin n → V) :
    indicator s x^2 = indicator s x := by
  simp only [indicator, ← Finset.prod_pow, constant_sq]

theorem indicator_eq_ite (s : Fin n → Bool) (x : Fin n → V) :
    indicator s x = if ∀ i, x i = 0 ↔ s i = true then 1 else 0 := by
  classical
  by_cases h : ∀ i, x i = 0 ↔ s i = true
  · rw [if_pos h]
    unfold indicator
    apply Finset.prod_eq_one
    intro i _
    cases hs : s i with
    | false =>
      have hx : x i ≠ 0 := by simpa [hs] using h i
      simp [supportConstant, hs, identityKernel, hx]
    | true =>
      have hx : x i = 0 := (h i).mpr hs
      simp [supportConstant, hs, identityKernel, hx]
  · rw [if_neg h]
    push Not at h
    obtain ⟨i, hi⟩ := h
    unfold indicator
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hs : s i <;> by_cases hx : x i = 0 <;>
      simp_all [supportConstant, identityKernel]

theorem indicator_zero (s : Fin n → Bool)
    (hs : 0 < PaperSupportProjection.supportCount s) :
    indicator s (0 : Fin n → V) = 0 := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hs
  have hi' : s i = false := (Finset.mem_filter.mp hi).2
  unfold indicator
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [supportConstant, hi', identityKernel]

theorem constant_sum (b : Bool) : (∑ x : V, supportConstant b x) =
    if b then 1 else (Fintype.card V : ℝ)-1 := by
  simpa only [constant_sq] using (supportConstant_energy (V := V) b)

theorem volume_product (s : Fin n → Bool) :
    (∏ i, if s i then (1 : ℝ) else (Fintype.card V : ℝ)-1) = volume (V := V) s := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  unfold volume PaperSupportProjection.supportCount
  congr 2
  ext i
  cases s i <;> simp

theorem indicator_sum (s : Fin n → Bool) :
    (∑ x : Fin n → V, indicator s x) = volume (V := V) s := by
  unfold indicator
  rw [← Fintype.prod_sum (fun i x => supportConstant (s i) x)]
  simp_rw [constant_sum]
  exact volume_product s

theorem volume_pos (hq : 1 < Fintype.card V) (s : Fin n → Bool) :
    0 < volume (V := V) s := by
  have h : (1 : ℝ) < Fintype.card V := by exact_mod_cast hq
  exact pow_pos (sub_pos.mpr h) _

theorem mass_sub (s : Fin n → Bool) (f g : (Fin n → V) → ℝ) :
    mass s (f-g) = mass s f - mass s g := by
  simp only [mass, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem mass_nonneg (s : Fin n → Bool) (f : (Fin n → V) → ℝ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ mass s f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (indicator_nonneg s x) (hf x))

theorem uniform_mass (s : Fin n → Bool)
    (hs : 0 < PaperSupportProjection.supportCount s) :
    mass s (uniformExcept (0 : Fin n → V)) =
      volume (V := V) s / ((Fintype.card V : ℝ)^n-1) := by
  have hz := indicator_zero (V := V) s hs
  have h (x : Fin n → V) :
      indicator s x * uniformExcept (0 : Fin n → V) x =
        indicator s x / ((Fintype.card V : ℝ)^n-1) := by
    by_cases hx : x = 0
    · simp [hx, hz, uniformExcept]
    · simp [uniformExcept, hx, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
        div_eq_mul_inv]
  unfold mass
  simp_rw [h]
  rw [← Finset.sum_div, indicator_sum]

theorem activity_kernel (s : Fin n → Bool) (y x : Fin n → V) :
    supportProduct (0 : V) (fun _ => false) s y x =
      indicator s y * indicator s x / volume (V := V) s := by
  unfold supportProduct
  simp_rw [supportPiece_unmarked, supportDualConstant]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, volume_product]
  change indicator s y * (indicator s x / volume (V := V) s) = _
  ring

theorem activity_action (s : Fin n → Bool) (f : (Fin n → V) → ℝ)
    (y : Fin n → V) :
    action (supportProduct (0 : V) (fun _ => false) s) f y =
      indicator s y * mass s f / volume (V := V) s := by
  unfold action
  simp_rw [activity_kernel]
  unfold mass
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem activity_energy (hq : 1 < Fintype.card V) (s : Fin n → Bool)
    (f : (Fin n → V) → ℝ) :
    (∑ y, action (supportProduct (0 : V) (fun _ => false) s) f y^2) =
      mass s f^2 / volume (V := V) s := by
  simp_rw [activity_action, div_pow, mul_pow, indicator_sq]
  rw [← Finset.sum_div, ← Finset.sum_mul, indicator_sum]
  have hv := ne_of_gt (volume_pos (V := V) hq s)
  field_simp

theorem activity_difference_energy_le (hq : 1 < Fintype.card V)
    (s : Fin n → Bool) (f g : (Fin n → V) → ℝ) (B : ℝ)
    (hf0 : 0 ≤ mass s f) (hg0 : 0 ≤ mass s g)
    (hf : mass s f ≤ B) (hg : mass s g ≤ B) :
    (∑ y, action (supportProduct (0 : V) (fun _ => false) s) (f-g) y^2) ≤
      B^2 / volume (V := V) s := by
  rw [activity_energy hq, mass_sub]
  apply div_le_div_of_nonneg_right _ (le_of_lt (volume_pos hq s))
  have hab : |mass s f - mass s g| ≤ B := abs_le.mpr ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := hf0.trans hf
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2

/-- Exact support probabilities survive every pointed stochastic word layer. -/
theorem constant_channel (S : V → V → ℝ) (hS : PointedBistochastic S 0)
    (b : Bool) (x : V) :
    (∑ y, supportConstant b y * S y x) = supportConstant b x := by
  cases b <;> simp [supportConstant, identityKernel, sub_mul,
    Finset.sum_sub_distrib, hS.column_sum, hS.zero_row]

theorem mass_tensor_response {X : Type*} [Fintype X]
    (S : V → V → ℝ) (hS : PointedBistochastic S 0) (s : Fin n → Bool)
    (coord : X → Fin n → V) (f : X → ℝ) :
    mass s (AESConcrete.WordColumnGram.tensorResponse (fun _ => S) coord f) =
      ∑ x, indicator s (coord x) * f x := by
  unfold mass AESConcrete.WordColumnGram.tensorResponse
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  unfold indicator AESConcrete.WordColumnGram.tensorColumn
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i y => supportConstant (s i) y * S y (coord x i))]
  simp_rw [constant_channel S hS]

theorem zero_degree_mask {t : ℕ} (p : PaperSupportBlockLift.BlockLabel n 0 t) :
    p.val.1 = (fun _ => false) := by
  funext i
  have hc := p.property.2.1
  unfold PaperSupportProjection.residualCount at hc
  have he := Finset.card_eq_zero.mp hc
  cases hi : p.val.1 i with
  | false => rfl
  | true =>
    have hm : i ∈ Finset.univ.filter (fun k => p.val.1 k = true) := by simp [hi]
    rw [he] at hm
    simpa using hm

/-- Orthogonality adds one squared mass difference per exact support. -/
theorem activity_component_energy_le (hq : 1 < Fintype.card V)
    (f g : (Fin 4 → V) → ℝ) (t : Fin 5) (B : ℝ)
    (hB : ∀ s : Fin 4 → Bool, PaperSupportProjection.supportCount s = t.val →
      (mass s f - mass s g)^2 ≤ B^2) :
    (∑ y, PaperSupportProjection.component (0 : V) (f-g) 0 t.val y^2) ≤
      (Nat.choose 4 t.val : ℝ) * B^2 / ((Fintype.card V : ℝ)-1)^t.val := by
  rw [PaperSupportBlockLift.component_labels]
  rw [orthogonal_family_energy _ (fun p q hpq =>
    PaperSupportProjection.raw_orthogonal (0 : V) hq p.val q.val
      (fun he => hpq (Subtype.ext he)) _ _)]
  calc
    _ ≤ ∑ _p : PaperSupportBlockLift.BlockLabel 4 0 t.val,
        B^2 / ((Fintype.card V : ℝ)-1)^t.val := by
      apply Finset.sum_le_sum
      intro p _
      have hz := zero_degree_mask p
      unfold PaperSupportProjection.raw
      rw [hz, activity_energy hq, mass_sub]
      unfold volume
      rw [p.property.2.2]
      apply div_le_div_of_nonneg_right (hB p.val.2 p.property.2.2)
      have hq' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hq
      exact pow_nonneg (sub_nonneg.mpr hq'.le) _
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [show Fintype.card (PaperSupportBlockLift.BlockLabel 4 0 t.val) =
        Nat.choose 4 t.val by
        have hc := PaperSupportBlockLift.four_word_count (0 : Fin 5) t
        simp only [Fin.val_zero, Nat.choose_zero_right, Nat.mul_one] at hc
        convert hc using 1
        exact Fintype.card_congr (Equiv.refl _)]
      ring

end AES8.PaperActivitySupportMass
