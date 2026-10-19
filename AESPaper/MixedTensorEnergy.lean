import AESPaper.BiasTensorEnergy
import AESConcrete.RestrictedMarginalEnergy
import AESMixing.CoordinateTensor
import AESMixing.MDSProjection

/-!
# Exact mixed J/Z/R action and counting-measure energy

The residual mask and bias set are disjoint. The input is an arbitrary signed
joint vector, and the weighted marginal is taken before the residual acts.
The coordinate split is a finite tuple equivalence; it does not assert
independence of the input. No actual-source or residual contraction bound is
assumed here. Fixed target: 14.3+73.1k. Constructive correctness only; no
attacks, manuscript edits, or changes to checked predecessor sources.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.MixedTensorEnergy
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.RestrictedMarginalEnergy (marginal)
open AESPaper.BiasTensorEnergy (basis basisProduct)

variable {V : Type*} [Fintype V] [DecidableEq V]
local notation "Q" => (Fintype.card V : ℝ)

/-- Bias coordinates must lie outside the residual mask. -/
def Disjoint (out : Fin 16) (S : Finset (Fin 4)) : Prop :=
  ∀ i ∈ S, maskBit out i = false

/-- The scalar left by summing the J/Z output coordinates. -/
def denominator (out : Fin 16) (S : Finset (Fin 4)) : ℝ :=
  Q ^ (4-maskSize out) * (Q-1) ^ S.card

/-- Literal tensor kernel: R on the mask, Z on S, J elsewhere. -/
def kernel (z : V) (out : Fin 16) (S : Finset (Fin 4))
    (R : V → V → ℝ) (y x : Fin 4 → V) : ℝ :=
  ∏ i : Fin 4, if maskBit out i = true then R (y i) (x i)
    else if i ∈ S then UniformBias.biasKernel z (y i) (x i)
    else UniformBias.uniformKernel (y i) (x i)

/-- The full joint signed weight is retained in this unnormalized marginal. -/
def weightedMarginal (z : V) (out : Fin 16) (S : Finset (Fin 4))
    (g : (Fin 4 → V) → ℝ) : (MaskCoordinates out → V) → ℝ :=
  marginal (fun x (i : MaskCoordinates out) => x i.val)
    (fun x => g x * basisProduct z S x)

theorem prod_ite_subtype {I : Type*} [Fintype I]
    (p : I → Prop) [DecidablePred p] (f : I → ℝ) :
    (∏ i : I, if p i then f i else 1) = ∏ i : {i // p i}, f i.val := by
  classical
  calc
    _ = (∏ i : {i // p i}, if p i.val then f i.val else 1) *
        (∏ i : {i // ¬p i}, if p i.val then f i.val else 1) :=
      (Fintype.prod_subtype_mul_prod_subtype p
        (fun i => if p i then f i else 1)).symm
    _ = (∏ i : {i // p i}, f i.val) * 1 := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        exact if_pos i.property
      · simp only [show (fun i : {i // ¬p i} =>
            if p i.val then f i.val else 1) = fun _ => 1 from by
              funext i; exact if_neg i.property, Finset.prod_const_one]
    _ = _ := mul_one _

theorem residual_constant_product (out : Fin 16) (a : ℝ) :
    (∏ i : Fin 4, if maskBit out i = true then 1 else a) =
      a ^ (4-maskSize out) := by
  have hc := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : Fin 4 => maskBit out i = true)
  have hc' : (Finset.univ.filter
      (fun i : Fin 4 => ¬maskBit out i = true)).card = 4-maskSize out := by
    change maskSize out + (Finset.univ.filter
      (fun i : Fin 4 => ¬maskBit out i = true)).card = 4 at hc
    omega
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, one_mul, hc']

theorem denominator_product (out : Fin 16) (S : Finset (Fin 4)) :
    (∏ i : Fin 4, (if maskBit out i = true then 1 else Q) *
      (if i ∈ S then Q-1 else 1)) = denominator (V := V) out S := by
  rw [Finset.prod_mul_distrib, residual_constant_product]
  have h := BiasTensorEnergy.constant_product S 1 (Q-1)
  simp only [one_mul, one_pow] at h
  rw [h]
  rfl

/-- Exact splitting of all four coordinates into the residual and its
complement, without choosing values for either group. -/
def tupleSplit (out : Fin 16) :
    (Fin 4 → V) ≃ (MaskCoordinates out → V) ×
      ({i : Fin 4 // ¬maskBit out i = true} → V) :=
  Equiv.piEquivPiSubtypeProd (fun i : Fin 4 => maskBit out i = true) (fun _ => V)

theorem tupleSplit_restrict (out : Fin 16)
    (p : (MaskCoordinates out → V) ×
      ({i : Fin 4 // ¬maskBit out i = true} → V)) :
    (fun i : MaskCoordinates out => (tupleSplit (V := V) out).symm p i.val) = p.1 := by
  funext i
  simp [tupleSplit, Equiv.piEquivPiSubtypeProd, i.property]

/-- A product weight equal to one on the residual coordinates sums exactly
over the complementary coordinates. The remaining function is arbitrary. -/
theorem weighted_sum_split (out : Fin 16) (w : Fin 4 → V → ℝ)
    (hw : ∀ i, maskBit out i = true → ∀ v, w i v = 1)
    (F : (MaskCoordinates out → V) → ℝ) :
    (∑ y : Fin 4 → V, (∏ i : Fin 4, w i (y i)) *
      F (fun i : MaskCoordinates out => y i.val)) =
      (∏ i : {i : Fin 4 // ¬maskBit out i = true}, ∑ v : V, w i.val v) *
        ∑ v : MaskCoordinates out → V, F v := by
  let e := tupleSplit (V := V) out
  have hp (p : (MaskCoordinates out → V) ×
      ({i : Fin 4 // ¬maskBit out i = true} → V)) :
      (∏ i : Fin 4, w i (e.symm p i)) =
        ∏ i : {i : Fin 4 // ¬maskBit out i = true}, w i.val (p.2 i) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype
      (fun i : Fin 4 => maskBit out i = true)]
    have hm : (∏ i : MaskCoordinates out, w i.val (e.symm p i.val)) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      exact hw i.val i.property _
    rw [hm, one_mul]
    apply Finset.prod_congr rfl
    intro i _
    simp [e, tupleSplit, Equiv.piEquivPiSubtypeProd, i.property]
  calc
    _ = ∑ p : (MaskCoordinates out → V) ×
        ({i : Fin 4 // ¬maskBit out i = true} → V),
        (∏ i : {i : Fin 4 // ¬maskBit out i = true}, w i.val (p.2 i)) * F p.1 := by
      rw [← e.symm.sum_comp]
      apply Finset.sum_congr rfl
      intro p _
      rw [hp, tupleSplit_restrict]
    _ = ∑ u : MaskCoordinates out → V,
        ∑ v : {i : Fin 4 // ¬maskBit out i = true} → V,
          (∏ i : {i : Fin 4 // ¬maskBit out i = true}, w i.val (v i)) * F u := by
      rw [Fintype.sum_prod_type]
    _ = ∑ u : MaskCoordinates out → V,
        (∑ v : {i : Fin 4 // ¬maskBit out i = true} → V,
          ∏ i : {i : Fin 4 // ¬maskBit out i = true}, w i.val (v i)) * F u := by
      apply Finset.sum_congr rfl
      intro u _
      exact (Finset.sum_mul _ _ _).symm
    _ = _ := by
      rw [← Fintype.prod_sum (fun (i : {i : Fin 4 // ¬maskBit out i = true})
        (v : V) => w i.val v)]
      exact (Finset.mul_sum _ _ _).symm

theorem kernel_eq (z : V) (hn : 1 < Fintype.card V) (out : Fin 16)
    (S : Finset (Fin 4)) (hd : Disjoint out S) (R : V → V → ℝ)
    (y x : Fin 4 → V) :
    kernel z out S R y x =
      basisProduct z S y * basisProduct z S x *
        coordinateKernel (fun _ : MaskCoordinates out => R)
          (fun i => y i.val) (fun i => x i.val) / denominator (V := V) out S := by
  have hp (i : Fin 4) :
      (if maskBit out i = true then R (y i) (x i)
        else if i ∈ S then UniformBias.biasKernel z (y i) (x i)
        else UniformBias.uniformKernel (y i) (x i)) =
      ((if maskBit out i = true then R (y i) (x i) else 1) *
        (if i ∈ S then basis z (y i) else 1) *
        (if i ∈ S then basis z (x i) else 1)) /
        ((if maskBit out i = true then 1 else Q) *
          (if i ∈ S then Q-1 else 1)) := by
    by_cases hi : maskBit out i = true
    · have hs : i ∉ S := by
        intro hs
        have hf := hd i hs
        simp [hf] at hi
      simp [hi, hs]
    · by_cases hs : i ∈ S
      · simpa only [if_neg hi, if_pos hs, one_mul] using
          BiasTensorEnergy.biasKernel_eq z hn (y i) (x i)
      · simp [hi, hs, UniformBias.uniformKernel]
  unfold kernel
  simp_rw [hp]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    denominator_product, prod_ite_subtype]
  change (_ * basisProduct z S y * basisProduct z S x) /
      denominator (V := V) out S = _
  unfold coordinateKernel
  ring

theorem residual_action_marginal (out : Fin 16) (R : V → V → ℝ)
    (f : (Fin 4 → V) → ℝ) (y : MaskCoordinates out → V) :
    action (coordinateKernel (fun _ : MaskCoordinates out => R))
      (marginal (fun x (i : MaskCoordinates out) => x i.val) f) y =
      ∑ x : Fin 4 → V, (∏ i : MaskCoordinates out, R (y i) (x i.val)) * f x := by
  simp only [action, marginal, coordinateKernel]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Exact mixed action, with the signed weighted joint marginal formed first. -/
theorem action_eq (z : V) (hn : 1 < Fintype.card V) (out : Fin 16)
    (S : Finset (Fin 4)) (hd : Disjoint out S) (R : V → V → ℝ)
    (g : (Fin 4 → V) → ℝ) (y : Fin 4 → V) :
    action (kernel z out S R) g y =
      (basisProduct z S y / denominator (V := V) out S) *
        action (coordinateKernel (fun _ : MaskCoordinates out => R))
          (weightedMarginal z out S g) (fun i => y i.val) := by
  have hp (x : Fin 4 → V) : kernel z out S R y x * g x =
      (basisProduct z S y / denominator (V := V) out S) *
        ((∏ i : MaskCoordinates out, R (y i.val) (x i.val)) *
          (g x * basisProduct z S x)) := by
    rw [kernel_eq z hn out S hd R]
    unfold coordinateKernel
    ring
  change (∑ x : Fin 4 → V, kernel z out S R y x * g x) = _
  simp_rw [hp]
  rw [← Finset.mul_sum]
  congr 1
  exact (residual_action_marginal out R
    (fun x => g x * basisProduct z S x) (fun i => y i.val)).symm

/-- The exact squared basis mass on each residual fiber. The arbitrary
function F is evaluated only on the residual coordinates. -/
theorem basis_square_weighted_sum (z : V) (out : Fin 16)
    (S : Finset (Fin 4)) (hd : Disjoint out S)
    (F : (MaskCoordinates out → V) → ℝ) :
    (∑ y : Fin 4 → V, basisProduct z S y ^ 2 *
      F (fun i : MaskCoordinates out => y i.val)) =
      denominator (V := V) out S * ∑ v : MaskCoordinates out → V, F v := by
  let w : Fin 4 → V → ℝ := fun i v => if i ∈ S then basis z v ^ 2 else 1
  have hw : ∀ i, maskBit out i = true → ∀ v, w i v = 1 := by
    intro i hi v
    have hs : i ∉ S := by
      intro hs
      have hf := hd i hs
      simp [hf] at hi
    simp [w, hs]
  have hb (y : Fin 4 → V) : basisProduct z S y ^ 2 = ∏ i, w i (y i) := by
    unfold basisProduct
    rw [pow_two, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ S <;> simp [w, hi, pow_two]
  have hc : (∏ i : {i : Fin 4 // ¬maskBit out i = true}, ∑ v : V, w i.val v) =
      denominator (V := V) out S := by
    calc
      _ = ∏ i : Fin 4, if ¬maskBit out i = true then (∑ v : V, w i v) else 1 :=
        (prod_ite_subtype (fun i : Fin 4 => ¬maskBit out i = true)
          (fun i => ∑ v : V, w i v)).symm
      _ = ∏ i : Fin 4, (if maskBit out i = true then 1 else Q) *
          (if i ∈ S then Q-1 else 1) := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hi : maskBit out i = true
        · have hs : i ∉ S := by
            intro hs
            have hf := hd i hs
            simp [hf] at hi
          simp [hi, hs]
        · by_cases hs : i ∈ S
          · simp [hi, hs, w, BiasTensorEnergy.basis_square_sum]
          · simp [hi, hs, w, Finset.card_univ, nsmul_eq_mul]
      _ = _ := denominator_product out S
  simp_rw [hb]
  rw [weighted_sum_split out w hw F, hc]

/-- Exact mixed energy: output J/Z summation contributes precisely one
denominator, including empty residual or bias coordinate sets. -/
theorem energy_eq (z : V) (hn : 1 < Fintype.card V) (out : Fin 16)
    (S : Finset (Fin 4)) (hd : Disjoint out S) (R : V → V → ℝ)
    (g : (Fin 4 → V) → ℝ) :
    (∑ y : Fin 4 → V, action (kernel z out S R) g y ^ 2) =
      (∑ v : MaskCoordinates out → V,
        action (coordinateKernel (fun _ : MaskCoordinates out => R))
          (weightedMarginal z out S g) v ^ 2) / denominator (V := V) out S := by
  have hQ : (1 : ℝ) < Q := by exact_mod_cast hn
  have h0 : Q ≠ 0 := by linarith
  have h1 : Q-1 ≠ 0 := by linarith
  have hD : denominator (V := V) out S ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ h1)
  let F : (MaskCoordinates out → V) → ℝ := fun v =>
    action (coordinateKernel (fun _ : MaskCoordinates out => R))
      (weightedMarginal z out S g) v ^ 2
  have hp (y : Fin 4 → V) :
      action (kernel z out S R) g y ^ 2 =
        (basisProduct z S y ^ 2 * F (fun i => y i.val)) /
          denominator (V := V) out S ^ 2 := by
    rw [action_eq z hn out S hd R]
    dsimp [F]
    ring
  calc
    _ = (∑ y : Fin 4 → V, basisProduct z S y ^ 2 *
        F (fun i : MaskCoordinates out => y i.val)) /
          denominator (V := V) out S ^ 2 := by
      simp_rw [hp]
      exact (Finset.sum_div _ _ _).symm
    _ = (denominator (V := V) out S * ∑ v : MaskCoordinates out → V, F v) /
          denominator (V := V) out S ^ 2 := by
      rw [basis_square_weighted_sum z out S hd F]
    _ = _ := by
      change (_ * ∑ v : MaskCoordinates out → V, F v) / _ ^ 2 =
        (∑ v : MaskCoordinates out → V, F v) / _
      field_simp [hD]
      <;> ring

end AESPaper.MixedTensorEnergy
