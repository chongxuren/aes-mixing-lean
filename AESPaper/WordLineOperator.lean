import AESPaper.WordPhysicalEncoding

/-!
# Actual primal and dual line operator bounds

Each nonempty physical marked side supplies one selected core coordinate.
Its actual primal or dual restriction is proved bijective by the physical
information-set theorem. All extra coordinates remain functions of the same
source. The matrix input is arbitrary and signed. The two exact scalars are
1/65536^uniformCount on the primal side and 1/65536^zeroCount after Fourier.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordLineOperator
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros uniformCount)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordPhysicalEncoding (sideCoefficient)
open AESPaper.RectangularFourier (EnergyBound)
attribute [local instance] Classical.propDecidable

section SingletonSplit
variable {K : Type*} [Fintype K] [DecidableEq K]

abbrev Extras (k0 : K) := {k : K // k ≠ k0}

/-- A concrete coordinate is the core; every other physical coordinate is
retained once in the complement. No source label is chosen by cardinality. -/
def singletonSplit (k0 : K) : Unit ⊕ Extras k0 ≃ K where
  toFun := Sum.elim (fun _ => k0) Subtype.val
  invFun k := if h : k = k0 then Sum.inl () else Sum.inr ⟨k,h⟩
  left_inv p := by
    cases p with
    | inl u => cases u; simp
    | inr k => simp [k.property]
  right_inv k := by
    by_cases h : k = k0 <;> simp [h]

@[simp] theorem singletonSplit_core (k0 : K) (u : Unit) :
    singletonSplit k0 (Sum.inl u) = k0 := rfl

@[simp] theorem singletonSplit_extra (k0 : K) (k : Extras k0) :
    singletonSplit k0 (Sum.inr k) = k.val := rfl

theorem extras_card_add_one (k0 : K) :
    Fintype.card (Extras k0) + 1 = Fintype.card K := by
  have h := Fintype.card_congr (singletonSplit k0)
  simp only [Fintype.card_sum, Fintype.card_unit] at h
  omega

end SingletonSplit

/-- Both selected cores account for exactly two marked physical positions. -/
theorem singleton_coefficient_product (m : GraphPosition → Bool)
    (o0 : OutputMarked m) (i0 : InputMarked m) :
    sideCoefficient Unit (Extras o0) * sideCoefficient Unit (Extras i0) =
      WeightedEncoding.nu ^ 2 *
        Real.sqrt (WeightedEncoding.delta ^ (Fintype.card (Marked m) - 2)) := by
  have ho := extras_card_add_one o0
  have hi := extras_card_add_one i0
  have hm := WordMarkedSplit.marked_card m
  have he : Fintype.card (Extras o0) + Fintype.card (Extras i0) =
      Fintype.card (Marked m) - 2 := by omega
  calc
    _ = WeightedEncoding.nu ^ 2 *
        (Real.sqrt (WeightedEncoding.delta ^ Fintype.card (Extras o0)) *
          Real.sqrt (WeightedEncoding.delta ^ Fintype.card (Extras i0))) := by
      simp only [sideCoefficient, Fintype.card_unit, pow_one]
      ring
    _ = WeightedEncoding.nu ^ 2 * Real.sqrt
        (WeightedEncoding.delta ^
          (Fintype.card (Extras o0) + Fintype.card (Extras i0))) := by
      rw [pow_add, Real.sqrt_mul (pow_nonneg WeightedEncoding.delta_nonnegative _)]
    _ = _ := by rw [he]

theorem line_coefficient_nonnegative (ell n : ℕ) :
    0 ≤ WeightedEncoding.nu ^ 2 * Real.sqrt (WeightedEncoding.delta ^ (ell - 2)) /
      (65536 : ℝ)^n := by
  exact div_nonneg (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
    (pow_nonneg (by norm_num) _)

/-- A one-dimensional actual primal source, with one core constructed on
each nonempty physical marked side. No selection is a theorem premise. -/
theorem boundary_primal_line_bound (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + 1 = 4)
    (hO : Nonempty (OutputMarked m)) (hI : Nonempty (InputMarked m)) :
    EnergyBound
      (WordOperatorDuality.reshape m (WordMarkedResponse.boundaryContractedResponse m s))
      (WeightedEncoding.nu ^ 2 *
        Real.sqrt (WeightedEncoding.delta ^ (Fintype.card (Marked m) - 2)) /
          (65536 : ℝ)^uniformCount s) := by
  let o0 : OutputMarked m := Classical.choice hO
  let i0 : InputMarked m := Classical.choice hI
  have hs : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card Unit = 4 := by simpa only [Fintype.card_unit] using hline
  have h := WordPhysicalEncoding.boundary_primal_bound m s
    (singletonSplit o0) (singletonSplit i0) hs hs
  have hc : (1 / (65536 : ℝ)^uniformCount s) *
      (sideCoefficient Unit (Extras o0) * sideCoefficient Unit (Extras i0)) =
      WeightedEncoding.nu ^ 2 *
        Real.sqrt (WeightedEncoding.delta ^ (Fintype.card (Marked m) - 2)) /
          (65536 : ℝ)^uniformCount s := by
    rw [singleton_coefficient_product]
    ring
  rw [hc] at h
  exact h

/-- A one-dimensional actual annihilator. Fourier transport preserves the
physical input adjoints and supplies the exact inverse zero-count factor. -/
theorem boundary_dual_line_bound (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hline : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      (Fintype.card (Marked m) - 1) = 4)
    (hO : Nonempty (OutputMarked m)) (hI : Nonempty (InputMarked m)) :
    EnergyBound
      (WordOperatorDuality.reshape m (WordMarkedResponse.boundaryContractedResponse m s))
      (WeightedEncoding.nu ^ 2 *
        Real.sqrt (WeightedEncoding.delta ^ (Fintype.card (Marked m) - 2)) /
          (65536 : ℝ)^(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))) := by
  let o0 : OutputMarked m := Classical.choice hO
  let i0 : InputMarked m := Classical.choice hI
  have hs : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      (Fintype.card (Marked m) - Fintype.card Unit) = 4 := by
    simpa only [Fintype.card_unit] using hline
  have h := WordPhysicalEncoding.boundary_dual_bound m s
    (Fintype.card (Marked m) - 1) hline (Nat.sub_le _ _)
    (singletonSplit o0) (singletonSplit i0) hs hs
  have hc :
      (1 / (65536 : ℝ)^(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))) *
        (sideCoefficient Unit (Extras o0) * sideCoefficient Unit (Extras i0)) =
      WeightedEncoding.nu ^ 2 *
        Real.sqrt (WeightedEncoding.delta ^ (Fintype.card (Marked m) - 2)) /
          (65536 : ℝ)^(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s)) := by
    rw [singleton_coefficient_product]
    ring
  rw [hc] at h
  exact h

end AESPaper.WordLineOperator
