import AESConcrete.ActivityEffectiveMetric
import AESMixing.Walsh
import AES8.Math.PaperDegreeThreeParityCounts

/-! Exact tensor parity spectrum for the actual four-byte activity metric.
The one-bit spectral expansion is tensorized using finite product/sum identities.
The resulting quadratic identity gives the parity lower bound on arbitrary real
coefficients; no matrix eigenvalue or positivity premise is assumed.
Constructive proof work only; no attacks or canonical/vendor/manuscript edits. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeTensorSpectrum
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.ActivityEffectiveMetric
open PaperDegreeThreeParityCounts
set_option autoImplicit false
set_option maxRecDepth 100000

abbrev Cube := BooleanCube 4

def numericBit (n k : ℕ) : Bool := decide (n / 2^k % 2 = 1)
theorem mask_bit_numeric : ∀ A : Fin 16, ∀ i : Fin 4,
    maskBit A i = numericBit A.val i.val := by decide

def bitMetric (r : ℝ) (a b : Bool) : ℝ := if a = b then 1 else r
def bitEigen (r : ℝ) (s : Bool) : ℝ := if s then 1-r else 1+r
def tensorMetric (r : ℝ) (A B : Cube) : ℝ := ∏ i, bitMetric r (A i) (B i)
def tensorEigen (r : ℝ) (s : Cube) : ℝ := ∏ i, bitEigen r (s i)
def parityMetric (A B : Cube) : ℝ :=
  (tensorMetric xi A B + tensorMetric (-xi) A B)/2
def parityEigen (s : Cube) : ℝ := (tensorEigen xi s + tensorEigen (-xi) s)/2

theorem bit_spectral (r : ℝ) (a b : Bool) :
    (∑ s : Bool, bitEigen r s * bitCharacter s a * bitCharacter s b) =
      2*bitMetric r a b := by
  cases a <;> cases b <;> simp [bitEigen, bitCharacter, bitMetric] <;> ring

theorem tensor_spectral (r : ℝ) (A B : Cube) :
    (∑ s : Cube, tensorEigen r s * walsh s A * walsh s B) =
      16*tensorMetric r A B := by
  simp only [tensorEigen, walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i s =>
    bitEigen r s * bitCharacter s (A i) * bitCharacter s (B i))]
  simp_rw [bit_spectral]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, tensorMetric]
  norm_num

theorem parity_spectral (A B : Cube) :
    (∑ s : Cube, parityEigen s * walsh s A * walsh s B) =
      16*parityMetric A B := by
  simp only [parityEigen, add_div, add_mul, Finset.sum_add_distrib,
    div_mul_eq_mul_div, ← Finset.sum_div]
  rw [tensor_spectral, tensor_spectral]
  unfold parityMetric
  ring

/-- These are exactly the three eigenvalues displayed in the frozen paper.
The Boolean-cube eigenvectors are tensor products of (1,1) and (1,-1). -/
theorem parity_eigenvalues (A : Fin 16) :
    parityEigen (maskBit A) =
      if maskSize A = 0 ∨ maskSize A = 4 then 1+6*xi^2+xi^4
      else if maskSize A = 1 ∨ maskSize A = 3 then 1-xi^4
      else (1-xi^2)^2 := by
  fin_cases A <;>
    norm_num [parityEigen, tensorEigen, bitEigen, Fin.prod_univ_succ,
      mask_bit_numeric, numericBit, mask_size_numeric, bitCount, xi]

theorem parity_eigenvalue_lower (s : Cube) : (1-xi^2)^2 ≤ parityEigen s := by
  obtain ⟨A, rfl⟩ := maskBitsEquiv.surjective s
  change (1-xi^2)^2 ≤ parityEigen (maskBit A)
  rw [parity_eigenvalues]
  split_ifs <;> norm_num [xi]

/-- Exact scalar spectral decomposition, including the normalization 16. -/
theorem parity_quadratic (u : Cube → ℝ) :
    16*qForm u parityMetric =
      ∑ s : Cube, parityEigen s * (∑ A : Cube, walsh s A*u A)^2 := by
  have he (s : Cube) : parityEigen s * (∑ A : Cube, walsh s A*u A)^2 =
      ∑ A : Cube, ∑ B : Cube,
        u A*u B*(parityEigen s*walsh s A*walsh s B) := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    ring
  simp_rw [he]
  calc
    _ = ∑ A : Cube, ∑ B : Cube, ∑ s : Cube,
        u A*u B*(parityEigen s*walsh s A*walsh s B) := by
      unfold qForm
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro B _
      rw [← Finset.mul_sum, parity_spectral]
      ring
    _ = ∑ A : Cube, ∑ s : Cube, ∑ B : Cube,
        u A*u B*(parityEigen s*walsh s A*walsh s B) := by
      apply Finset.sum_congr rfl
      intro A _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Lower quadratic bound on the parity average, on all coefficient vectors. -/
theorem parity_quadratic_lower (u : Cube → ℝ) :
    (1-xi^2)^2 * ∑ A : Cube, (u A)^2 ≤ qForm u parityMetric := by
  have h := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset Cube)) =>
    mul_le_mul_of_nonneg_right (parity_eigenvalue_lower s)
      (sq_nonneg (∑ A : Cube, walsh s A*u A)))
  rw [← Finset.mul_sum, walsh_energy, ← parity_quadratic] at h
  norm_num at h
  linarith

/-- The positive-sign tensor is the actual normalized activity-frame metric. -/
theorem tensorMetric_actual (A B : Fin 16) :
    tensorMetric xi (maskBit A) (maskBit B) = activityMetric A B := rfl

theorem same_parity_metric (A B : Fin 16)
    (hpar : maskSize A % 2 = maskSize B % 2) :
    parityMetric (maskBit A) (maskBit B) = activityMetric A B := by
  rw [← tensorMetric_actual]
  fin_cases A <;> fin_cases B <;>
    norm_num [mask_size_numeric, bitCount] at hpar <;>
    norm_num [parityMetric, tensorMetric, bitMetric, Fin.prod_univ_succ, mask_bit_numeric, numericBit, xi]

/-- The parity average agrees with the actual metric on each parity-supported
coefficient vector. This is a principal-block lower bound, not just a spectrum list. -/
theorem supported_quadratic_lower (u : Fin 16 → ℝ) (p : ℕ)
    (hu : ∀ A, maskSize A % 2 ≠ p → u A = 0) :
    (1-xi^2)^2 * ∑ A : Fin 16, (u A)^2 ≤ qForm u activityMetric := by
  let E := maskBitsEquiv
  have h := parity_quadratic_lower (fun s => u (E.symm s))
  have hn : (∑ s : Cube, (u (E.symm s))^2) = ∑ A : Fin 16, (u A)^2 := by
    simpa only [Equiv.symm_apply_apply] using
      (E.sum_comp (fun s => (u (E.symm s))^2)).symm
  have hq : qForm (fun s => u (E.symm s)) parityMetric =
      qForm u (fun A B => parityMetric (maskBit A) (maskBit B)) := by
    unfold qForm
    rw [← E.sum_comp]
    simp only [Equiv.symm_apply_apply]
    apply Finset.sum_congr rfl
    intro A _
    rw [← E.sum_comp]
    simp only [Equiv.symm_apply_apply]
    rfl
  rw [hn, hq] at h
  have he : qForm u (fun A B => parityMetric (maskBit A) (maskBit B)) =
      qForm u activityMetric := by
    unfold qForm
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    by_cases hA : maskSize A % 2 = p
    · by_cases hB : maskSize B % 2 = p
      · dsimp only
        rw [same_parity_metric A B (hA.trans hB.symm)]
      · rw [hu B hB]
        ring
    · rw [hu A hA]
      ring
  rwa [he] at h

end AES8.PaperDegreeThreeTensorSpectrum
