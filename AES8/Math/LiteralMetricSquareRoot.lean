import AES8.Math.LiteralSpectralRows
import AES8.Math.PaperSlopeMetric
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
The literal positive square root and inverse square root of a finite input
metric. Both are constructed by Hermitian spectral diagonalization. The
two-sided inverse and square identities are derived here; they are not inputs
asserting the desired comparison. This isolated source candidate awaits the
root task's formal-node compilation. Constructive scope only, no attacks.
-/

noncomputable section
open scoped BigOperators Matrix

namespace AES8.PaperSlopeLiteral

set_option autoImplicit false

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Real functional calculus using the actual orthonormal eigenbasis. -/
def spectralDiagonal {K : Matrix I I ℝ} (hK : K.IsHermitian) (d : I → ℝ) :
    Matrix I I ℝ :=
  Unitary.conjStarAlgAut ℝ (Matrix I I ℝ) hK.eigenvectorUnitary (Matrix.diagonal d)

theorem spectralDiagonal_mul {K : Matrix I I ℝ} (hK : K.IsHermitian)
    (d e : I → ℝ) :
    spectralDiagonal hK d * spectralDiagonal hK e =
      spectralDiagonal hK (fun i => d i * e i) := by
  unfold spectralDiagonal
  rw [← map_mul, Matrix.diagonal_mul_diagonal]

theorem spectralDiagonal_one {K : Matrix I I ℝ} (hK : K.IsHermitian) :
    spectralDiagonal hK (fun _ => 1) = 1 := by
  simp [spectralDiagonal]

theorem spectralDiagonal_const {K : Matrix I I ℝ} (hK : K.IsHermitian) (a : ℝ) :
    spectralDiagonal hK (fun _ => a) = a • (1 : Matrix I I ℝ) := by
  have hd : Matrix.diagonal (fun _ : I => a) = a • (1 : Matrix I I ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, Matrix.one_apply, hij]
  simp [spectralDiagonal, hd]

theorem spectralDiagonal_sub {K : Matrix I I ℝ} (hK : K.IsHermitian)
    (d e : I → ℝ) :
    spectralDiagonal hK (fun i => d i - e i) =
      spectralDiagonal hK d - spectralDiagonal hK e := by
  unfold spectralDiagonal
  rw [← map_sub]
  congr 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.diagonal, hij]

theorem spectralDiagonal_eigenvalues {K : Matrix I I ℝ} (hK : K.IsHermitian) :
    spectralDiagonal hK hK.eigenvalues = K := by
  simpa [spectralDiagonal, Function.comp_def] using hK.spectral_theorem.symm

theorem spectralDiagonal_posSemidef {K : Matrix I I ℝ} (hK : K.IsHermitian)
    (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) : (spectralDiagonal hK d).PosSemidef := by
  have hp : (Matrix.diagonal d).PosSemidef := Matrix.PosSemidef.diagonal hd
  simpa only [spectralDiagonal, Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose] using
    hp.mul_mul_conjTranspose_same (hK.eigenvectorUnitary : Matrix I I ℝ)

/-- A PSD metric with an actual inverse has strictly positive eigenvalues. -/
theorem metric_eigenvalues_pos (K H : Matrix I I ℝ) (hK : K.PosSemidef)
    (hHK : H * K = 1) (i : I) : 0 < hK.isHermitian.eigenvalues i := by
  have hnonneg : 0 ≤ hK.isHermitian.eigenvalues i := by
    rw [hK.isHermitian.eigenvalues_eq i]
    simpa using hK.dotProduct_mulVec_nonneg ⇑(hK.isHermitian.eigenvectorBasis i)
  have hne : hK.isHermitian.eigenvalues i ≠ 0 := by
    intro hz
    let v : I → ℝ := ⇑(hK.isHermitian.eigenvectorBasis i)
    have hKv : K *ᵥ v = 0 := by
      simpa only [v, hz, zero_smul] using hK.isHermitian.mulVec_eigenvectorBasis i
    have hv : v = 0 := by
      calc
        v = (H * K) *ᵥ v := by rw [hHK, Matrix.one_mulVec]
        _ = H *ᵥ (K *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
        _ = 0 := by rw [hKv, Matrix.mulVec_zero]
    have hv' : hK.isHermitian.eigenvectorBasis i = 0 := by
      ext j
      exact congrFun hv j
    have hn := hK.isHermitian.eigenvectorBasis.norm_eq_one i
    rw [hv', norm_zero] at hn
    norm_num at hn
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

def sqrtMetric {K : Matrix I I ℝ} (hK : K.PosSemidef) : Matrix I I ℝ :=
  spectralDiagonal hK.isHermitian (fun i => Real.sqrt (hK.isHermitian.eigenvalues i))

def inverseSqrtMetric {K : Matrix I I ℝ} (hK : K.PosSemidef) : Matrix I I ℝ :=
  spectralDiagonal hK.isHermitian
    (fun i => (Real.sqrt (hK.isHermitian.eigenvalues i))⁻¹)

theorem sqrtMetric_posSemidef {K : Matrix I I ℝ} (hK : K.PosSemidef) :
    (sqrtMetric hK).PosSemidef :=
  spectralDiagonal_posSemidef _ _ (fun i => Real.sqrt_nonneg _)

theorem inverseSqrtMetric_posSemidef {K : Matrix I I ℝ} (hK : K.PosSemidef) :
    (inverseSqrtMetric hK).PosSemidef :=
  spectralDiagonal_posSemidef _ _ (fun i => inv_nonneg.mpr (Real.sqrt_nonneg _))

theorem sqrtMetric_sq (K H : Matrix I I ℝ) (hK : K.PosSemidef)
    (hHK : H * K = 1) : sqrtMetric hK * sqrtMetric hK = K := by
  rw [sqrtMetric, spectralDiagonal_mul]
  have hd :
      (fun i => Real.sqrt (hK.isHermitian.eigenvalues i) *
        Real.sqrt (hK.isHermitian.eigenvalues i)) = hK.isHermitian.eigenvalues := by
    funext i
    exact Real.mul_self_sqrt (metric_eigenvalues_pos K H hK hHK i).le
  rw [hd, spectralDiagonal_eigenvalues]

theorem inverseSqrtMetric_mul_sqrtMetric (K H : Matrix I I ℝ)
    (hK : K.PosSemidef) (hHK : H * K = 1) :
    inverseSqrtMetric hK * sqrtMetric hK = 1 := by
  rw [inverseSqrtMetric, sqrtMetric, spectralDiagonal_mul]
  have hd :
      (fun i => (Real.sqrt (hK.isHermitian.eigenvalues i))⁻¹ *
        Real.sqrt (hK.isHermitian.eigenvalues i)) = fun _ => (1 : ℝ) := by
    funext i
    exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (metric_eigenvalues_pos K H hK hHK i)))
  rw [hd, spectralDiagonal_one]

theorem sqrtMetric_mul_inverseSqrtMetric (K H : Matrix I I ℝ)
    (hK : K.PosSemidef) (hHK : H * K = 1) :
    sqrtMetric hK * inverseSqrtMetric hK = 1 := by
  rw [sqrtMetric, inverseSqrtMetric, spectralDiagonal_mul]
  have hd :
      (fun i => Real.sqrt (hK.isHermitian.eigenvalues i) *
        (Real.sqrt (hK.isHermitian.eigenvalues i))⁻¹) = fun _ => (1 : ℝ) := by
    funext i
    exact mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (metric_eigenvalues_pos K H hK hHK i)))
  rw [hd, spectralDiagonal_one]

theorem inverseSqrtMetric_sq (K H : Matrix I I ℝ) (hK : K.PosSemidef)
    (hKH : K * H = 1) (hHK : H * K = 1) :
    inverseSqrtMetric hK * inverseSqrtMetric hK = H := by
  let S := inverseSqrtMetric hK
  let R := sqrtMetric hK
  have hSR : S * R = 1 := inverseSqrtMetric_mul_sqrtMetric K H hK hHK
  have hRR : R * R = K := sqrtMetric_sq K H hK hHK
  have hSSK : (S * S) * K = 1 := by
    rw [← hRR]
    calc
      S * S * (R * R) = S * (S * R) * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hSR, Matrix.mul_one, hSR]
  change S * S = H
  calc
    S * S = (S * S) * (K * H) := by rw [hKH, Matrix.mul_one]
    _ = ((S * S) * K) * H := (Matrix.mul_assoc _ _ _).symm
    _ = H := by rw [hSSK, Matrix.one_mul]

/-- The symmetric Gram comparison after inverse-square-root normalization. -/
def gramComparison (S J : Matrix I I ℝ) (c : ℝ) : Matrix I I ℝ := c • (S * J * S)

/-- The printed nonsymmetric product `c H J`. -/
def comparisonProduct (H J : Matrix I I ℝ) (c : ℝ) : Matrix I I ℝ := c • (H * J)

theorem gramComparison_posSemidef (S J : Matrix I I ℝ)
    (hS : S.IsHermitian) (hJ : J.PosSemidef) (c : ℝ) (hc : 0 ≤ c) :
    (gramComparison S J c).PosSemidef := by
  apply Matrix.PosSemidef.smul _ hc
  simpa only [hS.eq] using hJ.conjTranspose_mul_mul_same S

/-- The actual matrix identity behind similarity to `P = c H J`. -/
theorem gramComparison_similar_product (K H J : Matrix I I ℝ)
    (hK : K.PosSemidef) (hKH : K * H = 1) (hHK : H * K = 1) (c : ℝ) :
    inverseSqrtMetric hK * gramComparison (inverseSqrtMetric hK) J c * sqrtMetric hK =
      comparisonProduct H J c := by
  let S := inverseSqrtMetric hK
  let R := sqrtMetric hK
  have hSS : S * S = H := inverseSqrtMetric_sq K H hK hKH hHK
  have hSR : S * R = 1 := inverseSqrtMetric_mul_sqrtMetric K H hK hHK
  change S * (c • (S * J * S)) * R = c • (H * J)
  calc
    _ = c • ((S * S) * J * (S * R)) := by
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = _ := by rw [hSS, hSR, Matrix.mul_one]

theorem gramComparison_spectrum_product (K H J : Matrix I I ℝ)
    (hK : K.PosSemidef) (hKH : K * H = 1) (hHK : H * K = 1) (c : ℝ) :
    spectrum ℝ (comparisonProduct H J c) =
      spectrum ℝ (gramComparison (inverseSqrtMetric hK) J c) := by
  rw [← gramComparison_similar_product K H J hK hKH hHK c]
  exact similarity_spectrum _ _
    (inverseSqrtMetric_mul_sqrtMetric K H hK hHK)
    (sqrtMetric_mul_inverseSqrtMetric K H hK hHK) _

/-- The eigenvalue upper bound gives the Loewner upper comparison in the
orthonormal eigenbasis. This step is spectral, not a weighted Schur proof. -/
theorem spectral_quadratic_le (Q : Matrix I I ℝ) (hQ : Q.IsHermitian)
    (a : ℝ) (heig : ∀ i, |hQ.eigenvalues i| ≤ a) (x : I → ℝ) :
    PaperSlopeMetric.quad Q x ≤ a * (x ⬝ᵥ x) := by
  have hd : ∀ i, 0 ≤ a - hQ.eigenvalues i := fun i =>
    sub_nonneg.mpr ((le_abs_self _).trans (heig i))
  have heq : spectralDiagonal hQ (fun i => a - hQ.eigenvalues i) =
      a • (1 : Matrix I I ℝ) - Q := by
    rw [spectralDiagonal_sub, spectralDiagonal_const, spectralDiagonal_eigenvalues]
  have hp := spectralDiagonal_posSemidef hQ _ hd
  rw [heq] at hp
  have hn := hp.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul] at hn
  exact sub_nonneg.mp hn

theorem quad_symmetric_congruence (S J : Matrix I I ℝ)
    (hS : ∀ i j, S i j = S j i) (x : I → ℝ) :
    PaperSlopeMetric.quad (S * J * S) x =
      PaperSlopeMetric.quad J (S *ᵥ x) := by
  unfold PaperSlopeMetric.quad
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [PaperSlopeMetric.dot_mulVec_symm S hS]
  exact dotProduct_comm _ _

theorem quad_symmetric_square (R : Matrix I I ℝ)
    (hR : ∀ i j, R i j = R j i) (x : I → ℝ) :
    PaperSlopeMetric.quad (R * R) x = (R *ᵥ x) ⬝ᵥ (R *ᵥ x) := by
  unfold PaperSlopeMetric.quad
  rw [← Matrix.mulVec_mulVec]
  exact PaperSlopeMetric.dot_mulVec_symm R hR x (R *ᵥ x)

/-- Transporting the spectral comparison back through the square root
recovers precisely the original metric comparison. -/
theorem metric_quadratic_le_of_gram_spectrum (K H J : Matrix I I ℝ)
    (hK : K.PosSemidef) (hHK : H * K = 1) (c a : ℝ)
    (hQ : (gramComparison (inverseSqrtMetric hK) J c).IsHermitian)
    (heig : ∀ i, |hQ.eigenvalues i| ≤ a) (x : I → ℝ) :
    c * PaperSlopeMetric.quad J x ≤ a * PaperSlopeMetric.quad K x := by
  let S := inverseSqrtMetric hK
  let R := sqrtMetric hK
  have hS : ∀ i j, S i j = S j i := by
    intro i j
    have hs := (inverseSqrtMetric_posSemidef hK).isHermitian
    have he := congrArg (fun M : Matrix I I ℝ => M j i) hs.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using he
  have hR : ∀ i j, R i j = R j i := by
    intro i j
    have hs := (sqrtMetric_posSemidef hK).isHermitian
    have he := congrArg (fun M : Matrix I I ℝ => M j i) hs.eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using he
  have hSR : S * R = 1 := inverseSqrtMetric_mul_sqrtMetric K H hK hHK
  have hRR : R * R = K := sqrtMetric_sq K H hK hHK
  have hx : S *ᵥ (R *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hSR, Matrix.one_mulVec]
  have hleft : PaperSlopeMetric.quad (gramComparison S J c) (R *ᵥ x) =
      c * PaperSlopeMetric.quad J x := by
    simp only [gramComparison, PaperSlopeMetric.quad, Matrix.smul_mulVec,
      dotProduct_smul, smul_eq_mul]
    change c * PaperSlopeMetric.quad (S * J * S) (R *ᵥ x) = _
    rw [quad_symmetric_congruence S J hS, hx]
    rfl
  have hright : (R *ᵥ x) ⬝ᵥ (R *ᵥ x) = PaperSlopeMetric.quad K x := by
    rw [← hRR, quad_symmetric_square R hR]
  have h := spectral_quadratic_le (gramComparison S J c) hQ a heig (R *ᵥ x)
  rwa [hleft, hright] at h

end AES8.PaperSlopeLiteral
