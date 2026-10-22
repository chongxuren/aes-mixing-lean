import AESConcrete.FourteenResponse
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Future conditional fourteen-response energy and scalar comparison

This adapter combines four single, six pair and four triple response estimates
against the same supplied amplitude energy. Full-response cancellation and
quadruple kernel vanishing remain explicit caller premises. The event-value
type is arbitrary with the stated cardinality; no physical event indexing or
selected-minor response identity is asserted here.

The rational pair norm uses rho squared divided by kappa = 6615/8 < 29 squared.
The final factor sixteen is only an exact scalar certificate comparison.
This source and its dependencies still require compilation and independent
review. No physical cap, inventory addition, return or complete AES theorem is
asserted. Constructive mathematics only; no attacks. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct reference
pairs and the fixed AES 10/14/16 target remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleUniformResponseEnergy
open AESConcrete.UniformGraphScalar (rho kappa rho_nonneg kappa_nonneg)
open AESConcrete.ActivityCodeScalar (q s q_pos s_pos s_sq q_sub_one_pos)
open AESRound.Terminal (lambda)
open AESRound.Certificate (L)

/-- Rational norm coefficients for the three proper-event sizes. -/
def singleNorm : ℝ := q * rho * kappa
def pairNorm : ℝ := 29 * s * rho * kappa
def tripleNorm : ℝ := rho * kappa

theorem singleNorm_nonneg : 0 ≤ singleNorm := by
  unfold singleNorm
  exact mul_nonneg (mul_nonneg (le_of_lt q_pos) rho_nonneg) kappa_nonneg

theorem pairNorm_nonneg : 0 ≤ pairNorm := by
  unfold pairNorm
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt s_pos)) rho_nonneg) kappa_nonneg

theorem tripleNorm_nonneg : 0 ≤ tripleNorm :=
  mul_nonneg rho_nonneg kappa_nonneg

theorem singleNorm_sq : singleNorm ^ 2 = q ^ 2 * rho ^ 2 * kappa ^ 2 := by
  unfold singleNorm
  ring

theorem tripleNorm_sq : tripleNorm ^ 2 = rho ^ 2 * kappa ^ 2 := by
  unfold tripleNorm
  ring

theorem rho_sq_div_kappa : rho ^ 2 / kappa = 6615 / 8 := by
  norm_num [rho, kappa]

theorem rho_sq_div_kappa_lt_29_sq : rho ^ 2 / kappa < (29 : ℝ) ^ 2 := by
  rw [rho_sq_div_kappa]
  norm_num

theorem rho_sq_le_29_sq_mul_kappa : rho ^ 2 ≤ (29 : ℝ) ^ 2 * kappa := by
  have hkappa : 0 < kappa := by norm_num [kappa]
  exact le_of_lt ((div_lt_iff₀ hkappa).mp rho_sq_div_kappa_lt_29_sq)

/-- One rational envelope applies to every pair restriction. -/
theorem pair_energy_le_pairNorm_sq : q * rho ^ 4 * kappa ≤ pairNorm ^ 2 := by
  calc
    _ = (q * rho ^ 2 * kappa) * rho ^ 2 := by ring
    _ ≤ (q * rho ^ 2 * kappa) * ((29 : ℝ) ^ 2 * kappa) :=
      mul_le_mul_of_nonneg_left rho_sq_le_29_sq_mul_kappa
        (mul_nonneg (mul_nonneg (le_of_lt q_pos) (sq_nonneg rho)) kappa_nonneg)
    _ = _ := by
      unfold pairNorm
      rw [← s_sq]
      ring

/-- Conditional response coefficient, before any physical support aggregation. -/
def C_safe : ℝ :=
  rho ^ 2 * kappa ^ 2 * (4 * q + 174 * s + 4) ^ 2 / (q - 1) ^ 4

theorem C_safe_nonneg : 0 ≤ C_safe := by
  unfold C_safe
  exact div_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg rho) (sq_nonneg kappa)) (sq_nonneg _))
    (pow_nonneg (le_of_lt q_sub_one_pos) 4)

/-- Four, six and four norms are added before squaring. -/
theorem fourteen_coefficient_eq :
    (4 * singleNorm + 6 * pairNorm + 4 * tripleNorm) ^ 2 / (q - 1) ^ 4 = C_safe := by
  unfold singleNorm pairNorm tripleNorm C_safe
  ring

section ConditionalResponse
variable {S Y Z V : Type*} [Fintype S] [Fintype Y] [Fintype Z]
    [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- A conditional adapter only: the caller must identify all fourteen raw
responses and prove both endpoint premises. All categories use the same g. -/
theorem conditional14_response_energy
    (hcard : (Fintype.card V : ℝ) = q)
    (h : S → ℝ) (K : Y → S → ℝ) (events : Fin 4 → S → V) (g : Z → ℝ)
    (hfull : WeightedResponse.rawResponse h K = 0)
    (hquad : ∀ y x, events 0 x = 0 → events 1 x = 0 →
      events 2 x = 0 → events 3 x = 0 → K y x = 0)
    (hA : ∀ i : Fin 4,
      (∑ y, FourteenResponse.singleResponses h K events i y ^ 2) ≤
        (q ^ 2 * rho ^ 2 * kappa ^ 2) * ∑ z, g z ^ 2)
    (hB : ∀ i : Fin 6,
      (∑ y, FourteenResponse.pairResponses h K events i y ^ 2) ≤
        (q * rho ^ 4 * kappa) * ∑ z, g z ^ 2)
    (hC : ∀ i : Fin 4,
      (∑ y, FourteenResponse.tripleResponses h K events i y ^ 2) ≤
        (rho ^ 2 * kappa ^ 2) * ∑ z, g z ^ 2) :
    (∑ y, FourteenResponse.weightedResponse h K events y ^ 2) ≤
      C_safe * ∑ z, g z ^ 2 := by
  have hn : 1 ≤ Fintype.card V := by
    have hn' : (1 : ℝ) ≤ Fintype.card V := by
      rw [hcard]
      norm_num [q]
    exact_mod_cast hn'
  have henergy : 0 ≤ ∑ z, g z ^ 2 :=
    Finset.sum_nonneg (fun z _ => sq_nonneg (g z))
  have hA' : ∀ i : Fin 4,
      (∑ y, FourteenResponse.singleResponses h K events i y ^ 2) ≤
        singleNorm ^ 2 * ∑ z, g z ^ 2 := by
    intro i
    rw [singleNorm_sq]
    exact hA i
  have hB' : ∀ i : Fin 6,
      (∑ y, FourteenResponse.pairResponses h K events i y ^ 2) ≤
        pairNorm ^ 2 * ∑ z, g z ^ 2 := by
    intro i
    exact (hB i).trans
      (mul_le_mul_of_nonneg_right pair_energy_le_pairNorm_sq henergy)
  have hC' : ∀ i : Fin 4,
      (∑ y, FourteenResponse.tripleResponses h K events i y ^ 2) ≤
        tripleNorm ^ 2 * ∑ z, g z ^ 2 := by
    intro i
    rw [tripleNorm_sq]
    exact hC i
  have he := FourteenResponse.weightedResponse_energy_le hn h K events g hfull hquad
    singleNorm pairNorm tripleNorm singleNorm_nonneg pairNorm_nonneg tripleNorm_nonneg
    hA' hB' hC'
  rw [hcard, fourteen_coefficient_eq] at he
  exact he

end ConditionalResponse

/-- This is the unchanged certificate datum, not a replacement entry. -/
theorem certificate_12_7_entry :
    L (12 : Fin 14) (7 : Fin 14) =
      (4000246387713471 : ℝ) / 77056884765625000000000000 := rfl

/-- Exact rational arithmetic only. The factor sixteen is not derived as
a physical aggregation identity in this conditional scalar module. -/
theorem certificate_bound :
    0 ≤ lambda * L 12 7 ∧ 16 * C_safe ≤ (lambda * L 12 7) ^ 2 := by
  rw [certificate_12_7_entry]
  norm_num [C_safe, rho, kappa, q, s, AESRound.Terminal.lambda]

end AESConcrete.TripleUniformResponseEnergy
