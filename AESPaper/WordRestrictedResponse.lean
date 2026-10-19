import AESPaper.StartingWord
import AESPaper.WordDamping
import AESConcrete.ActualRestrictedResponse

/-!
# Whole-word residual responses of unnormalized restricted sources

The frozen generic tensor/section lemmas apply to arbitrary joint weights.
This module discharges their channel premises for actual 32-bit AES words,
using nu = 21/131072 and the centered column cap delta < 1/q. Information-set
maps and source domination remain explicit inputs, to be supplied separately
by shortened-MDS source sections. No event mass is divided out, and no
pointwise comparison is applied after the signed residual channel.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AESPaper.WordRestrictedResponse
open AESMixing AESConcrete
open AESPaper.StartingWord (q)
open AESPaper.WordDamping (nu)
open AESConcrete.RestrictedMarginalEnergy (marginal)
open AESConcrete.RestrictedResponseEnergy (splitResponse)

abbrev residual : AES.Word → AES.Word → ℝ := residualMatrix AES.wordSuperboxKernel 0

def delta : ℝ := 17/(15*q) - 1/(q-1)

theorem delta_nonnegative : 0 ≤ delta := by norm_num [delta, q]
theorem delta_lt_inv_q : delta < 1/q := by norm_num [delta, q]
theorem q_nu_sq_le : q * nu^2 ≤ 128 := by norm_num [q, nu]

theorem residual_zero_column (y : AES.Word) : residual y 0 = 0 := by
  unfold residual residualMatrix activityMatrix
  rw [AES.word_superbox_pointed.zero_column]
  by_cases h : y = 0 <;> simp [h]

theorem residual_column_energy_le (a : AES.Word) :
    (∑ y, residual y a ^ 2) ≤ delta := by
  by_cases ha : a = 0
  · subst a
    simp only [residual_zero_column, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]
    exact delta_nonnegative
  · exact (StartingWord.residual_column_energy_lt_sharp a ha).le

theorem residual_coordinate_energy {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → AES.Word) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : I => residual)) f y ^ 2) ≤
      nu^(2 * Fintype.card I) * ∑ x, f x ^ 2 :=
  FiniteTensorEnergy.uniform_coordinate_energy residual nu
    SharpDampedWordNorm.word_superbox_residual_energy f

/-- The high-observation branch: core coordinates identify the source, and
extra output labels may be arbitrary functions of that same source. -/
theorem split_response_energy {C I J : Type*}
    [Fintype C] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (g : C → ℝ) :
    (∑ y, splitResponse (fun _ : I => residual) (fun _ : J => residual)
      e rest g y ^ 2) ≤
      nu^(2 * Fintype.card I) * delta^Fintype.card J * ∑ c, g c ^ 2 :=
  RestrictedResponseEnergy.split_response_energy _ _ e rest g
    (nu^(2 * Fintype.card I)) delta (pow_nonneg WordDamping.nu_nonnegative _)
    delta_nonnegative residual_coordinate_energy (fun _ => residual_column_energy_le)

/-- Retains the source-energy hypothesis rather than hiding its proof. -/
theorem split_response_energy_of_source_bound {C I J : Type*}
    [Fintype C] [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (g : C → ℝ) (B : ℝ)
    (hSource : (∑ c, g c ^ 2) ≤ B) :
    (∑ y, splitResponse (fun _ : I => residual) (fun _ : J => residual)
      e rest g y ^ 2) ≤ nu^(2 * Fintype.card I) * delta^Fintype.card J * B :=
  (split_response_energy e rest g).trans
    (mul_le_mul_of_nonneg_left hSource
      (mul_nonneg (pow_nonneg WordDamping.nu_nonnegative _) (pow_nonneg delta_nonnegative _)))

/-- Low-observation branch. Domination is used on nonnegative source weights
before applying the residual operator to the resulting unnormalized marginal. -/
theorem restricted_marginal_energy {C S U I : Type*}
    [Fintype C] [Fintype S] [Fintype U] [Fintype I] [DecidableEq I]
    (e : C ≃ S × U) (coord : C → I → AES.Word)
    (hsection : ∀ s : S, Function.Bijective (fun u => coord (e.symm (s,u))))
    (lambda : S → ℝ) (f : U → ℝ) (g : C → ℝ) (scale rho : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s, lambda s) = 1)
    (hf_nonneg : ∀ u, 0 ≤ f u) (hf : (∑ u, f u^2) ≤ rho)
    (hscale : 0 ≤ scale) (hg : ∀ c, 0 ≤ g c)
    (hdom : ∀ c, g c ≤ scale * lambda (e c).1 * f (e c).2) :
    (∑ y, action (coordinateKernel (fun _ : I => residual)) (marginal coord g) y ^ 2) ≤
      nu^(2 * Fintype.card I) * scale^2 * rho := by
  have hm := RestrictedMarginalEnergy.restricted_marginal_energy_le_of_bijective
    e coord hsection lambda f g scale rho hlambda hmass hf_nonneg hf hscale hg hdom
  calc
    _ ≤ nu^(2 * Fintype.card I) * ∑ x, marginal coord g x ^ 2 :=
      residual_coordinate_energy (marginal coord g)
    _ ≤ nu^(2 * Fintype.card I) * (scale^2 * rho) :=
      mul_le_mul_of_nonneg_left hm (pow_nonneg WordDamping.nu_nonnegative _)
    _ = _ := by ring

/-- The same low-observation estimate stated as an exact tensor response. -/
theorem restricted_tensorResponse_energy {C S U I : Type*}
    [Fintype C] [Fintype S] [Fintype U] [Fintype I] [DecidableEq I]
    (e : C ≃ S × U) (coord : C → I → AES.Word)
    (hsection : ∀ s : S, Function.Bijective (fun u => coord (e.symm (s,u))))
    (lambda : S → ℝ) (f : U → ℝ) (g : C → ℝ) (scale rho : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s, lambda s) = 1)
    (hf_nonneg : ∀ u, 0 ≤ f u) (hf : (∑ u, f u^2) ≤ rho)
    (hscale : 0 ≤ scale) (hg : ∀ c, 0 ≤ g c)
    (hdom : ∀ c, g c ≤ scale * lambda (e c).1 * f (e c).2) :
    (∑ y, WordColumnGram.tensorResponse (fun _ : I => residual) coord g y ^ 2) ≤
      nu^(2 * Fintype.card I) * scale^2 * rho := by
  rw [ActualRestrictedResponse.tensorResponse_eq_action_marginal]
  exact restricted_marginal_energy e coord hsection lambda f g scale rho
    hlambda hmass hf_nonneg hf hscale hg hdom

end AESPaper.WordRestrictedResponse
