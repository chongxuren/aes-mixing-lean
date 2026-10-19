import AESConcrete.RestrictedResponseEnergy
import AESConcrete.FiniteTensorEnergy
import AESConcrete.RestrictedMarginalEnergy
import AESConcrete.ByteGramDiagonal

/-!
# Actual byte residual constants in the restricted-response interfaces

These wrappers discharge tensor-operator and residual-column premises using
the actual byte resources. Core information-set equivalences, coordinate
functions, source densities and their domination remain explicit caller
inputs. No actual MDS restriction or full multibyte word-column estimate is
asserted here. Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActualRestrictedResponse
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.RestrictedResponseEnergy (splitResponse)
open AESConcrete.RestrictedMarginalEnergy (marginal)

abbrev Byte := BinaryWord 8

/-- Exact pushforward identity for arbitrary signed, unnormalized weights.
The marginal is formed before applying the possibly signed tensor channel. -/
theorem tensorResponse_eq_action_marginal {X K W : Type*}
    [Fintype X] [Fintype K] [Fintype W] [DecidableEq K] [DecidableEq W]
    (T : K → W → W → ℝ) (coord : X → K → W) (μ : X → ℝ) :
    WordColumnGram.tensorResponse T coord μ =
      action (coordinateKernel T) (marginal coord μ) := by
  funext y
  simp only [WordColumnGram.tensorResponse, WordColumnGram.tensorColumn,
    action, marginal, coordinateKernel]
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Exact nonzero residual column energy, and zero energy at the zero label. -/
theorem actual_residual_column_energy (o : Orientation) (a : Byte) :
    (∑ b : Byte, residualMatrix (channel o) 0 b a ^ 2) =
      if a = 0 then 0 else (16766 / 4177920 : ℝ) := by
  have h := ByteGramDiagonal.actual_gram_diagonal o a
  rw [ByteGramDiagonal.residualGram, gram_diagonal] at h
  convert h using 1 <;> norm_num

theorem actual_residual_column_energy_le (o : Orientation) (a : Byte) :
    (∑ b : Byte, residualMatrix (channel o) 0 b a ^ 2) ≤
      (16766 / 4177920 : ℝ) := by
  rw [actual_residual_column_energy]
  split_ifs <;> norm_num

section HighObserved

variable {C I J : Type*} [Fintype C] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- No tensor or column estimate is a premise of this actual specialization.
The source weights may be signed and unnormalized. -/
theorem actual_split_response_energy
    (o : I → Orientation) (p : J → Orientation)
    (e : C ≃ (I → Byte)) (rest : C → J → Byte) (g : C → ℝ) :
    (∑ y : I ⊕ J → Byte, splitResponse
      (fun i => residualMatrix (channel (o i)) 0)
      (fun j => residualMatrix (channel (p j)) 0) e rest g y ^ 2) ≤
      (9 / 128 : ℝ) ^ (2 * Fintype.card I) *
        (16766 / 4177920 : ℝ) ^ Fintype.card J * ∑ c : C, g c ^ 2 :=
  RestrictedResponseEnergy.split_response_energy
    (fun i => residualMatrix (channel (o i)) 0)
    (fun j => residualMatrix (channel (p j)) 0) e rest g
    ((9 / 128 : ℝ) ^ (2 * Fintype.card I)) (16766 / 4177920)
    (by positivity) (by norm_num)
    (FiniteTensorEnergy.actual_byte_residual_coordinate_energy o)
    (fun j => actual_residual_column_energy_le (p j))

/-- Only the separate source-energy inequality is retained as a premise. -/
theorem actual_split_response_energy_of_source_bound
    (o : I → Orientation) (p : J → Orientation)
    (e : C ≃ (I → Byte)) (rest : C → J → Byte) (g : C → ℝ) (B : ℝ)
    (hSource : (∑ c : C, g c ^ 2) ≤ B) :
    (∑ y : I ⊕ J → Byte, splitResponse
      (fun i => residualMatrix (channel (o i)) 0)
      (fun j => residualMatrix (channel (p j)) 0) e rest g y ^ 2) ≤
      (9 / 128 : ℝ) ^ (2 * Fintype.card I) *
        (16766 / 4177920 : ℝ) ^ Fintype.card J * B :=
  (actual_split_response_energy o p e rest g).trans
    (mul_le_mul_of_nonneg_left hSource (by positivity))

end HighObserved

section LowObserved

variable {C S U I : Type*} [Fintype C] [Fintype S] [Fintype U] [Fintype I]
  [DecidableEq I]

/-- Apply the actual parallel residual to an unnormalized dominated marginal.
The MDS/source interface is explicit; every operator constant is concrete. -/
theorem actual_restricted_marginal_energy
    (o : I → Orientation) (e : C ≃ S × U) (coord : C → (I → Byte))
    (E : S → U ≃ (I → Byte))
    (hcoord : ∀ s u, coord (e.symm (s, u)) = E s u)
    (lambda : S → ℝ) (f : U → ℝ) (g : C → ℝ) (scale rho : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s : S, lambda s) = 1)
    (hf_nonneg : ∀ u, 0 ≤ f u) (hf : (∑ u : U, f u ^ 2) ≤ rho)
    (hscale : 0 ≤ scale) (hg : ∀ c, 0 ≤ g c)
    (hdom : ∀ c, g c ≤ scale * lambda (e c).1 * f (e c).2) :
    (∑ y : I → Byte, action (coordinateKernel (fun i =>
      residualMatrix (channel (o i)) 0)) (marginal coord g) y ^ 2) ≤
      (9 / 128 : ℝ) ^ (2 * Fintype.card I) * scale ^ 2 * rho := by
  classical
  have hm := RestrictedMarginalEnergy.restricted_marginal_energy_le
    e coord E hcoord lambda f g scale rho hlambda hmass hf_nonneg hf hscale hg hdom
  have ht := FiniteTensorEnergy.actual_byte_residual_coordinate_energy o (marginal coord g)
  calc
    _ ≤ (9 / 128 : ℝ) ^ (2 * Fintype.card I) *
        (∑ y : I → Byte, marginal coord g y ^ 2) := ht
    _ ≤ (9 / 128 : ℝ) ^ (2 * Fintype.card I) * (scale ^ 2 * rho) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by ring

theorem actual_restricted_marginal_energy_of_bijective
    (o : I → Orientation) (e : C ≃ S × U) (coord : C → (I → Byte))
    (hsection : ∀ s : S, Function.Bijective (fun u : U => coord (e.symm (s, u))))
    (lambda : S → ℝ) (f : U → ℝ) (g : C → ℝ) (scale rho : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s : S, lambda s) = 1)
    (hf_nonneg : ∀ u, 0 ≤ f u) (hf : (∑ u : U, f u ^ 2) ≤ rho)
    (hscale : 0 ≤ scale) (hg : ∀ c, 0 ≤ g c)
    (hdom : ∀ c, g c ≤ scale * lambda (e c).1 * f (e c).2) :
    (∑ y : I → Byte, action (coordinateKernel (fun i =>
      residualMatrix (channel (o i)) 0)) (marginal coord g) y ^ 2) ≤
      (9 / 128 : ℝ) ^ (2 * Fintype.card I) * scale ^ 2 * rho := by
  classical
  let E : S → U ≃ (I → Byte) := fun s => Equiv.ofBijective
    (fun u => coord (e.symm (s, u))) (hsection s)
  exact actual_restricted_marginal_energy o e coord E (fun _ _ => rfl)
    lambda f g scale rho hlambda hmass hf_nonneg hf hscale hg hdom

/-- The low-observed estimate for the tensor response itself, using the
proved pushforward identity rather than assuming a marginal-action match. -/
theorem actual_restricted_tensorResponse_energy_of_bijective
    (o : I → Orientation) (e : C ≃ S × U) (coord : C → (I → Byte))
    (hsection : ∀ s : S, Function.Bijective (fun u : U => coord (e.symm (s, u))))
    (lambda : S → ℝ) (f : U → ℝ) (g : C → ℝ) (scale rho : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s : S, lambda s) = 1)
    (hf_nonneg : ∀ u, 0 ≤ f u) (hf : (∑ u : U, f u ^ 2) ≤ rho)
    (hscale : 0 ≤ scale) (hg : ∀ c, 0 ≤ g c)
    (hdom : ∀ c, g c ≤ scale * lambda (e c).1 * f (e c).2) :
    (∑ y : I → Byte, WordColumnGram.tensorResponse
      (fun i => residualMatrix (channel (o i)) 0) coord g y ^ 2) ≤
      (9 / 128 : ℝ) ^ (2 * Fintype.card I) * scale ^ 2 * rho := by
  rw [tensorResponse_eq_action_marginal]
  exact actual_restricted_marginal_energy_of_bijective
    o e coord hsection lambda f g scale rho hlambda hmass hf_nonneg hf hscale hg hdom

end LowObserved
end AESConcrete.ActualRestrictedResponse
