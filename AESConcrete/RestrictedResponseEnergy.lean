import AESConcrete.WordColumnGram
import AESMixing.CoordinateTensor
import AESMixing.Product

/-!
# Extra output columns after an observed information set

The core source labels are explicitly equivalent to all tuples on `I`.
Its tensor energy estimate is an explicit premise, not an asserted actual
AES norm bound.  The remaining coordinates may be arbitrary functions of
the common source.  Fiberwise contraction pays the core energy coefficient;
each extra column pays one further column-energy factor.

Source weights may be signed and unnormalized. No MDS, independent-source,
pointwise-probability, or exact-support hypothesis is hidden in this generic
interface. Those separate semantic and source-energy bounds belong to the
caller. Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.RestrictedResponseEnergy
open AESMixing
open AESConcrete.WordColumnGram (tensorResponse tensorColumn)

variable {C I J V : Type*} [Fintype C] [Fintype I] [Fintype J] [Fintype V]
  [DecidableEq I] [DecidableEq J]

/-- The exact `I ⊕ J` tensor response, with a bijective core label and
arbitrary additional coordinate functions. -/
def splitResponse (T : I → V → V → ℝ) (U : J → V → V → ℝ)
    (e : C ≃ (I → V)) (rest : C → J → V) (μ : C → ℝ)
    (y : I ⊕ J → V) : ℝ :=
  tensorResponse (Sum.elim T U) (fun c => Sum.elim (e c) (rest c)) μ y

theorem splitResponse_apply (T : I → V → V → ℝ) (U : J → V → V → ℝ)
    (e : C ≃ (I → V)) (rest : C → J → V) (μ : C → ℝ)
    (y : I → V) (z : J → V) :
    splitResponse T U e rest μ (Sum.elim y z) =
      ∑ c : C, coordinateKernel T y (e c) *
        (μ c * ∏ j : J, U j (z j) (rest c j)) := by
  simp only [splitResponse, tensorResponse, tensorColumn, coordinateKernel,
    Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Reindexing the source by the actual equivalence preserves its energy. -/
theorem core_reindexed_energy (T : I → V → V → ℝ) (e : C ≃ (I → V)) (s : ℝ)
    (hTensor : ∀ f : (I → V) → ℝ,
      (∑ y, action (coordinateKernel T) f y ^ 2) ≤ s * ∑ x, f x ^ 2)
    (f : C → ℝ) :
    (∑ y : I → V, (∑ c : C, coordinateKernel T y (e c) * f c) ^ 2) ≤
      s * ∑ c : C, f c ^ 2 := by
  have ha (y : I → V) : (∑ c : C, coordinateKernel T y (e c) * f c) =
      action (coordinateKernel T) (fun x => f (e.symm x)) y := by
    simpa only [action, e.symm_apply_apply] using
      e.sum_comp (fun x => coordinateKernel T y x * f (e.symm x))
  simp_rw [ha]
  have h := hTensor (fun x => f (e.symm x))
  have he : (∑ x : I → V, f (e.symm x) ^ 2) = ∑ c : C, f c ^ 2 :=
    e.symm.sum_comp (fun c => f c ^ 2)
  rw [he] at h
  exact h

theorem splitResponse_energy_split
    (T : I → V → V → ℝ) (U : J → V → V → ℝ)
    (e : C ≃ (I → V)) (rest : C → J → V) (μ : C → ℝ) :
    (∑ y : I ⊕ J → V, splitResponse T U e rest μ y ^ 2) =
      ∑ z : J → V, ∑ y : I → V,
        (∑ c : C, coordinateKernel T y (e c) *
          (μ c * ∏ j : J, U j (z j) (rest c j))) ^ 2 := by
  rw [← (Equiv.sumArrowEquivProdArrow I J V).symm.sum_comp
    (fun y => splitResponse T U e rest μ y ^ 2), Fintype.sum_prod_type]
  change (∑ y : I → V, ∑ z : J → V,
    splitResponse T U e rest μ (Sum.elim y z) ^ 2) = _
  rw [Finset.sum_comm]
  simp_rw [splitResponse_apply]

/-- The high-observed-coordinate branch. `s` is already an energy
coefficient; in the intended use it is `nu^(2*card I)`. The core tensor
estimate remains explicit until the caller proves that specialization. -/
theorem split_response_energy
    (T : I → V → V → ℝ) (U : J → V → V → ℝ)
    (e : C ≃ (I → V)) (rest : C → J → V) (μ : C → ℝ) (s δ : ℝ)
    (hs : 0 ≤ s) (_hδ : 0 ≤ δ)
    (hTensor : ∀ f : (I → V) → ℝ,
      (∑ y, action (coordinateKernel T) f y ^ 2) ≤ s * ∑ x, f x ^ 2)
    (hColumn : ∀ j : J, ∀ a : V, (∑ b : V, U j b a ^ 2) ≤ δ) :
    (∑ y : I ⊕ J → V, splitResponse T U e rest μ y ^ 2) ≤
      s * δ ^ Fintype.card J * ∑ c : C, μ c ^ 2 := by
  rw [splitResponse_energy_split]
  calc
    _ ≤ ∑ z : J → V, s * ∑ c : C,
        (μ c * ∏ j : J, U j (z j) (rest c j)) ^ 2 :=
      Finset.sum_le_sum (fun z _ => core_reindexed_energy T e s hTensor
        (fun c => μ c * ∏ j : J, U j (z j) (rest c j)))
    _ = s * ∑ c : C, μ c ^ 2 *
        ∑ z : J → V, (∏ j : J, U j (z j) (rest c j)) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [mul_pow, Finset.mul_sum]
    _ ≤ s * ∑ c : C, μ c ^ 2 * δ ^ Fintype.card J := by
      apply mul_le_mul_of_nonneg_left _ hs
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (product_column_energy_le (fun j b => U j b (rest c j)) δ
          (fun j => hColumn j (rest c j))) (sq_nonneg (μ c))
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Separate source-energy input, for a later restricted product density. -/
theorem split_response_energy_of_source_bound
    (T : I → V → V → ℝ) (U : J → V → V → ℝ)
    (e : C ≃ (I → V)) (rest : C → J → V) (μ : C → ℝ) (s δ B : ℝ)
    (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (hTensor : ∀ f : (I → V) → ℝ,
      (∑ y, action (coordinateKernel T) f y ^ 2) ≤ s * ∑ x, f x ^ 2)
    (hColumn : ∀ j : J, ∀ a : V, (∑ b : V, U j b a ^ 2) ≤ δ)
    (hSource : (∑ c : C, μ c ^ 2) ≤ B) :
    (∑ y : I ⊕ J → V, splitResponse T U e rest μ y ^ 2) ≤
      s * δ ^ Fintype.card J * B :=
  (split_response_energy T U e rest μ s δ hs hδ hTensor hColumn).trans
    (mul_le_mul_of_nonneg_left hSource (mul_nonneg hs (pow_nonneg hδ _)))

end AESConcrete.RestrictedResponseEnergy
