import AES8.Math.PaperRestrictedSource
import AES8.Math.InformationEncoding
import AESConcrete.RestrictedMarginalEnergy

/-!
# Restricted response after the observed outputs identify the source

The high-observation branch of `lem:marginals` is stated on the actual tensor
response and literal MDS fibers. Both input and output information sets are
derived from MDS, and arbitrary further source events remain unnormalized.
Local operator and column-energy bounds are explicit. Their specialization to
`R = S - P`, and the low-observation branch, are separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedResponse
open AESMixing PaperMDSGram PaperMDSFiber

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Tensor response of an unnormalized source, with physical output labels. -/
def response (C : AddSubgroup (K → V)) (fixed observed : Finset K) (target : K → V)
    (T : K → V → V → ℝ) (f : Fiber C fixed target → ℝ) (y : observed → V) : ℝ :=
  ∑ c : Fiber C fixed target, (∏ i : observed, T i.val (y i) (c.val.val i.val)) * f c

/-- Exact pushforward identity, valid even for signed source weights. The
restricted marginal retains its total mass before the channel acts. -/
theorem response_eq_marginal_action (C : AddSubgroup (K → V))
    (fixed observed : Finset K) (target : K → V)
    (T : K → V → V → ℝ) (f : Fiber C fixed target → ℝ) :
    response C fixed observed target T f =
      action (coordinateKernel (fun i : observed => T i.val))
        (AESConcrete.RestrictedMarginalEnergy.marginal
          (observe C fixed observed target) f) := by
  funext y
  unfold response action AESConcrete.RestrictedMarginalEnergy.marginal
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/-- Encoding bound on arbitrary prescribed MDS fibers. The output information
set is a conclusion of MDS and `d ≤ j`, not an extra analytic premise. -/
theorem response_energy_high (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (hfixed : fixed.card ≤ k) (hobserved : k - fixed.card ≤ observed.card)
    (target : K → V) (T : K → V → V → ℝ) (f : Fiber C fixed target → ℝ)
    (nu delta : ℝ)
    (hoperator : ∀ i ∈ observed, ∀ g : V → ℝ,
      (∑ y, action (T i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ i ∈ observed, ∀ x, (∑ y, T i y x ^ 2) ≤ delta) :
    (∑ y : observed → V, response C fixed observed target T f y ^ 2) ≤
      nu ^ (2 * (k - fixed.card)) * delta ^ (observed.card - (k - fixed.card)) *
        ∑ c : Fiber C fixed target, f c ^ 2 := by
  obtain ⟨info, hsub, hcard⟩ := Finset.exists_subset_card_eq hobserved
  have hdisj : Disjoint fixed info := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hd hi (hsub hj)
  let e := informationEquiv C k hk hMDS fixed info hdisj (by omega) target
  let rest := fun c : Fiber C fixed target => fun i : ↥(observed \ info) => c.val.val i.val
  let E := FiniteCoordinatePartition.split (V := V) info observed hsub
  have heq (y : observed → V) : response C fixed observed target T f y =
      action (InformationEncoding.kernel e rest (fun i : info => T i.val)
        (fun i : ↥(observed \ info) => T i.val)) f (E y) := by
    unfold response action InformationEncoding.kernel
    apply Finset.sum_congr rfl
    intro c _
    apply congrArg (· * f c)
    let g : K → ℝ := fun i => if hi : i ∈ observed then T i (y ⟨i, hi⟩) (c.val.val i) else 1
    have hg : (∏ i : observed, T i.val (y i) (c.val.val i.val)) = ∏ i ∈ observed, g i := by
      rw [← Finset.prod_coe_sort observed g]
      apply Finset.prod_congr rfl
      intro i _
      simp only [g, dif_pos i.property]
    rw [hg, FiniteCoordinatePartition.prod_split info observed hsub]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      simp only [g, dif_pos (hsub i.property)]
      rfl
    · apply Finset.prod_congr rfl
      intro i _
      simp only [g, dif_pos (Finset.mem_sdiff.mp i.property).1]
      rfl
  have hb := InformationEncoding.encoding_energy e rest (fun i : info => T i.val)
    (fun i : ↥(observed \ info) => T i.val) (fun _ => nu) delta
    (fun i => hoperator i.val (hsub i.property))
    (fun i => hcolumn i.val (Finset.mem_sdiff.mp i.property).1) f
  simp_rw [heq]
  rw [E.sum_comp (fun y => action (InformationEncoding.kernel e rest
    (fun i : info => T i.val) (fun i : ↥(observed \ info) => T i.val)) f y ^ 2)]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe,
    Finset.card_sdiff_of_subset hsub, hcard, ← pow_mul, Nat.mul_comm] using hb

/-- High-observation restricted-product response with every geometric and
source-energy premise discharged. `inputs.card - d` is the number of input
probability factors bounded pointwise; all extra events are retained. -/
theorem restricted_response_energy_high (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs observed : Finset K)
    (hdi : Disjoint fixed inputs) (hdo : Disjoint fixed observed)
    (hfixed : fixed.card ≤ k) (hinputs : k - fixed.card ≤ inputs.card)
    (hobserved : k - fixed.card ≤ observed.card)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (T : K → V → V → ℝ) (p rho nu delta : ℝ) (hp : 0 ≤ p) (hdelta : 0 ≤ delta)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho)
    (hoperator : ∀ i ∈ observed, ∀ g : V → ℝ,
      (∑ y, action (T i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ i ∈ observed, ∀ x, (∑ y, T i y x ^ 2) ≤ delta) :
    (∑ y : observed → V, response C fixed observed target T
      (PaperRestrictedSource.density C fixed inputs target mu event) y ^ 2) ≤
      p ^ (2 * (inputs.card - (k - fixed.card))) *
        (rho * nu ^ 2) ^ (k - fixed.card) * delta ^ (observed.card - (k - fixed.card)) := by
  have hb := response_energy_high C k hk hMDS fixed observed hdo hfixed hobserved
    target T (PaperRestrictedSource.density C fixed inputs target mu event) nu delta
    hoperator hcolumn
  have hs := PaperRestrictedSource.density_energy_le C k hk hMDS fixed inputs hdi
    hfixed hinputs target mu event p rho hp hmu hpoint hcollision
  apply hb.trans
  calc
    _ ≤ nu ^ (2 * (k - fixed.card)) * delta ^ (observed.card - (k - fixed.card)) *
        (p ^ (2 * (inputs.card - (k - fixed.card))) * rho ^ (k - fixed.card)) := by
      apply mul_le_mul_of_nonneg_left hs
      exact mul_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg nu) _)
        (pow_nonneg hdelta _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end AES8.PaperRestrictedResponse
