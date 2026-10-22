import AES8.Math.PaperMDSFiber
import AES8.Math.FiniteCoordinatePartition
import AESConcrete.RestrictedProductDensity

/-!
# Product-source energy on a shortened MDS fiber

This is the source-density step of `lem:marginals`. An arbitrary extra event
is retained as an indicator, without conditioning or normalization. The free
input information set is selected from the actual input coordinates and its
bijection is derived from MDS. No source-energy bound is assumed.

The code dimension and alphabet are arbitrary. The output-response estimate
belongs to `PaperRestrictedResponse`; zero-event mass is a separate obligation.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedSource
open PaperMDSGram PaperMDSFiber
open AESConcrete.RestrictedProductDensity

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The literal joint-event density on codewords with prescribed coordinates. -/
def density (C : AddSubgroup (K → V)) (fixed inputs : Finset K) (target : K → V)
    (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (c : Fiber C fixed target) : ℝ :=
  if event c then ∏ i ∈ inputs, mu i (c.val.val i) else 0

theorem density_nonneg (C : AddSubgroup (K → V)) (fixed inputs : Finset K)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x) (c : Fiber C fixed target) :
    0 ≤ density C fixed inputs target mu event c := by
  unfold density
  split_ifs
  · exact Finset.prod_nonneg (fun i hi => hmu i hi _)
  · exact le_rfl

/-- Pointwise domination on a chosen input subset. This precedes every
application of a signed channel. -/
theorem density_domination (C : AddSubgroup (K → V)) (fixed inputs info : Finset K)
    (hsub : info ⊆ inputs) (target : K → V) (mu : K → V → ℝ)
    (event : Fiber C fixed target → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p) (c : Fiber C fixed target) :
    density C fixed inputs target mu event c ≤
      p ^ (inputs.card - info.card) * ∏ i : info, mu i.val (c.val.val i.val) := by
  have hprod : 0 ≤ ∏ i : info, mu i.val (c.val.val i.val) :=
    Finset.prod_nonneg (fun i _ => hmu i.val (hsub i.property) _)
  have hrest := productDensity_point_bound
    (fun i : ↥(inputs \ info) => mu i.val) p
    (fun i => hmu i.val (Finset.mem_sdiff.mp i.property).1)
    (fun i => hpoint i.val (Finset.mem_sdiff.mp i.property).1)
    (fun i => c.val.val i.val)
  simp only [productDensity, Fintype.card_coe, Finset.card_sdiff_of_subset hsub] at hrest
  unfold density
  split_ifs
  · rw [FiniteCoordinatePartition.prod_split info inputs hsub]
    exact (mul_le_mul_of_nonneg_left hrest hprod).trans_eq (mul_comm _ _)
  · exact mul_nonneg (pow_nonneg hp _) hprod

/-- The `p^(2z) C^d` source bound, with the `d` free inputs constructed from
MDS. The omitted factor count is `inputs.card - (k - fixed.card)`.
Normalization and nonzero support are not needed for this energy bound. -/
theorem density_energy_le (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs : Finset K) (hd : Disjoint fixed inputs)
    (hfixed : fixed.card ≤ k) (hinputs : k - fixed.card ≤ inputs.card)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (p rho : ℝ) (hp : 0 ≤ p)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho) :
    (∑ c : Fiber C fixed target, density C fixed inputs target mu event c ^ 2) ≤
      p ^ (2 * (inputs.card - (k - fixed.card))) * rho ^ (k - fixed.card) := by
  obtain ⟨info, hsub, hcard⟩ := Finset.exists_subset_card_eq hinputs
  have hdisj : Disjoint fixed info := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hd hi (hsub hj)
  let e := informationEquiv C k hk hMDS fixed info hdisj (by omega) target
  let rest := fun c : Fiber C fixed target => fun i : ↥(inputs \ info) => c.val.val i.val
  have heq (c : Fiber C fixed target) :
      density C fixed inputs target mu event c =
        restrictedDensity e (fun i : info => mu i.val)
          (fun i : ↥(inputs \ info) => mu i.val) rest event c := by
    unfold density restrictedDensity
    split_ifs
    · exact FiniteCoordinatePartition.prod_split info inputs hsub (fun i => mu i (c.val.val i))
    · rfl
  simp_rw [heq]
  have hb := restrictedDensity_energy_le e (fun i : info => mu i.val)
    (fun i : ↥(inputs \ info) => mu i.val) rest event p rho hp
    (fun i => hmu i.val (hsub i.property))
    (fun i => hmu i.val (Finset.mem_sdiff.mp i.property).1)
    (fun i => hpoint i.val (Finset.mem_sdiff.mp i.property).1)
    (fun i => hcollision i.val (hsub i.property))
  simpa only [Fintype.card_coe, Finset.card_sdiff_of_subset hsub, hcard] using hb

end AES8.PaperRestrictedSource
