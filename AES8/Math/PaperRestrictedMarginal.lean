import AES8.Math.PaperRestrictedResponse

/-!
# Restricted marginals with fewer observed outputs than free inputs

Choose free input coordinates, then fix `d-j` of them. MDS makes the remaining
`j` coordinates bijective to the marked outputs in each section. The section
weights are normalized product laws; the restricted source itself is never
normalized. This proves the low-observation branch of `lem:marginals`.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedMarginal
open AESMixing PaperMDSGram PaperMDSFiber PaperRestrictedSource PaperRestrictedResponse
open AESConcrete.RestrictedProductDensity AESConcrete.RestrictedMarginalEnergy

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Fixing `d-j` free inputs makes the other `j` free inputs an information
set for the observed outputs. The section bijection is proved from MDS. -/
theorem section_bijective (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed info shared observed : Finset K)
    (hfi : Disjoint fixed info) (hfo : Disjoint fixed observed)
    (hio : Disjoint info observed) (hsub : shared ⊆ info)
    (hi : fixed.card + info.card = k)
    (hs : shared.card + observed.card = info.card) (target : K → V) :
    let e := (informationEquiv C k hk hMDS fixed info hfi hi target).trans
      (FiniteCoordinatePartition.split (V := V) shared info hsub)
    ∀ s : shared → V, Function.Bijective (fun u : ↥(info \ shared) → V =>
      observe C fixed observed target (e.symm (s,u))) := by
  dsimp only
  let e := (informationEquiv C k hk hMDS fixed info hfi hi target).trans
    (FiniteCoordinatePartition.split (V := V) shared info hsub)
  have hso : Disjoint shared observed := by
    apply Finset.disjoint_left.mpr
    intro i hi ho
    exact Finset.disjoint_left.mp hio (hsub hi) ho
  have hfu : Disjoint fixed (shared ∪ observed) := by
    apply Finset.disjoint_left.mpr
    intro i hf hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact Finset.disjoint_left.mp hfi hf (hsub hu)
    · exact Finset.disjoint_left.mp hfo hf hu
  have hsize : fixed.card + (shared ∪ observed).card = k := by
    rw [Finset.card_union_of_disjoint hso]
    omega
  have hinj := (projection_bijective C k hk hMDS fixed (shared ∪ observed)
    hfu hsize target).injective
  intro s
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro u v huv
    have hc : e.symm (s,u) = e.symm (s,v) := by
      apply hinj
      funext i
      rcases Finset.mem_union.mp i.property with hi | ho
      · have hu := congrFun (congrArg Prod.fst (e.apply_symm_apply (s,u))) ⟨i.val, hi⟩
        have hv := congrFun (congrArg Prod.fst (e.apply_symm_apply (s,v))) ⟨i.val, hi⟩
        exact hu.trans hv.symm
      · exact congrFun huv ⟨i.val, ho⟩
    have h := congrArg (fun c => (e c).2) hc
    simpa only [e.apply_symm_apply] using h
  · simp only [Fintype.card_fun, Fintype.card_coe, Finset.card_sdiff_of_subset hsub]
    congr 1
    omega

/-- Energy of the actual unnormalized pushforward. MDS supplies all section
bijections; independence and normalization enter only through the input laws. -/
theorem marginal_energy_low (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs observed : Finset K)
    (hfi : Disjoint fixed inputs) (hfo : Disjoint fixed observed)
    (hio : Disjoint inputs observed) (hfixed : fixed.card ≤ k)
    (hinputs : k - fixed.card ≤ inputs.card) (hobserved : observed.card ≤ k - fixed.card)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (p rho : ℝ) (hp : 0 ≤ p)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ inputs, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho) :
    (∑ y : observed → V, marginal (observe C fixed observed target)
      (density C fixed inputs target mu event) y ^ 2) ≤
      p ^ (2 * (inputs.card - (k - fixed.card))) * rho ^ observed.card := by
  obtain ⟨info, hsub, hcard⟩ := Finset.exists_subset_card_eq hinputs
  obtain ⟨shared, hshared, hsharedcard⟩ := Finset.exists_subset_card_eq
    (show k - fixed.card - observed.card ≤ info.card by omega)
  have hfi' : Disjoint fixed info := by
    apply Finset.disjoint_left.mpr
    intro i hf hi
    exact Finset.disjoint_left.mp hfi hf (hsub hi)
  have hio' : Disjoint info observed := by
    apply Finset.disjoint_left.mpr
    intro i hi ho
    exact Finset.disjoint_left.mp hio (hsub hi) ho
  let e := (informationEquiv C k hk hMDS fixed info hfi' (by omega) target).trans
    (FiniteCoordinatePartition.split (V := V) shared info hshared)
  let lam := productDensity (fun i : shared => mu i.val)
  let a := productDensity (fun i : ↥(info \ shared) => mu i.val)
  have hsection : ∀ s, Function.Bijective (fun u =>
      observe C fixed observed target (e.symm (s,u))) :=
    section_bijective C k hk hMDS fixed info shared observed hfi' hfo hio'
      hshared (by omega) (by omega) target
  have hdom (c : Fiber C fixed target) : density C fixed inputs target mu event c ≤
      p ^ (inputs.card - info.card) * lam (e c).1 * a (e c).2 := by
    apply (density_domination C fixed inputs info hsub target mu event p hp hmu hpoint c).trans_eq
    rw [Finset.prod_coe_sort info (fun i => mu i (c.val.val i)),
      FiniteCoordinatePartition.prod_split shared info hshared]
    change _ = p ^ (inputs.card - info.card) *
      (∏ i : shared, mu i.val (c.val.val i.val)) *
      (∏ i : ↥(info \ shared), mu i.val (c.val.val i.val))
    ring
  have hb := restricted_marginal_energy_le_of_bijective e (observe C fixed observed target)
    hsection lam a (density C fixed inputs target mu event)
    (p ^ (inputs.card - info.card)) (rho ^ Fintype.card ↥(info \ shared))
    (productDensity_nonneg _ (fun i => hmu i.val (hsub (hshared i.property))))
    (productDensity_mass_one _ (fun i => hmass i.val (hsub (hshared i.property))))
    (productDensity_nonneg _ (fun i => hmu i.val (hsub (Finset.mem_sdiff.mp i.property).1)))
    (productDensity_energy_le _ rho
      (fun i => hcollision i.val (hsub (Finset.mem_sdiff.mp i.property).1)))
    (pow_nonneg hp _) (density_nonneg C fixed inputs target mu event hmu) hdom
  have hrest : Fintype.card ↥(info \ shared) = observed.card := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset hshared]
    omega
  simpa only [hrest, hcard, ← pow_mul, Nat.mul_comm] using hb

/-- Low-observation response, after applying the tensor operator to the
already bounded marginal. No monotonicity of signed response is used. -/
theorem restricted_response_energy_low (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs observed : Finset K)
    (hfi : Disjoint fixed inputs) (hfo : Disjoint fixed observed)
    (hio : Disjoint inputs observed) (hfixed : fixed.card ≤ k)
    (hinputs : k - fixed.card ≤ inputs.card) (hobserved : observed.card ≤ k - fixed.card)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (T : K → V → V → ℝ) (p rho nu : ℝ) (hp : 0 ≤ p)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ inputs, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho)
    (hoperator : ∀ i ∈ observed, ∀ g : V → ℝ,
      (∑ y, action (T i) g y ^ 2) ≤ nu ^ 2 * ∑ x, g x ^ 2) :
    (∑ y : observed → V, response C fixed observed target T
      (density C fixed inputs target mu event) y ^ 2) ≤
      p ^ (2 * (inputs.card - (k - fixed.card))) * (rho * nu ^ 2) ^ observed.card := by
  rw [response_eq_marginal_action]
  have ht := AESConcrete.FiniteTensorEnergy.coordinate_energy
    (fun i : observed => T i.val) (fun _ => nu) (fun i => hoperator i.val i.property)
    (marginal (observe C fixed observed target) (density C fixed inputs target mu event))
  have hs := marginal_energy_low C k hk hMDS fixed inputs observed hfi hfo hio hfixed
    hinputs hobserved target mu event p rho hp hmu hmass hpoint hcollision
  apply ht.trans
  apply (mul_le_mul_of_nonneg_left hs (sq_nonneg (∏ _ : observed, nu))).trans_eq
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe, mul_pow, ← pow_mul]
  rw [Nat.mul_comm observed.card 2]
  ring

end AES8.PaperRestrictedMarginal
