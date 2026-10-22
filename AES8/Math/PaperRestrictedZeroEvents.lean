import AES8.Math.PaperRestrictedSource
import AES8.Math.PaperRestrictedZeroAlgebra

/-!
# Specified-zero-event mass under arbitrary MDS diffusion

This module supplies the two Cauchy--Schwarz branches of `lem:marginals` (a).
The density is the actual product of input laws on a prescribed MDS fiber,
with an optional further event indicator. Both information sets and every
section bijection are derived from `IsMDS`; no desired mass or collision
bound on a restricted/conditional law is assumed.

Write `w = inputs.card`, `d = k - fixed.card`, and `z = w-d`. In the graph
of the paper's diffusion, `fixed` contains inactive inputs and the `z`
specified zero outputs, so these are exactly the paper's `w,d,z`.
The generic conclusion is `rho^min(z,d) * p^(z-d)`. A separate lemma below
handles impossible zero fibers using nonzero input support.

Constructive mathematics only. No attacks, numerical searches or manuscript
edits; this module does not assert the concrete diffusion-graph bridge.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperRestrictedZeroEvents

open PaperMDSGram PaperMDSFiber PaperRestrictedSource PaperRestrictedZeroAlgebra
open AESConcrete.RestrictedProductDensity

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Split an information set into two literal physical-coordinate blocks. -/
def informationSplit (C : AddSubgroup (K → V)) (fixed s a : Finset K)
    (target : K → V) (c : Fiber C fixed target) : (s → V) × (a → V) :=
  (fun i => c.val.val i.val, fun i => c.val.val i.val)

theorem informationSplit_bijective (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed s a : Finset K) (hsa : Disjoint s a)
    (hfixed : Disjoint fixed (s ∪ a))
    (hsize : fixed.card + s.card + a.card = k) (target : K → V) :
    Function.Bijective (informationSplit C fixed s a target) := by
  have hinfo := projection_bijective C k hk hMDS fixed (s ∪ a) hfixed
    (by rw [Finset.card_union_of_disjoint hsa]; omega) target
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro c d h
    apply hinfo.injective
    funext i
    rcases Finset.mem_union.mp i.property with hi | hi
    · exact congrFun (congrArg Prod.fst h) ⟨i.val, hi⟩
    · exact congrFun (congrArg Prod.snd h) ⟨i.val, hi⟩
  · rw [prescribed_card C k hk hMDS fixed (by omega) target,
      Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_coe, Fintype.card_coe, ← pow_add]
    congr 1
    omega

def informationSplitEquiv (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed s a : Finset K) (hsa : Disjoint s a)
    (hfixed : Disjoint fixed (s ∪ a))
    (hsize : fixed.card + s.card + a.card = k) (target : K → V) :
    Fiber C fixed target ≃ (s → V) × (a → V) :=
  Equiv.ofBijective _
    (informationSplit_bijective C k hk hMDS fixed s a hsa hfixed hsize target)

omit [Fintype K] in
/-- Factor a product on two disjoint physical blocks. -/
theorem prod_union (a b : Finset K) (hab : Disjoint a b) (f : K → ℝ) :
    (∏ i : ↥(a ∪ b), f i.val) =
      (∏ i : a, f i.val) * (∏ i : b, f i.val) := by
  rw [Finset.prod_coe_sort (a ∪ b) f, Finset.prod_union hab,
    ← Finset.prod_coe_sort a f, ← Finset.prod_coe_sort b f]

/-- Two disjoint full information sets give the branch with point caps on
all remaining input factors. The sets are constructed from cardinality. -/
theorem mass_le_high (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs : Finset K) (hd : Disjoint fixed inputs)
    (hfixed : fixed.card ≤ k) (hfit : 2 * (k - fixed.card) ≤ inputs.card)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (p rho : ℝ) (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho) :
    (∑ c : Fiber C fixed target, density C fixed inputs target mu event c) ≤
      rho ^ (k - fixed.card) * p ^ (inputs.card - 2 * (k - fixed.card)) := by
  obtain ⟨a, ha, hca⟩ := Finset.exists_subset_card_eq
    (show k - fixed.card ≤ inputs.card by omega)
  have hfitb : k - fixed.card ≤ (inputs \ a).card := by
    rw [Finset.card_sdiff_of_subset ha, hca]
    omega
  obtain ⟨b, hb, hcb⟩ := Finset.exists_subset_card_eq hfitb
  have hbsub : b ⊆ inputs := fun i hi => (Finset.mem_sdiff.mp (hb hi)).1
  have hab : Disjoint a b := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact (Finset.mem_sdiff.mp (hb hj)).2 hi)
  have habsub : a ∪ b ⊆ inputs := Finset.union_subset ha hbsub
  have hda : Disjoint fixed a := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact Finset.disjoint_left.mp hd hi (ha hj))
  have hdb : Disjoint fixed b := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact Finset.disjoint_left.mp hd hi (hbsub hj))
  let e := informationEquiv C k hk hMDS fixed a hda (by omega) target
  let f := informationEquiv C k hk hMDS fixed b hdb (by omega) target
  have he (c : Fiber C fixed target) (i : a) : e c i = c.val.val i.val := rfl
  have hf (c : Fiber C fixed target) (i : b) : f c i = c.val.val i.val := rfl
  have henergyA := productDensity_energy_le (fun i : a => mu i.val) rho
    (fun i => hcollision i.val (ha i.property))
  have henergyB := productDensity_energy_le (fun i : b => mu i.val) rho
    (fun i => hcollision i.val (hbsub i.property))
  simp only [Fintype.card_coe, hca] at henergyA
  simp only [Fintype.card_coe, hcb] at henergyB
  have hdom (c : Fiber C fixed target) :
      density C fixed inputs target mu event c ≤
        p ^ (inputs.card - 2 * (k - fixed.card)) *
          productDensity (fun i : a => mu i.val) (e c) *
            productDensity (fun i : b => mu i.val) (f c) := by
    have h := density_domination C fixed inputs (a ∪ b) habsub target mu event
      p hp hmu hpoint c
    rw [Finset.card_union_of_disjoint hab, hca, hcb,
      prod_union a b hab (fun i => mu i (c.val.val i))] at h
    simpa only [productDensity, he, hf, mul_assoc,
      show k - fixed.card + (k - fixed.card) = 2 * (k - fixed.card) by omega] using h
  have h := dominated_paired_mass_le e f
    (productDensity (fun i : a => mu i.val))
    (productDensity (fun i : b => mu i.val))
    (density C fixed inputs target mu event)
    (p ^ (inputs.card - 2 * (k - fixed.card))) (rho ^ (k - fixed.card))
    (pow_nonneg hp _) (pow_nonneg hrho _) henergyA henergyB hdom
  exact h.trans_eq (mul_comm _ _)

/-- In the low-zero branch the remaining coordinates are averaged with their
original normalized product law. Both size-`d` parametrizations share this
block; their section bijection is a consequence of MDS. -/
theorem mass_le_low (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs : Finset K) (hd : Disjoint fixed inputs)
    (hfixed : fixed.card ≤ k) (hinputs : k - fixed.card ≤ inputs.card)
    (hfit : inputs.card ≤ 2 * (k - fixed.card))
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ inputs, (∑ x, mu i x) = 1)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho) :
    (∑ c : Fiber C fixed target, density C fixed inputs target mu event c) ≤
      rho ^ (inputs.card - (k - fixed.card)) := by
  let z := inputs.card - (k - fixed.card)
  obtain ⟨a, ha, hca⟩ := Finset.exists_subset_card_eq
    (show z ≤ inputs.card by omega)
  have hfitb : z ≤ (inputs \ a).card := by
    rw [Finset.card_sdiff_of_subset ha, hca]
    dsimp [z]
    omega
  obtain ⟨b, hb, hcb⟩ := Finset.exists_subset_card_eq hfitb
  let s := inputs \ (a ∪ b)
  have hbsub : b ⊆ inputs := fun i hi => (Finset.mem_sdiff.mp (hb hi)).1
  have hab : Disjoint a b := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact (Finset.mem_sdiff.mp (hb hj)).2 hi)
  have habsub : a ∪ b ⊆ inputs := Finset.union_subset ha hbsub
  have hssub : s ⊆ inputs := fun i hi => (Finset.mem_sdiff.mp hi).1
  have hsa : Disjoint s a := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left b hj))
  have hsb : Disjoint s b := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_right a hj))
  have hscard : s.card = inputs.card - 2 * z := by
    dsimp [s]
    rw [Finset.card_sdiff_of_subset habsub, Finset.card_union_of_disjoint hab, hca, hcb]
    congr 1
    omega
  have hdsa : Disjoint fixed (s ∪ a) := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact Finset.disjoint_left.mp hd hi ((Finset.union_subset hssub ha) hj))
  have hdsb : Disjoint fixed (s ∪ b) := Finset.disjoint_left.mpr (by
    intro i hi hj
    exact Finset.disjoint_left.mp hd hi ((Finset.union_subset hssub hbsub) hj))
  have hsizeA : fixed.card + s.card + a.card = k := by
    rw [hscard, hca]
    dsimp [z]
    omega
  have hsizeB : fixed.card + s.card + b.card = k := by
    rw [hscard, hcb]
    dsimp [z]
    omega
  let e := informationSplitEquiv C k hk hMDS fixed s a hsa hdsa hsizeA target
  let f := informationSplitEquiv C k hk hMDS fixed s b hsb hdsb hsizeB target
  have henergyA := productDensity_energy_le (fun i : a => mu i.val) rho
    (fun i => hcollision i.val (ha i.property))
  have henergyB := productDensity_energy_le (fun i : b => mu i.val) rho
    (fun i => hcollision i.val (hbsub i.property))
  simp only [Fintype.card_coe, hca] at henergyA
  simp only [Fintype.card_coe, hcb] at henergyB
  apply section_paired_mass_le e f (fun _ => rfl)
    (productDensity (fun i : s => mu i.val))
    (productDensity (fun i : a => mu i.val))
    (productDensity (fun i : b => mu i.val))
    (density C fixed inputs target mu event) (rho ^ z)
    (productDensity_nonneg _ (fun i => hmu i.val (hssub i.property)))
    (productDensity_mass_one _ (fun i => hmass i.val (hssub i.property)))
    (pow_nonneg hrho _) henergyA henergyB
  intro c
  have heS (i : s) : (e c).1 i = c.val.val i.val := rfl
  have heA (i : a) : (e c).2 i = c.val.val i.val := rfl
  have hfB (i : b) : (f c).2 i = c.val.val i.val := rfl
  have hprod :
      (∏ i ∈ inputs, mu i (c.val.val i)) =
        productDensity (fun i : s => mu i.val) (e c).1 *
          productDensity (fun i : a => mu i.val) (e c).2 *
            productDensity (fun i : b => mu i.val) (f c).2 := by
    rw [FiniteCoordinatePartition.prod_split (a ∪ b) inputs habsub,
      prod_union a b hab (fun i => mu i (c.val.val i))]
    simp only [productDensity, heS, heA, hfB]
    ring
  unfold density
  split_ifs
  · exact hprod.le
  · exact mul_nonneg
      (mul_nonneg
        (productDensity_nonneg (fun i : s => mu i.val)
          (fun i => hmu i.val (hssub i.property)) (e c).1)
        (productDensity_nonneg (fun i : a => mu i.val)
          (fun i => hmu i.val (ha i.property)) (e c).2))
      (productDensity_nonneg (fun i : b => mu i.val)
        (fun i => hmu i.val (hbsub i.property)) (f c).2)

/-- The arbitrary-alphabet specified-event bound. In the diffusion graph,
`inputs.card - d` is the number of prescribed output zeros. A further input
indicator is retained without renormalizing the density. -/
theorem mass_le_min (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs : Finset K) (hd : Disjoint fixed inputs)
    (hfixed : fixed.card ≤ k) (hinputs : k - fixed.card ≤ inputs.card)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (p rho : ℝ) (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ inputs, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho) :
    (∑ c : Fiber C fixed target, density C fixed inputs target mu event c) ≤
      rho ^ min (inputs.card - (k - fixed.card)) (k - fixed.card) *
        p ^ (inputs.card - 2 * (k - fixed.card)) := by
  by_cases hlow : inputs.card ≤ 2 * (k - fixed.card)
  · have hmin : min (inputs.card - (k - fixed.card)) (k - fixed.card) =
        inputs.card - (k - fixed.card) := Nat.min_eq_left (by omega)
    have hexp : inputs.card - 2 * (k - fixed.card) = 0 := by omega
    simpa only [hmin, hexp, pow_zero, mul_one] using
      mass_le_low C k hk hMDS fixed inputs hd hfixed hinputs hlow target mu event
        rho hrho hmu hmass hcollision
  · have hmin : min (inputs.card - (k - fixed.card)) (k - fixed.card) =
        k - fixed.card := Nat.min_eq_right (by omega)
    simpa only [hmin] using
      mass_le_high C k hk hMDS fixed inputs hd hfixed (by omega) target mu event
        p rho hp hrho hmu hpoint hcollision

/-- The exponents stated in `eq:zero-events`, using the literal input count
and shortened-fiber dimension. Natural subtraction is truncated at zero. -/
theorem paper_mass_le (C : AddSubgroup (K → V)) (k w z : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs : Finset K) (hd : Disjoint fixed inputs)
    (hfixed : fixed.card ≤ k) (hw : inputs.card = w)
    (hdim : k - fixed.card = w - z) (hz : z < w)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (p rho : ℝ) (hp : 0 ≤ p) (hrho : 0 ≤ rho)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ inputs, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho) :
    (∑ c : Fiber C fixed target, density C fixed inputs target mu event c) ≤
      rho ^ min z (w - z) * p ^ (2 * z - w) := by
  have hb := mass_le_min C k hk hMDS fixed inputs hd hfixed (by omega)
    target mu event p rho hp hrho hmu hmass hpoint hcollision
  simpa only [hw, hdim, show w - (w - z) = z by omega,
    show w - 2 * (w - z) = 2 * z - w by omega] using hb

/-- Replace all but one collision factor by a point cap. This is the
algebraic last sentence of part (a), for positive `z,d`. -/
theorem zero_event_factor_le_simple (z d : ℕ) (hz : 0 < z) (hd : 0 < d)
    (rho p : ℝ) (hrho : 0 ≤ rho) (hrhop : rho ≤ p) :
    rho ^ min z d * p ^ (z - d) ≤ rho * p ^ (z - 1) := by
  have hp : 0 ≤ p := hrho.trans hrhop
  have hminpos : 0 < min z d := lt_min hz hd
  have hexp : min z d - 1 + (z - d) = z - 1 := by
    by_cases hzd : z ≤ d
    · rw [Nat.min_eq_left hzd]
      omega
    · rw [Nat.min_eq_right (by omega)]
      omega
  have hpower : rho ^ min z d ≤ rho * p ^ (min z d - 1) := by
    calc
      rho ^ min z d = rho * rho ^ (min z d - 1) := by
        nth_rw 1 [show min z d = (min z d - 1) + 1 by omega]
        rw [pow_succ, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hrho hrhop _) hrho
  calc
    _ ≤ (rho * p ^ (min z d - 1)) * p ^ (z - d) :=
      mul_le_mul_of_nonneg_right hpower (pow_nonneg hp _)
    _ = rho * p ^ (min z d - 1 + (z - d)) := by rw [mul_assoc, ← pow_add]
    _ = rho * p ^ (z - 1) := by rw [hexp]

/-- The simpler `rho * p^(z-1)` zero-event mass bound under `rho ≤ p`. -/
theorem paper_mass_le_simple (C : AddSubgroup (K → V)) (k w z : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs : Finset K) (hd : Disjoint fixed inputs)
    (hfixed : fixed.card ≤ k) (hw : inputs.card = w)
    (hdim : k - fixed.card = w - z) (hz0 : 0 < z) (hz : z < w)
    (target : K → V) (mu : K → V → ℝ) (event : Fiber C fixed target → Prop)
    (p rho : ℝ) (hrho : 0 ≤ rho) (hrhop : rho ≤ p)
    (hmu : ∀ i ∈ inputs, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ inputs, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ inputs, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ inputs, (∑ x, mu i x ^ 2) ≤ rho) :
    (∑ c : Fiber C fixed target, density C fixed inputs target mu event c) ≤
      rho * p ^ (z - 1) := by
  have hb := paper_mass_le C k w z hk hMDS fixed inputs hd hfixed hw hdim hz
    target mu event p rho (hrho.trans hrhop) hrho hmu hmass hpoint hcollision
  have hs := zero_event_factor_le_simple z (w - z) hz0 (by omega) rho p hrho hrhop
  have hexp : z - (w - z) = 2 * z - w := by omega
  rw [hexp] at hs
  exact hb.trans hs

omit [DecidableEq K] [Fintype V] [DecidableEq V] in
/-- Prescribing zero at at least `k` physical coordinates forces the entire
MDS codeword to zero. This uses injectivity of a subset of size `k`. -/
theorem codeword_eq_zero_of_prescribed_zero (C : AddSubgroup (K → V)) (k : ℕ)
    (_hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed : Finset K) (hfixed : k ≤ fixed.card)
    (c : Fiber C fixed (0 : K → V)) : c.val = 0 := by
  obtain ⟨info, hsub, hcard⟩ := Finset.exists_subset_card_eq hfixed
  apply (hMDS (fun i => i ∈ info) (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard)).injective
  funext i
  change c.val.val i.val = 0
  exact c.property i.val (hsub i.property)

/-- If at least one original input law vanishes at zero, the forced-zero
fiber has zero product weight, even with any further event indicator. -/
theorem density_eq_zero_of_prescribed_zero (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs : Finset K) (hfixed : k ≤ fixed.card)
    (mu : K → V → ℝ) (hzero : ∃ i ∈ inputs, mu i 0 = 0)
    (event : Fiber C fixed (0 : K → V) → Prop)
    (c : Fiber C fixed (0 : K → V)) :
    density C fixed inputs 0 mu event c = 0 := by
  obtain ⟨i, hi, hmui⟩ := hzero
  have hc := codeword_eq_zero_of_prescribed_zero C k hk hMDS fixed hfixed c
  have hci : c.val.val i = 0 := congrArg (fun x : C => x.val i) hc
  unfold density
  split_ifs
  · exact Finset.prod_eq_zero hi (by rw [hci, hmui])
  · rfl

/-- The impossible specified-zero event has mass zero. For the diffusion
graph, `z ≥ w` makes `fixed.card ≥ k`; each active law has `mu i 0 = 0`. -/
theorem mass_eq_zero_of_prescribed_zero (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed inputs : Finset K) (hfixed : k ≤ fixed.card)
    (mu : K → V → ℝ) (hzero : ∃ i ∈ inputs, mu i 0 = 0)
    (event : Fiber C fixed (0 : K → V) → Prop) :
    (∑ c : Fiber C fixed (0 : K → V), density C fixed inputs 0 mu event c) = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  exact density_eq_zero_of_prescribed_zero C k hk hMDS fixed inputs hfixed
    mu hzero event c

end AES8.PaperRestrictedZeroEvents
