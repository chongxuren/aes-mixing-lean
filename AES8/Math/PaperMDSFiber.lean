/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.PaperMDSGram
import AES8.Math.FiberCollision
import AESMixing.CoordinateCount
import Mathlib.Data.Finset.Card

/-!
# Collision sums on arbitrary affine shortened MDS fibers

This module targets Lemma 7 (`lem:fiber-sum`) in the paper's
`writing/sections/05-fibers.tex`.  An affine fiber is represented literally by
prescribing arbitrary coordinates of an additive MDS code.  Every count and
information-set bijection below is derived from `PaperMDSGram.IsMDS`; neither
constant observation-fiber cardinalities nor a chosen information set are
additional hypotheses.

There are no restrictions on the coordinate count or on the finite alphabet
beyond those of an additive code.  The fixed and observed sets must be
disjoint, and at most the code dimension may be fixed.  The exact exponents
are the fixed-fiber dimension `k - fixed.card` and the observed count
`observed.card`.  Constructive mathematics only; no attacks or AES numerical
claims.  This source does not edit or certify the manuscript.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperMDSFiber

open AESMixing PaperMDSGram

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- An affine shortened fiber, retaining its actual codeword as the point. -/
abbrev Fiber (C : AddSubgroup (K → V)) (fixed : Finset K) (target : K → V) :=
  {c : C // ∀ i ∈ fixed, c.val i = target i}

/-- Restriction to a literal physical coordinate set. -/
def observe (C : AddSubgroup (K → V)) (fixed observed : Finset K)
    (target : K → V) (x : Fiber C fixed target) : observed → V :=
  fun i => x.val.val i.val

/-- A coordinate subset inside a larger coordinate subset carries no extra
labels: flattening its two subtype layers is a bijection. -/
def subsetCoordinatesEquiv (s t : Finset K) (hst : s ⊆ t) :
    {i : t // i.val ∈ s} ≃ s where
  toFun i := ⟨i.val.val, i.property⟩
  invFun i := ⟨⟨i.val, hst i.property⟩, i.property⟩
  left_inv i := Subtype.ext (Subtype.ext rfl)
  right_inv i := Subtype.ext rfl

/-- Extend a small prescribed set to an information set and count its
unprescribed labels.  The desired multiplicity is a conclusion. -/
theorem prescribed_card (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed : Finset K) (hfixed : fixed.card ≤ k) (target : K → V) :
    Fintype.card (Fiber C fixed target) =
      Fintype.card V ^ (k - fixed.card) := by
  obtain ⟨info, hsub, _, hcard⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ fixed) hfixed
      (show k ≤ (Finset.univ : Finset K).card by simpa using hk)
  have hinfo : Function.Bijective (subgroupRestriction C (fun i => i ∈ info)) :=
    hMDS (fun i => i ∈ info) (by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcard)
  let e : C ≃ (info → V) := Equiv.ofBijective _ hinfo
  have hconstraint (c : C) :
      (∀ i ∈ fixed, c.val i = target i) ↔
        ∀ i : info, i.val ∈ fixed → e c i = target i.val := by
    constructor
    · intro hc i hi
      exact hc i.val hi
    · intro hc i hi
      exact hc ⟨i, hsub hi⟩ hi
  have hsmall : Fintype.card {i : info // i.val ∈ fixed} = fixed.card := by
    rw [Fintype.card_congr (subsetCoordinatesEquiv fixed info hsub)]
    simp
  calc
    Fintype.card (Fiber C fixed target) =
        Fintype.card {c : C // ∀ i : info, i.val ∈ fixed → e c i = target i.val} :=
      Fintype.card_congr (Equiv.subtypeEquivRight hconstraint)
    _ = Fintype.card V ^ Fintype.card {i : info // ¬ i.val ∈ fixed} :=
      AESMixing.bijective_prescribed_card e (fun i : info => i.val ∈ fixed)
        (fun i => target i.val)
    _ = Fintype.card V ^ (k - fixed.card) := by
      rw [Fintype.card_subtype_compl, hsmall]
      simp only [Fintype.card_coe, hcard]

/-- Merge a fixed label and a new observation into one full coordinate label. -/
def mergedTarget (fixed observed : Finset K) (target : K → V)
    (u : observed → V) (i : K) : V :=
  if hi : i ∈ fixed then target i else
    if hj : i ∈ observed then u ⟨i, hj⟩ else 0

theorem mergedTarget_fixed (fixed observed : Finset K) (target : K → V)
    (u : observed → V) (i : K) (hi : i ∈ fixed) :
    mergedTarget fixed observed target u i = target i := by
  simp [mergedTarget, hi]

theorem mergedTarget_observed (fixed observed : Finset K)
    (hd : Disjoint fixed observed) (target : K → V)
    (u : observed → V) (i : observed) :
    mergedTarget fixed observed target u i.val = u i := by
  have hi : i.val ∉ fixed := fun h => (Finset.disjoint_left.mp hd) h i.property
  simp [mergedTarget, hi, i.property]

/-- The literal observation fiber is the same code with the union of fixed
and observed coordinates prescribed. -/
def projectionFiberEquiv (C : AddSubgroup (K → V))
    (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (target : K → V) (u : observed → V) :
    {x : Fiber C fixed target // observe C fixed observed target x = u} ≃
      Fiber C (fixed ∪ observed) (mergedTarget fixed observed target u) where
  toFun x := ⟨x.val.val, by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [mergedTarget_fixed fixed observed target u i hi]
      exact x.val.property i hi
    · rw [mergedTarget_observed fixed observed hd target u ⟨i, hi⟩]
      exact congrFun x.property ⟨i, hi⟩⟩
  invFun x := ⟨⟨x.val, by
    intro i hi
    simpa only [mergedTarget_fixed fixed observed target u i hi] using
      x.property i (Finset.mem_union_left observed hi)⟩, by
    funext i
    exact (x.property i.val (Finset.mem_union_right fixed i.property)).trans
      (mergedTarget_observed fixed observed hd target u i)⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

/-- All observation tuples have their exact MDS multiplicity whenever the
fixed and observed sets together fit in an information set. -/
theorem projection_fiber_card (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (hle : fixed.card + observed.card ≤ k) (target : K → V) (u : observed → V) :
    Fintype.card {x : Fiber C fixed target // observe C fixed observed target x = u} =
      Fintype.card V ^ (k - (fixed.card + observed.card)) := by
  rw [Fintype.card_congr (projectionFiberEquiv C fixed observed hd target u),
    prescribed_card C k hk hMDS (fixed ∪ observed)
      (by simpa only [Finset.card_union_of_disjoint hd] using hle),
    Finset.card_union_of_disjoint hd]

/-- With exactly the remaining dimension observed, physical-coordinate
restriction on the affine fiber is bijective. -/
theorem projection_bijective (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (heq : fixed.card + observed.card = k) (target : K → V) :
    Function.Bijective (observe C fixed observed target) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply (hMDS (fun i => i ∈ fixed ∪ observed) (by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe,
        Finset.card_union_of_disjoint hd] using heq)).injective
    funext i
    rcases Finset.mem_union.mp i.property with hi | hi
    · exact (x.property i.val hi).trans (y.property i.val hi).symm
    · exact congrFun hxy ⟨i.val, hi⟩
  · rw [prescribed_card C k hk hMDS fixed (by omega) target,
      Fintype.card_fun, Fintype.card_coe]
    congr 1
    omega

def informationEquiv (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (heq : fixed.card + observed.card = k) (target : K → V) :
    Fiber C fixed target ≃ (observed → V) :=
  Equiv.ofBijective _ (projection_bijective C k hk hMDS fixed observed hd heq target)

/-- The high-dimensional collision branch, with the exact `q` factor
derived from MDS rather than assumed as a uniformity premise. -/
theorem collision_sum_high (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (hle : observed.card ≤ k - fixed.card) (hfixed : fixed.card ≤ k)
    (target : K → V) (g : K → V → ℝ) (h : ℝ)
    (hg0 : ∀ i ∈ observed, ∀ x, 0 ≤ g i x)
    (hgsum : ∀ i ∈ observed, (∑ x, g i x) ≤ h) :
    (∑ c : Fiber C fixed target, ∏ i ∈ observed, g i (c.val.val i)) ≤
      (Fintype.card V : ℝ) ^ (k - fixed.card - observed.card) * h ^ observed.card := by
  have hcount := projection_fiber_card C k hk hMDS fixed observed hd (by omega) target
  have hb := FiberCollision.constant_fiber_projection_sum_bound
    (observe C fixed observed target)
    (Fintype.card V ^ (k - (fixed.card + observed.card))) hcount
    (fun i : observed => g i.val) h (fun i => hg0 i.val i.property)
    (fun i => hgsum i.val i.property)
  calc
    (∑ c : Fiber C fixed target, ∏ i ∈ observed, g i (c.val.val i)) =
        ∑ c : Fiber C fixed target, ∏ i : observed, g i.val (c.val.val i.val) := by
      apply Finset.sum_congr rfl
      intro c _
      exact (Finset.prod_coe_sort observed (fun i : K => g i (c.val.val i))).symm
    _ ≤ _ := by
      simpa only [observe, Nat.cast_pow, Fintype.card_coe, Nat.sub_sub] using hb

/-- The information-set branch with an explicit nonnegative pointwise cap.
The public paper wrapper below derives this sign condition from the local
hypotheses whenever an observed coordinate exists. -/
theorem collision_sum_low_of_nonneg (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (hle : k - fixed.card ≤ observed.card) (hfixed : fixed.card ≤ k)
    (target : K → V) (g : K → V → ℝ) (h delta : ℝ) (hdelta : 0 ≤ delta)
    (hg0 : ∀ i ∈ observed, ∀ x, 0 ≤ g i x)
    (hgsum : ∀ i ∈ observed, (∑ x, g i x) ≤ h)
    (hgcap : ∀ i ∈ observed, ∀ x, g i x ≤ delta) :
    (∑ c : Fiber C fixed target, ∏ i ∈ observed, g i (c.val.val i)) ≤
      delta ^ (observed.card - (k - fixed.card)) * h ^ (k - fixed.card) := by
  obtain ⟨info, hsub, hcard⟩ := Finset.exists_subset_card_eq hle
  have hdisj : Disjoint fixed info := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.disjoint_left.mp hd) hi (hsub hj)
  have hsize : fixed.card + info.card = k := by omega
  let e := informationEquiv C k hk hMDS fixed info hdisj hsize target
  let rest := fun c : Fiber C fixed target => fun i : ↥(observed \ info) => c.val.val i.val
  have hprod (c : Fiber C fixed target) :
      (∏ i ∈ observed, g i (c.val.val i)) =
        (∏ i : info, g i.val (e c i)) *
          (∏ i : ↥(observed \ info), g i.val (rest c i)) := by
    change _ = (∏ i : info, g i.val (c.val.val i.val)) *
      (∏ i : ↥(observed \ info), g i.val (c.val.val i.val))
    rw [Finset.prod_coe_sort info (fun i : K => g i (c.val.val i)),
      Finset.prod_coe_sort (observed \ info) (fun i : K => g i (c.val.val i)), mul_comm]
    exact (Finset.prod_sdiff hsub).symm
  have hb := FiberCollision.information_set_sum_bound e rest
    (fun i : info => g i.val) (fun i : ↥(observed \ info) => g i.val) h delta hdelta
    (fun i => hg0 i.val (hsub i.property))
    (fun i => hg0 i.val (Finset.mem_sdiff.mp i.property).1)
    (fun i => hgsum i.val (hsub i.property))
    (fun i => hgcap i.val (Finset.mem_sdiff.mp i.property).1)
  calc
    (∑ c : Fiber C fixed target, ∏ i ∈ observed, g i (c.val.val i)) =
        ∑ c : Fiber C fixed target,
          (∏ i : info, g i.val (e c i)) *
            (∏ i : ↥(observed \ info), g i.val (rest c i)) :=
      Finset.sum_congr rfl (fun c _ => hprod c)
    _ ≤ h ^ Fintype.card info * delta ^ Fintype.card ↥(observed \ info) := hb
    _ = delta ^ (observed.card - (k - fixed.card)) * h ^ (k - fixed.card) := by
      rw [Fintype.card_coe, Fintype.card_coe, Finset.card_sdiff_of_subset hsub, hcard]
      exact mul_comm _ _

/-- The exact two-branch collision cost in equation `eq:fiber-sum`. -/
def collisionBound (q : ℕ) (n a : ℕ) (h delta : ℝ) : ℝ :=
  if a ≤ n then delta ^ (n - a) * h ^ a else (q : ℝ) ^ (a - n) * h ^ n

/-- Paper Lemma 7 (`lem:fiber-sum`) for arbitrary finite coordinate sets,
arbitrary additive MDS codes, and arbitrary affine prescribed-coordinate
fibers.  The desired information-set and multiplicity facts are conclusions
of the preceding MDS lemmas, not analytic assumptions. -/
theorem paper_affine_mds_fiber_collision_bound (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (hfixed : fixed.card ≤ k) (target : K → V) (g : K → V → ℝ) (h delta : ℝ)
    (hg0 : ∀ i ∈ observed, ∀ x, 0 ≤ g i x)
    (hgsum : ∀ i ∈ observed, (∑ x, g i x) ≤ h)
    (hgcap : ∀ i ∈ observed, ∀ x, g i x ≤ delta) :
    (∑ c : Fiber C fixed target, ∏ i ∈ observed, g i (c.val.val i)) ≤
      collisionBound (Fintype.card V) observed.card (k - fixed.card) h delta := by
  by_cases hlow : k - fixed.card ≤ observed.card
  · rw [collisionBound, if_pos hlow]
    by_cases hobs : observed.Nonempty
    · obtain ⟨i, hi⟩ := hobs
      have hdelta : 0 ≤ delta := (hg0 i hi 0).trans (hgcap i hi 0)
      exact collision_sum_low_of_nonneg C k hk hMDS fixed observed hd hlow hfixed
        target g h delta hdelta hg0 hgsum hgcap
    · have hempty : observed = ∅ := Finset.not_nonempty_iff_eq_empty.mp hobs
      have ha : k - fixed.card = 0 := by
        simp only [hempty, Finset.card_empty] at hlow
        omega
      have hcard : Fintype.card (Fiber C fixed target) = 1 := by
        rw [prescribed_card C k hk hMDS fixed hfixed target, ha, pow_zero]
      simpa only [hempty, Finset.prod_empty, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, hcard, Nat.cast_one, mul_one, Finset.card_empty, ha,
        Nat.sub_self, pow_zero] using (le_rfl : (1 : ℝ) ≤ 1)
  · rw [collisionBound, if_neg hlow]
    exact collision_sum_high C k hk hMDS fixed observed hd (by omega) hfixed
      target g h hg0 hgsum

end AES8.PaperMDSFiber
