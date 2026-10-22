/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.PaperMDSFiberAffine
import AES8.Math.FiberIncidence

/-!
# Physical-coordinate inputs for normalized MDS overlap

An outside label is the actual coordinate restriction of a point in an
affine translate of a larger MDS graph. Information parametrizations,
outside-image fiber counts, and local collision sums are consequences of
MDS. They are not additional uniformity or operator-bound premises.

This file supplies the physical bridge to `PaperInformationOverlap`.
No AES numerical instantiation, manuscript edits, or attacks.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperMDSOverlap

open PaperMDSGram PaperMDSFiber FiberIncidence

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The actual points of a translated graph, before any coordinate is fixed. -/
abbrev AffineCode (C : AddSubgroup (K → V)) (offset : K → V) :=
  {x : K → V // x - offset ∈ C}

/-- Translation identifies the affine graph with its additive code. -/
def affineCodeEquiv (C : AddSubgroup (K → V)) (offset : K → V) :
    AffineCode C offset ≃ C where
  toFun x := ⟨x.val - offset, x.property⟩
  invFun c := ⟨c.val + offset, by simpa only [add_sub_cancel_right] using c.property⟩
  left_inv x := Subtype.ext (sub_add_cancel _ _)
  right_inv c := Subtype.ext (add_sub_cancel_right _ _)

/-- Restriction to any injective family of `k` physical coordinates. -/
theorem restriction_bijective_of_card {I : Type*} [Fintype I]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (f : I ↪ K) (hcard : Fintype.card I = k) :
    Function.Bijective (fun c : C => fun i : I => c.val (f i)) := by
  let e : I ≃ Set.range (f : I → K) := Equiv.ofInjective f f.injective
  have hr := hMDS (fun x => x ∈ Set.range (f : I → K)) (by
    calc
      Nat.card (Set.range (f : I → K)) = Nat.card I := Nat.card_congr e.symm
      _ = k := by simpa only [Nat.card_eq_fintype_card] using hcard)
  constructor
  · intro c d h
    apply hr.injective
    funext x
    obtain ⟨i, rfl⟩ := e.surjective x
    exact congrFun h i
  · intro u
    obtain ⟨c, hc⟩ := hr.surjective (fun x => u (e.symm x))
    refine ⟨c, ?_⟩
    funext i
    have hi := congrFun hc (e i)
    change c.val (f i) = u (e.symm (e i)) at hi
    simpa using hi

/-- The same information coordinates parametrise every affine translate. -/
theorem affine_restriction_bijective {I : Type*} [Fintype I]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : K → V) (f : I ↪ K) (hcard : Fintype.card I = k) :
    Function.Bijective (fun c : AffineCode C offset => fun i : I => c.val (f i)) := by
  have hr := restriction_bijective_of_card C k hMDS f hcard
  constructor
  · intro c d h
    have hc : affineCodeEquiv C offset c = affineCodeEquiv C offset d := by
      apply hr.injective
      funext i
      change c.val (f i) - offset (f i) = d.val (f i) - offset (f i)
      have hi := congrFun h i
      change c.val (f i) = d.val (f i) at hi
      exact congrArg (fun z => z - offset (f i)) hi
    exact (affineCodeEquiv C offset).injective hc
  · intro u
    obtain ⟨c, hc⟩ := hr.surjective (fun i => u i - offset (f i))
    refine ⟨(affineCodeEquiv C offset).symm c, ?_⟩
    funext i
    change c.val (f i) + offset (f i) = u i
    exact eq_sub_iff_add_eq.mp (congrFun hc i)

def affineInformationEquiv {I : Type*} [Fintype I]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : K → V) (f : I ↪ K) (hcard : Fintype.card I = k) :
    AffineCode C offset ≃ (I → V) :=
  Equiv.ofBijective _ (affine_restriction_bijective C k hMDS offset f hcard)

/-- The physical outside-coordinate map. -/
def outsideMap (C : AddSubgroup (K → V)) (offset : K → V) (outside : Finset K)
    (x : AffineCode C offset) : outside → V := fun i => x.val i.val

/-- Extend a coordinate label only to state the literal prescribed fiber. -/
def outsideTarget (outside : Finset K) (u : outside → V) (i : K) : V :=
  if hi : i ∈ outside then u ⟨i, hi⟩ else 0

theorem outsideTarget_apply (outside : Finset K) (u : outside → V) (i : outside) :
    outsideTarget outside u i.val = u i := by
  simp [outsideTarget, i.property]

/-- Fixing the outside label is literally a prescribed-coordinate affine fiber. -/
def outsideFiberEquiv (C : AddSubgroup (K → V)) (offset : K → V)
    (outside : Finset K) (u : outside → V) :
    {x : AffineCode C offset // outsideMap C offset outside x = u} ≃
      AffineFiber C offset outside (outsideTarget outside u) where
  toFun x := ⟨x.val.val, ⟨x.val.property, by
    intro i hi
    exact (congrFun x.property ⟨i, hi⟩).trans
      (outsideTarget_apply outside u ⟨i, hi⟩).symm⟩⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, by
    funext i
    exact (x.property.2 i.val i.property).trans (outsideTarget_apply outside u i)⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

/-- Exact fiber cardinalities when the outside coordinates fit in an information set. -/
theorem outside_fiber_card_small (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k) (offset : K → V)
    (outside : Finset K) (hout : outside.card ≤ k) (u : outside → V) :
    Fintype.card {x : AffineCode C offset // outsideMap C offset outside x = u} =
      Fintype.card V ^ (k - outside.card) := by
  rw [Fintype.card_congr (outsideFiberEquiv C offset outside u)]
  exact affine_prescribed_card C k hk hMDS offset outside hout (outsideTarget outside u)

/-- Regroup a raw outside sum into its literal physical affine fiber. -/
theorem raw_outside_sum (C : AddSubgroup (K → V)) (offset : K → V)
    (outside : Finset K) (u : outside → V) (w : (K → V) → ℝ) :
    rawFiberSum (outsideMap C offset outside) (fun x => w x.val) u =
      ∑ x : AffineFiber C offset outside (outsideTarget outside u), w x.val := by
  have hs : rawFiberSum (outsideMap C offset outside) (fun x => w x.val) u =
      ∑ x : {x : AffineCode C offset // outsideMap C offset outside x = u},
        w x.val.val := by
    unfold rawFiberSum
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hs]
  exact (outsideFiberEquiv C offset outside u).sum_comp (fun x => w x.val)

/-- Lemma 7 provides exactly the local raw collision-sum premise required
by the normalized overlap theorem. The outside size is a physical count. -/
theorem raw_outside_collision_bound_small
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hMDS : IsMDS C k) (offset : K → V) (outside observed : Finset K)
    (hd : Disjoint outside observed) (hout : outside.card ≤ k)
    (u : outside → V) (g : K → V → ℝ) (h delta : ℝ)
    (hg0 : ∀ i ∈ observed, ∀ x, 0 ≤ g i x)
    (hgsum : ∀ i ∈ observed, (∑ x, g i x) ≤ h)
    (hgcap : ∀ i ∈ observed, ∀ x, g i x ≤ delta) :
    rawFiberSum (outsideMap C offset outside)
      (fun x => ∏ i ∈ observed, g i (x.val i)) u ≤
      collisionBound (Fintype.card V) observed.card (k - outside.card) h delta := by
  rw [raw_outside_sum C offset outside u (fun z : K → V => ∏ i ∈ observed, g i (z i))]
  exact paper_affine_mds_collision_bound C k hk hMDS offset outside observed hd hout
    (outsideTarget outside u) g h delta hg0 hgsum hgcap

/-- Reparametrizing actual graph points by information labels preserves every raw sum. -/
theorem rawFiberSum_equiv {X Y O : Type*} [Fintype X] [Fintype Y] [Fintype O]
    [DecidableEq O] (e : X ≃ Y) (proj : Y → O) (w : Y → ℝ) (u : O) :
    rawFiberSum (fun x => proj (e x)) (fun x => w (e x)) u = rawFiberSum proj w u := by
  exact e.sum_comp (fun y => if proj y = u then w y else 0)

/-- Only labels actually occurring on the graph belong to the outside space. -/
abbrev OutsideLabel (C : AddSubgroup (K → V)) (offset : K → V)
    (outside : Finset K) := Set.range (outsideMap C offset outside)

def outsideProjection (C : AddSubgroup (K → V)) (offset : K → V)
    (outside : Finset K) (x : AffineCode C offset) : OutsideLabel C offset outside :=
  ⟨outsideMap C offset outside x, ⟨x, rfl⟩⟩

theorem outsideProjection_surjective (C : AddSubgroup (K → V)) (offset : K → V)
    (outside : Finset K) : Function.Surjective (outsideProjection C offset outside) := by
  intro u
  obtain ⟨x, hx⟩ := u.property
  exact ⟨x, Subtype.ext hx⟩

/-- The image-valued outside map fixes exactly the same physical coordinates. -/
def admissibleFiberEquiv (C : AddSubgroup (K → V)) (offset : K → V)
    (outside : Finset K) (u : OutsideLabel C offset outside) :
    {x : AffineCode C offset // outsideProjection C offset outside x = u} ≃
      {x : AffineCode C offset // outsideMap C offset outside x = u.val} where
  toFun x := ⟨x.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨x.val, Subtype.ext x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

/-- A physical outside set containing an information set determines the graph point. -/
theorem outsideMap_injective_large (C : AddSubgroup (K → V)) (k : ℕ)
    (hMDS : IsMDS C k) (offset : K → V) (outside : Finset K)
    (hout : k ≤ outside.card) : Function.Injective (outsideMap C offset outside) := by
  obtain ⟨info, hsub, hcard⟩ := Finset.exists_subset_card_eq hout
  let f : info ↪ K := ⟨Subtype.val, Subtype.val_injective⟩
  have hi := (affine_restriction_bijective C k hMDS offset f (by simpa using hcard)).injective
  intro x y hxy
  apply hi
  funext i
  exact congrFun hxy ⟨i.val, hsub i.property⟩

theorem outsideProjection_injective_large (C : AddSubgroup (K → V)) (k : ℕ)
    (hMDS : IsMDS C k) (offset : K → V) (outside : Finset K)
    (hout : k ≤ outside.card) :
    Function.Injective (outsideProjection C offset outside) := by
  intro x y hxy
  exact outsideMap_injective_large C k hMDS offset outside hout (congrArg Subtype.val hxy)

/-- Once the outside count reaches the dimension, every admissible fiber is a singleton. -/
def largeOutsideFiberEquiv (C : AddSubgroup (K → V)) (k : ℕ)
    (hMDS : IsMDS C k) (offset : K → V) (outside : Finset K)
    (hout : k ≤ outside.card) (u : OutsideLabel C offset outside) :
    {x : AffineCode C offset // outsideProjection C offset outside x = u} ≃ Unit := by
  let x₀ := Classical.choose (outsideProjection_surjective C offset outside u)
  have hx₀ := Classical.choose_spec (outsideProjection_surjective C offset outside u)
  refine
    { toFun := fun _ => ()
      invFun := fun _ => ⟨x₀, hx₀⟩
      left_inv := ?_
      right_inv := fun x => by cases x; rfl }
  intro x
  apply Subtype.ext
  exact outsideProjection_injective_large C k hMDS offset outside hout
    (hx₀.trans x.property.symm)

/-- The outside rank is `min k |outside|`, including saturated outside sets.
The normalizer is derived over the admissible image, with no rank premise. -/
theorem outside_fiber_card (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k) (offset : K → V)
    (outside : Finset K) (u : OutsideLabel C offset outside) :
    Fintype.card {x : AffineCode C offset // outsideProjection C offset outside x = u} =
      Fintype.card V ^ (k - min k outside.card) := by
  by_cases hout : outside.card ≤ k
  · rw [Nat.min_eq_right hout, Fintype.card_congr (admissibleFiberEquiv C offset outside u)]
    exact outside_fiber_card_small C k hk hMDS offset outside hout u.val
  · rw [Nat.min_eq_left (by omega), Nat.sub_self, pow_zero,
      Fintype.card_congr (largeOutsideFiberEquiv C k hMDS offset outside (by omega) u)]
    simp

theorem outside_normalizer_pos (k : ℕ) (outside : Finset K) :
    0 < Fintype.card V ^ (k - min k outside.card) := by
  exact pow_pos (Fintype.card_pos_iff.mpr ⟨(0 : V)⟩) _

theorem raw_admissible_sum_eq (C : AddSubgroup (K → V)) (offset : K → V)
    (outside : Finset K) (u : OutsideLabel C offset outside)
    (w : AffineCode C offset → ℝ) :
    rawFiberSum (outsideProjection C offset outside) w u =
      rawFiberSum (outsideMap C offset outside) w u.val := by
  rcases u with ⟨u, hu⟩
  simp only [rawFiberSum, outsideProjection, Subtype.mk.injEq]

/-- All local collision sums on actual admissible outside fibers, at the
paper's exact remaining dimension, follow from Lemma 7 and MDS injectivity. -/
theorem raw_outside_collision_bound
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hMDS : IsMDS C k) (offset : K → V) (outside observed : Finset K)
    (hd : Disjoint outside observed) (u : OutsideLabel C offset outside)
    (g : K → V → ℝ) (h delta : ℝ)
    (hg0 : ∀ i ∈ observed, ∀ x, 0 ≤ g i x)
    (hgsum : ∀ i ∈ observed, (∑ x, g i x) ≤ h)
    (hgcap : ∀ i ∈ observed, ∀ x, g i x ≤ delta) :
    rawFiberSum (outsideProjection C offset outside)
      (fun x => ∏ i ∈ observed, g i (x.val i)) u ≤
      collisionBound (Fintype.card V) observed.card (k - min k outside.card) h delta := by
  by_cases hout : outside.card ≤ k
  · rw [Nat.min_eq_right hout, raw_admissible_sum_eq]
    exact raw_outside_collision_bound_small C k hk hMDS offset outside observed hd hout
      u.val g h delta hg0 hgsum hgcap
  · have hi := outsideProjection_injective_large C k hMDS offset outside (by omega)
    obtain ⟨x₀, hx₀⟩ := outsideProjection_surjective C offset outside u
    have heq : rawFiberSum (outsideProjection C offset outside)
        (fun x => ∏ i ∈ observed, g i (x.val i)) u =
        ∏ i ∈ observed, g i (x₀.val i) := by
      unfold rawFiberSum
      rw [Finset.sum_eq_single x₀]
      · simp [hx₀]
      · intro x _ hx
        have hxne : outsideProjection C offset outside x ≠ u := by
          intro he
          exact hx (hi (he.trans hx₀.symm))
        simp [hxne]
      · simp
    rw [heq, Nat.min_eq_left (by omega), Nat.sub_self, collisionBound, if_pos (Nat.zero_le _)]
    simp only [Nat.sub_zero, pow_zero, mul_one]
    calc
      (∏ i ∈ observed, g i (x₀.val i)) ≤ ∏ _i ∈ observed, delta :=
        Finset.prod_le_prod (fun i hi => hg0 i hi _) (fun i hi => hgcap i hi _)
      _ = delta ^ observed.card := by simp

/-- The collision premise transported to any information parametrization of
the actual affine graph. This is the normalized-overlap theorem's interface. -/
theorem information_raw_collision_bound {X : Type*} [Fintype X]
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hMDS : IsMDS C k) (offset : K → V) (e : X ≃ AffineCode C offset)
    (outside observed : Finset K) (hd : Disjoint outside observed)
    (u : OutsideLabel C offset outside) (g : K → V → ℝ) (h delta : ℝ)
    (hg0 : ∀ i ∈ observed, ∀ x, 0 ≤ g i x)
    (hgsum : ∀ i ∈ observed, (∑ x, g i x) ≤ h)
    (hgcap : ∀ i ∈ observed, ∀ x, g i x ≤ delta) :
    rawFiberSum (fun x => outsideProjection C offset outside (e x))
      (fun x => ∏ i ∈ observed, g i ((e x).val i)) u ≤
      collisionBound (Fintype.card V) observed.card (k - min k outside.card) h delta := by
  rw [rawFiberSum_equiv e (outsideProjection C offset outside)
    (fun z : AffineCode C offset => ∏ i ∈ observed, g i (z.val i)) u]
  exact raw_outside_collision_bound C k hk hMDS offset outside observed hd u g h delta
    hg0 hgsum hgcap

/-- The equal-fiber count is preserved by the derived information coordinates. -/
theorem information_outside_fiber_card {X : Type*} [Fintype X]
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hMDS : IsMDS C k) (offset : K → V) (e : X ≃ AffineCode C offset)
    (outside : Finset K) (u : OutsideLabel C offset outside) :
    Fintype.card {x : X // outsideProjection C offset outside (e x) = u} =
      Fintype.card V ^ (k - min k outside.card) := by
  let ef : {x : X // outsideProjection C offset outside (e x) = u} ≃
      {x : AffineCode C offset // outsideProjection C offset outside x = u} :=
    { toFun := fun x => ⟨e x.val, x.property⟩
      invFun := fun x => ⟨e.symm x.val, by simpa using x.property⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val) }
  rw [Fintype.card_congr ef]
  exact outside_fiber_card C k hk hMDS offset outside u

/-- A local family on an injected physical set, extended by zero elsewhere. -/
def extendLocal {J : Type*} [Fintype J] (f : J ↪ K) (g : J → V → ℝ)
    (i : K) (x : V) : ℝ := ∑ j, if f j = i then g j x else 0

@[simp] theorem extendLocal_apply {J : Type*} [Fintype J] [DecidableEq J]
    (f : J ↪ K) (g : J → V → ℝ) (j : J) (x : V) :
    extendLocal f g (f j) x = g j x := by
  simp [extendLocal, f.injective.eq_iff]

/-- Coordinate embeddings turn the physical collision theorem into the
literal product over the observed coordinate type. No multiplicity premise
is added when passing from a physical set to its enumeration. -/
theorem information_raw_collision_bound_embedding
    {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hMDS : IsMDS C k) (offset : K → V) (e : X ≃ AffineCode C offset)
    (outside : Finset K) (obs : J ↪ K)
    (hd : Disjoint outside (Finset.univ.map obs))
    (u : OutsideLabel C offset outside) (g : J → V → ℝ) (h delta : ℝ)
    (hg0 : ∀ j x, 0 ≤ g j x) (hgsum : ∀ j, (∑ x, g j x) ≤ h)
    (hgcap : ∀ j x, g j x ≤ delta) :
    rawFiberSum (fun x => outsideProjection C offset outside (e x))
      (fun x => ∏ j, g j ((e x).val (obs j))) u ≤
      collisionBound (Fintype.card V) (Fintype.card J) (k - min k outside.card) h delta := by
  have hmem (i : K) (hi : i ∈ Finset.univ.map obs) : ∃ j, obs j = i := by
    simpa only [Finset.mem_map, Finset.mem_univ, true_and] using hi
  have hb := information_raw_collision_bound C k hk hMDS offset e outside
    (Finset.univ.map obs) hd u (extendLocal obs g) h delta
    (by
      intro i hi x
      obtain ⟨j, rfl⟩ := hmem i hi
      simpa only [extendLocal_apply] using hg0 j x)
    (by
      intro i hi
      obtain ⟨j, rfl⟩ := hmem i hi
      simpa only [extendLocal_apply] using hgsum j)
    (by
      intro i hi x
      obtain ⟨j, rfl⟩ := hmem i hi
      simpa only [extendLocal_apply] using hgcap j x)
  simpa only [Finset.prod_map, Finset.card_map, Finset.card_univ, extendLocal_apply] using hb

/-- Two information-coordinate blocks retain their physical interpretation. -/
def pairInformationEquiv {I J : Type*} [Fintype I] [Fintype J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : K → V) (f : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k) :
    AffineCode C offset ≃ ((I → V) × (J → V)) :=
  (affineInformationEquiv C k hMDS offset f (by simpa using hcard)).trans
    (Equiv.sumArrowEquivProdArrow I J V)

@[simp] theorem pairInformationEquiv_left {I J : Type*} [Fintype I] [Fintype J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : K → V) (f : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k) (x : AffineCode C offset) (i : I) :
    (pairInformationEquiv C k hMDS offset f hcard x).1 i = x.val (f (Sum.inl i)) := rfl

@[simp] theorem pairInformationEquiv_right {I J : Type*} [Fintype I] [Fintype J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : K → V) (f : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k) (x : AffineCode C offset) (j : J) :
    (pairInformationEquiv C k hMDS offset f hcard x).2 j = x.val (f (Sum.inr j)) := rfl

@[simp] theorem pairInformationEquiv_symm_left {I J : Type*} [Fintype I] [Fintype J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : K → V) (f : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k)
    (u : (I → V) × (J → V)) (i : I) :
    ((pairInformationEquiv C k hMDS offset f hcard).symm u).val (f (Sum.inl i)) = u.1 i := by
  exact congrFun (congrArg Prod.fst
    ((pairInformationEquiv C k hMDS offset f hcard).apply_symm_apply u)) i

@[simp] theorem pairInformationEquiv_symm_right {I J : Type*} [Fintype I] [Fintype J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : K → V) (f : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k)
    (u : (I → V) × (J → V)) (j : J) :
    ((pairInformationEquiv C k hMDS offset f hcard).symm u).val (f (Sum.inr j)) = u.2 j := by
  exact congrFun (congrArg Prod.snd
    ((pairInformationEquiv C k hMDS offset f hcard).apply_symm_apply u)) j

/-- The physical outside map in the derived two-block information labels. -/
def pairOutside {I J : Type*} [Fintype I] [Fintype J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : K → V) (info : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k) (outside : Finset K)
    (u : (I → V) × (J → V)) : OutsideLabel C offset outside :=
  outsideProjection C offset outside
    ((pairInformationEquiv C k hMDS offset info hcard).symm u)

/-- The remaining physical coordinates as functions of the retained information labels. -/
def pairRemaining {I J O : Type*} [Fintype I] [Fintype J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (offset : K → V) (info : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k) (obs : O ↪ K)
    (u : (I → V) × (J → V)) (o : O) : V :=
  ((pairInformationEquiv C k hMDS offset info hcard).symm u).val (obs o)

/-- Exact positive normalizer counts in two-block information coordinates. -/
theorem pairOutside_fiber_card {I J : Type*} [Fintype I] [Fintype J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hMDS : IsMDS C k) (offset : K → V) (info : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k) (outside : Finset K)
    (u : OutsideLabel C offset outside) :
    Fintype.card {x : (I → V) × (J → V) //
      pairOutside C k hMDS offset info hcard outside x = u} =
      Fintype.card V ^ (k - min k outside.card) :=
  information_outside_fiber_card C k hk hMDS offset
    (pairInformationEquiv C k hMDS offset info hcard).symm outside u

/-- The normalized information lift is an actual isometry, with the
normalizer proved from the larger MDS graph. -/
theorem pairOutside_normalizedLift_l2 {I J : Type*} [Fintype I] [Fintype J]
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hMDS : IsMDS C k) (offset : K → V) (info : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k) (outside : Finset K)
    (f : OutsideLabel C offset outside → ℝ) :
    AESMixing.l2 (normalizedLift (pairOutside C k hMDS offset info hcard outside)
      (Fintype.card V ^ (k - min k outside.card)) f) = AESMixing.l2 f := by
  exact normalizedLift_l2 _ _ (outside_normalizer_pos (V := V) k outside)
    (pairOutside_fiber_card C k hk hMDS offset info hcard outside) f

/-- The local collision premise in exactly the two-block information labels
used by the overlap factorization. All code and outside counts are derived. -/
theorem pair_raw_collision_bound {I J O : Type*}
    [Fintype I] [Fintype J] [Fintype O] [DecidableEq O]
    (C : AddSubgroup (K → V)) (k : ℕ) (hk : k ≤ Fintype.card K)
    (hMDS : IsMDS C k) (offset : K → V) (info : I ⊕ J ↪ K)
    (hcard : Fintype.card I + Fintype.card J = k)
    (outside : Finset K) (obs : O ↪ K)
    (hd : Disjoint outside (Finset.univ.map obs))
    (u : OutsideLabel C offset outside) (g : O → V → ℝ) (h delta : ℝ)
    (hg0 : ∀ o x, 0 ≤ g o x) (hgsum : ∀ o, (∑ x, g o x) ≤ h)
    (hgcap : ∀ o x, g o x ≤ delta) :
    rawFiberSum (pairOutside C k hMDS offset info hcard outside)
      (fun x => ∏ o, g o (pairRemaining C k hMDS offset info hcard obs x o)) u ≤
      collisionBound (Fintype.card V) (Fintype.card O) (k - min k outside.card) h delta := by
  exact information_raw_collision_bound_embedding C k hk hMDS offset
    (pairInformationEquiv C k hMDS offset info hcard).symm outside obs hd u g h delta
    hg0 hgsum hgcap

/-- Nonnegativity of the exact two-branch collision factor. -/
theorem collisionBound_nonneg (q n a : ℕ) (h delta : ℝ)
    (hh : 0 ≤ h) (hd : 0 ≤ delta) : 0 ≤ collisionBound q n a h delta := by
  unfold collisionBound
  split <;> positivity

end AES8.PaperMDSOverlap
