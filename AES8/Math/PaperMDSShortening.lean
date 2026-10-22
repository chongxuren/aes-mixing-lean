import AES8.Math.PaperThinLinesFibers

/-!
# Literal outside partitions of arbitrary affine MDS shortenings

Retained points are ambient graph words, including coordinates already fixed.
The outside map is literal restriction to a disjoint physical coordinate set,
with its actual image as label space. All cardinalities are derived from MDS.
This supplies the shortening correspondence used by the thin-plane endpoint.
Constructive proof checking only; no attacks or numerical instantiation.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperMDSShortening
open PaperMDSGram PaperMDSFiber PaperThinHolder PaperThinLines

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Physical data for a d-dimensional shortening of a larger MDS graph.
The fields assert only the original MDS property and which coordinates
are fixed, outside, and middle; no analytic or partition bound is a field. -/
structure PhysicalShortening (K V : Type*) [Fintype K] [DecidableEq K]
    [AddCommGroup V] [Fintype V] [DecidableEq V] (d n : ℕ) where
  code : AddSubgroup (K → V)
  dimension : ℕ
  dimension_le : dimension ≤ Fintype.card K
  mds : IsMDS code dimension
  offset : K → V
  fixed : Finset K
  target : K → V
  remaining : fixed.card + d = dimension
  middle : Fin n ↪ K
  middle_unfixed : ∀ a, middle a ∉ fixed
  observed : Finset K
  outside_unfixed : Disjoint fixed observed
  middle_outside : ∀ a, middle a ∉ observed

namespace PhysicalShortening

variable {d n : ℕ} (G : PhysicalShortening K V d n)

abbrev Points := AffineFiber G.code G.offset G.fixed G.target

end PhysicalShortening

def shortWord (C : AddSubgroup (K → V)) (offset : K → V)
    (fixed : Finset K) (target : K → V) (x : AffineFiber C offset fixed target) : K → V :=
  x.val

abbrev ShortOutsideLabels (C : AddSubgroup (K → V)) (offset : K → V)
    (fixed : Finset K) (target : K → V) (observed : Finset K) :=
  OutsideLabels (shortWord C offset fixed target) observed

def shortOutside (C : AddSubgroup (K → V)) (offset : K → V)
    (fixed : Finset K) (target : K → V) (observed : Finset K) :=
  outside (shortWord C offset fixed target) observed

theorem shortOutside_surjective (C : AddSubgroup (K → V)) (offset : K → V)
    (fixed : Finset K) (target : K → V) (observed : Finset K) :
    Function.Surjective (shortOutside C offset fixed target observed) :=
  outside_surjective _ _

/-- Prescribing an admissible outside label means prescribing precisely the
union of the original fixed positions and the physical outside positions. -/
def shortOutsideFiberEquiv (C : AddSubgroup (K → V)) (offset : K → V)
    (fixed observed : Finset K) (hd : Disjoint fixed observed) (target : K → V)
    (o : ShortOutsideLabels C offset fixed target observed) :
    {x : AffineFiber C offset fixed target // shortOutside C offset fixed target observed x = o} ≃
      AffineFiber C offset (fixed ∪ observed) (mergedTarget fixed observed target o.val) where
  toFun x := ⟨x.val.val, x.val.property.1, by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · rw [mergedTarget_fixed fixed observed target o.val i hi]
      exact x.val.property.2 i hi
    · rw [mergedTarget_observed fixed observed hd target o.val ⟨i, hi⟩]
      exact congrFun (congrArg Subtype.val x.property) ⟨i, hi⟩⟩
  invFun x := ⟨⟨x.val, x.property.1, by
    intro i hi
    simpa only [mergedTarget_fixed fixed observed target o.val i hi] using
      x.property.2 i (Finset.mem_union_left observed hi)⟩, by
    apply Subtype.ext
    funext i
    exact (x.property.2 i.val (Finset.mem_union_right fixed i.property)).trans
      (mergedTarget_observed fixed observed hd target o.val i)⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

/-- A saturated outside observation determines the retained ambient word.
An information subset is selected inside the observed coordinates. -/
theorem shortOutside_injective (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k) (offset : K → V)
    (fixed observed : Finset K) (hd : Disjoint fixed observed) (target : K → V)
    (hfixed : fixed.card ≤ k) (hlarge : k - fixed.card ≤ observed.card) :
    Function.Injective (shortOutside C offset fixed target observed) := by
  obtain ⟨info, hsub, hcard⟩ := Finset.exists_subset_card_eq hlarge
  have hdisj : Disjoint fixed info := by
    exact Finset.disjoint_left.mpr (fun i hi hj =>
      Finset.disjoint_left.mp hd hi (hsub hj))
  have hb := (affine_projection_bijective C k hk hC offset fixed info hdisj
    (by omega) target).injective
  intro x y hxy
  apply hb
  funext i
  exact congrFun (congrArg Subtype.val hxy) ⟨i.val, hsub i.property⟩

def shortOutsideSingletonEquiv (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k) (offset : K → V)
    (fixed observed : Finset K) (hd : Disjoint fixed observed) (target : K → V)
    (hfixed : fixed.card ≤ k) (hlarge : k - fixed.card ≤ observed.card)
    (o : ShortOutsideLabels C offset fixed target observed) :
    {x : AffineFiber C offset fixed target // shortOutside C offset fixed target observed x = o} ≃
      Unit := by
  let x₀ := Classical.choose (shortOutside_surjective C offset fixed target observed o)
  have hx₀ := Classical.choose_spec (shortOutside_surjective C offset fixed target observed o)
  refine
    { toFun := fun _ => ()
      invFun := fun _ => ⟨x₀, hx₀⟩
      left_inv := ?_
      right_inv := fun u => by cases u; rfl }
  intro x
  apply Subtype.ext
  exact shortOutside_injective C k hk hC offset fixed observed hd target hfixed hlarge
    (hx₀.trans x.property.symm)

/-- Exact physical outside-fiber dimension, including saturation and the
zero-dimensional case. No rank or multiplicity is an extra hypothesis. -/
theorem shortOutside_fiber_card (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k) (offset : K → V)
    (fixed observed : Finset K) (hd : Disjoint fixed observed) (target : K → V)
    (hfixed : fixed.card ≤ k) (o : ShortOutsideLabels C offset fixed target observed) :
    Fintype.card {x : AffineFiber C offset fixed target //
      shortOutside C offset fixed target observed x = o} =
      Fintype.card V ^ ((k - fixed.card) - min (k - fixed.card) observed.card) := by
  by_cases hsmall : observed.card ≤ k - fixed.card
  · rw [Fintype.card_congr (shortOutsideFiberEquiv C offset fixed observed hd target o),
      affine_prescribed_card C k hk hC offset (fixed ∪ observed)
        (by rw [Finset.card_union_of_disjoint hd]; omega)
        (mergedTarget fixed observed target o.val),
      Finset.card_union_of_disjoint hd, Nat.min_eq_right hsmall]
    congr 1
    omega
  · rw [Fintype.card_congr (shortOutsideSingletonEquiv C k hk hC offset fixed observed hd
      target hfixed (by omega) o), Nat.min_eq_left (by omega), Nat.sub_self, pow_zero]
    simp

/-- Before saturation every outside tuple is admissible, by extending it
to an information set. This is a conclusion about the physical map. -/
theorem shortRestriction_surjective (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k) (offset : K → V)
    (fixed observed : Finset K) (hd : Disjoint fixed observed) (target : K → V)
    (hsmall : fixed.card + observed.card ≤ k) :
    Function.Surjective (outsideRestriction (shortWord C offset fixed target) observed) := by
  intro u
  have hcard := affine_prescribed_card C k hk hC offset (fixed ∪ observed)
    (by simpa only [Finset.card_union_of_disjoint hd] using hsmall)
    (mergedTarget fixed observed target u)
  have hpos : 0 < Fintype.card
      (AffineFiber C offset (fixed ∪ observed) (mergedTarget fixed observed target u)) := by
    rw [hcard]
    exact pow_pos (Fintype.card_pos_iff.mpr ⟨(0 : V)⟩) _
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hpos
  refine ⟨⟨x.val, x.property.1, ?_⟩, ?_⟩
  · intro i hi
    simpa only [mergedTarget_fixed fixed observed target u i hi] using
      x.property.2 i (Finset.mem_union_left observed hi)
  · funext i
    exact (x.property.2 i.val (Finset.mem_union_right fixed i.property)).trans
      (mergedTarget_observed fixed observed hd target u i)

/-- The actual admissible outside space has exactly q^r labels, with
r = min(d, |outside|). Thus both the image size and the fiber size are
derived from MDS, rather than asserted as an outside-rank premise. -/
theorem shortOutside_label_card (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k) (offset : K → V)
    (fixed observed : Finset K) (hd : Disjoint fixed observed) (target : K → V)
    (hfixed : fixed.card ≤ k) :
    Fintype.card (ShortOutsideLabels C offset fixed target observed) =
      Fintype.card V ^ min (k - fixed.card) observed.card := by
  by_cases hsmall : observed.card ≤ k - fixed.card
  · let e : ShortOutsideLabels C offset fixed target observed ≃ (observed → V) :=
      Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, by
        intro u
        obtain ⟨x, hx⟩ := shortRestriction_surjective C k hk hC offset fixed observed hd target
          (by omega) u
        exact ⟨⟨u, ⟨x, hx⟩⟩, rfl⟩⟩
    rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_coe,
      Nat.min_eq_right hsmall]
  · let e := Equiv.ofBijective (shortOutside C offset fixed target observed)
      ⟨shortOutside_injective C k hk hC offset fixed observed hd target hfixed (by omega),
        shortOutside_surjective C offset fixed target observed⟩
    rw [← Fintype.card_congr e, affine_prescribed_card C k hk hC offset fixed hfixed target,
      Nat.min_eq_left (by omega)]

/-- Partial sums are transported to the literal additionally prescribed
affine fiber. In particular previously fixed coordinates stay present. -/
theorem shortOutside_raw_sum (C : AddSubgroup (K → V)) (offset : K → V)
    (fixed observed : Finset K) (hd : Disjoint fixed observed) (target : K → V)
    (o : ShortOutsideLabels C offset fixed target observed) (w : (K → V) → ℝ) :
    (∑ x : AffineFiber C offset fixed target,
      if shortOutside C offset fixed target observed x = o then w x.val else 0) =
    ∑ x : AffineFiber C offset (fixed ∪ observed) (mergedTarget fixed observed target o.val),
      w x.val := by
  have hs : (∑ x : AffineFiber C offset fixed target,
      if shortOutside C offset fixed target observed x = o then w x.val else 0) =
      ∑ x : {x : AffineFiber C offset fixed target //
        shortOutside C offset fixed target observed x = o}, w x.val.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hs]
  exact (shortOutsideFiberEquiv C offset fixed observed hd target o).sum_comp
    (fun x => w x.val)

namespace PhysicalShortening

variable {d n : ℕ} (G : PhysicalShortening K V d n)

def word : G.Points → K → V := shortWord G.code G.offset G.fixed G.target

abbrev Labels := ShortOutsideLabels G.code G.offset G.fixed G.target G.observed

def projection : G.Points → G.Labels :=
  shortOutside G.code G.offset G.fixed G.target G.observed

def outsideRank : ℕ := min d G.observed.card

def fiberDimension : ℕ := d - G.outsideRank

theorem points_card : Fintype.card G.Points = Fintype.card V ^ d := by
  have he : G.dimension - G.fixed.card = d := by have := G.remaining; omega
  simpa only [Points, he] using affine_prescribed_card G.code G.dimension G.dimension_le
    G.mds G.offset G.fixed (by have := G.remaining; omega) G.target

theorem labels_card : Fintype.card G.Labels = Fintype.card V ^ G.outsideRank := by
  have he : G.dimension - G.fixed.card = d := by have := G.remaining; omega
  simpa only [Labels, outsideRank, he] using shortOutside_label_card G.code G.dimension
    G.dimension_le G.mds G.offset G.fixed G.observed G.outside_unfixed G.target
    (by have := G.remaining; omega)

theorem fiber_card (o : G.Labels) :
    Fintype.card {x : G.Points // G.projection x = o} = Fintype.card V ^ G.fiberDimension := by
  have he : G.dimension - G.fixed.card = d := by have := G.remaining; omega
  have hb := shortOutside_fiber_card G.code G.dimension G.dimension_le G.mds G.offset G.fixed
    G.observed G.outside_unfixed G.target (by have := G.remaining; omega) o
  rw [← Nat.card_eq_fintype_card] at hb ⊢
  simpa only [Points, projection, fiberDimension, outsideRank, he] using hb

theorem projection_surjective : Function.Surjective G.projection :=
  shortOutside_surjective G.code G.offset G.fixed G.target G.observed

theorem projection_injective (h : d ≤ G.observed.card) : Function.Injective G.projection := by
  apply shortOutside_injective G.code G.dimension G.dimension_le G.mds G.offset G.fixed
    G.observed G.outside_unfixed G.target
  · have := G.remaining; omega
  · have := G.remaining; omega

theorem projection_empty (h : G.observed = ∅) (o : G.Labels) (x : G.Points) :
    G.projection x = o := by
  apply Subtype.ext
  funext i
  exact False.elim (Finset.notMem_empty i.val (h ▸ i.property))

theorem raw_sum (o : G.Labels) (w : (K → V) → ℝ) :
    (∑ x : G.Points, if G.projection x = o then w x.val else 0) =
      ∑ x : AffineFiber G.code G.offset (G.fixed ∪ G.observed)
        (mergedTarget G.fixed G.observed G.target o.val), w x.val :=
  shortOutside_raw_sum G.code G.offset G.fixed G.observed G.outside_unfixed G.target o w

end PhysicalShortening

end AES8.PaperMDSShortening
