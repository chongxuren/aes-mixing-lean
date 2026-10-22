/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.PaperMDSFiber

/-!
# The affine-coset form of the MDS fiber collision bound

The ambient points here lie in an arbitrary translate `offset + C` of the
additive MDS code.  Subtracting `offset` identifies each prescribed affine
fiber with the additive prescribed fiber in `PaperMDSFiber`.  Local function
sums are unchanged by the corresponding alphabet translations.  Thus the
paper's affine language introduces neither a hidden linearity assumption nor
an assumed observation multiplicity.  No AES numerical claims or attacks.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperMDSFiber

open PaperMDSGram

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Actual ambient points in an arbitrary affine translate of the code,
with the specified physical-coordinate values. -/
abbrev AffineFiber (C : AddSubgroup (K → V)) (offset : K → V)
    (fixed : Finset K) (target : K → V) :=
  {x : K → V // x - offset ∈ C ∧ ∀ i ∈ fixed, x i = target i}

/-- Subtracting the affine offset also subtracts it from the fixed labels. -/
def affineFiberEquiv (C : AddSubgroup (K → V)) (offset : K → V)
    (fixed : Finset K) (target : K → V) :
    AffineFiber C offset fixed target ≃ Fiber C fixed (target - offset) where
  toFun x := ⟨⟨x.val - offset, x.property.1⟩, by
    intro i hi
    change x.val i - offset i = target i - offset i
    rw [x.property.2 i hi]⟩
  invFun c := ⟨c.val.val + offset, ⟨by
    simpa only [add_sub_cancel_right] using c.val.property, by
    intro i hi
    have hc := c.property i hi
    change c.val.val i = target i - offset i at hc
    change c.val.val i + offset i = target i
    exact eq_sub_iff_add_eq.mp hc⟩⟩
  left_inv x := Subtype.ext (sub_add_cancel _ _)
  right_inv c := Subtype.ext (Subtype.ext (add_sub_cancel_right _ _))

/-- The affine fiber's exact size is inherited by an explicit translation
bijection, without any uniform-fiber premise. -/
theorem affine_prescribed_card (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (offset : K → V) (fixed : Finset K) (hfixed : fixed.card ≤ k) (target : K → V) :
    Fintype.card (AffineFiber C offset fixed target) =
      Fintype.card V ^ (k - fixed.card) := by
  rw [Fintype.card_congr (affineFiberEquiv C offset fixed target)]
  exact prescribed_card C k hk hMDS fixed hfixed (target - offset)

/-- Paper Lemma 7 (`lem:fiber-sum`) on an arbitrary affine translate of an
additive MDS code, after any admissible number of coordinates is fixed.
All cardinalities and selected information sets are derived from MDS. -/
theorem paper_affine_mds_collision_bound (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (offset : K → V) (fixed observed : Finset K) (hd : Disjoint fixed observed)
    (hfixed : fixed.card ≤ k) (target : K → V) (g : K → V → ℝ) (h delta : ℝ)
    (hg0 : ∀ i ∈ observed, ∀ x, 0 ≤ g i x)
    (hgsum : ∀ i ∈ observed, (∑ x, g i x) ≤ h)
    (hgcap : ∀ i ∈ observed, ∀ x, g i x ≤ delta) :
    (∑ x : AffineFiber C offset fixed target, ∏ i ∈ observed, g i (x.val i)) ≤
      collisionBound (Fintype.card V) observed.card (k - fixed.card) h delta := by
  let e := affineFiberEquiv C offset fixed target
  have hb := paper_affine_mds_fiber_collision_bound C k hk hMDS fixed observed hd hfixed
    (target - offset) (fun i x => g i (x + offset i)) h delta
    (fun i hi x => hg0 i hi (x + offset i))
    (by
      intro i hi
      calc
        (∑ x : V, g i (x + offset i)) = ∑ x : V, g i x :=
          Equiv.sum_comp (Equiv.addRight (offset i)) (g i)
        _ ≤ h := hgsum i hi)
    (fun i hi x => hgcap i hi (x + offset i))
  have hsum := e.symm.sum_comp
    (fun x : AffineFiber C offset fixed target => ∏ i ∈ observed, g i (x.val i))
  change (∑ c : Fiber C fixed (target - offset),
    ∏ i ∈ observed, g i (c.val.val i + offset i)) =
      (∑ x : AffineFiber C offset fixed target, ∏ i ∈ observed, g i (x.val i)) at hsum
  rw [← hsum]
  exact hb

end AES8.PaperMDSFiber
