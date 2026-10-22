import AES8.Math.PaperThinLinesRaw

/-!
# Literal outside fibers on a line

An outside label is the restriction of the actual word to physical outside
positions, with only admissible labels retained. If each word coordinate is a
bijection, fixing no outside position leaves the whole line; fixing at least
one determines the word. Both classification and exact fiber size are proved.
The affine-MDS specialization is supplied below, not assumed as a partition law.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperThinLines

attribute [local instance] Classical.propDecidable

variable {K V L : Type*} [Fintype K] [DecidableEq K] [Fintype V] [Fintype L]

def outsideRestriction (word : L → K → V) (s : Finset K) (x : L) : s → V :=
  fun i => word x i.val

abbrev OutsideLabels (word : L → K → V) (s : Finset K) :=
  Set.range (outsideRestriction word s)

def outside (word : L → K → V) (s : Finset K) (x : L) : OutsideLabels word s :=
  ⟨outsideRestriction word s x, ⟨x, rfl⟩⟩

def outsideDimension (s : Finset K) : ℕ := if s = ∅ then 1 else 0

def partialCap (s : Finset K) (A B : ℝ) : ℝ := if s = ∅ then B else A

theorem outsideDimension_cases (s : Finset K) :
    outsideDimension s = 0 ∨ outsideDimension s = 1 := by
  by_cases hs : s = ∅ <;> simp [outsideDimension, hs]

/-- The branch notation is exactly R_a, with a the derived fiber dimension. -/
theorem partialCap_dimension (s : Finset K) (A B : ℝ) :
    partialCap s A B = if outsideDimension s = 0 then A else B := by
  by_cases hs : s = ∅ <;> simp [partialCap, outsideDimension, hs]

theorem outside_surjective (word : L → K → V) (s : Finset K) :
    Function.Surjective (outside word s) := by
  intro o
  obtain ⟨x, hx⟩ := o.property
  exact ⟨x, Subtype.ext hx⟩

/-- A nonempty outside restriction of a line is injective. This is the
singleton branch of the paper's fiber classification. -/
theorem outside_injective (word : L → K → V)
    (s : Finset K) (hword : ∀ i ∈ s, Function.Injective (fun x => word x i))
    (hs : s ≠ ∅) : Function.Injective (outside word s) := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  intro x y hxy
  apply hword i hi
  exact congrFun (congrArg Subtype.val hxy) ⟨i, hi⟩

/-- An empty outside restriction is constant, so its only admissible fiber
is the entire line. -/
theorem outside_empty (word : L → K → V) (o : OutsideLabels word ∅) (x : L) :
    outside word ∅ x = o := by
  apply Subtype.ext
  funext i
  exact False.elim (Finset.notMem_empty i.val i.property)

/-- Exact singleton/whole-line classification, before taking any sums. -/
theorem outside_fiber_classification (word : L → K → V)
    (s : Finset K) (hword : ∀ i ∈ s, Function.Injective (fun x => word x i))
    (o : OutsideLabels word s) :
    (s = ∅ ∧ ∀ x, outside word s x = o) ∨
      (s ≠ ∅ ∧ ∃ x, ∀ y, outside word s y = o ↔ y = x) := by
  by_cases hs : s = ∅
  · subst s
    exact Or.inl ⟨rfl, outside_empty word o⟩
  · obtain ⟨x, hx⟩ := outside_surjective word s o
    exact Or.inr ⟨hs, x, fun y => ⟨fun hy => outside_injective word s hword hs
      (hy.trans hx.symm), fun hy => hy ▸ hx⟩⟩

/-- The classification gives exactly q^a points, including the a=0 case.
The sole cardinal premise here is the size of the entire line; the physical
MDS endpoint derives it by a coordinate equivalence. -/
theorem outside_fiber_card (word : L → K → V)
    (s : Finset K) (hword : ∀ i ∈ s, Function.Injective (fun x => word x i))
    (hcard : Nat.card L = Fintype.card V)
    (o : OutsideLabels word s) :
    Nat.card {x : L // outside word s x = o} =
      Fintype.card V ^ outsideDimension s := by
  rcases outside_fiber_classification word s hword o with ⟨hs, hall⟩ | ⟨hs, x, hx⟩
  · let e : {x : L // outside word s x = o} ≃ L :=
      { toFun := Subtype.val
        invFun := fun x => ⟨x, hall x⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, hcard]
    simp [outsideDimension, hs]
  · let e : {y : L // outside word s y = o} ≃ Unit :=
      { toFun := fun _ => ()
        invFun := fun _ => ⟨x, (hx x).mpr rfl⟩
        left_inv := fun y => Subtype.ext ((hx y.val).mp y.property).symm
        right_inv := fun y => by cases y; rfl }
    rw [Nat.card_congr e]
    simp [outsideDimension, hs]

/-- A partial sum becomes either one row/column or the total sum. This is a
general finite intermediate; the endpoint derives its raw bounds separately. -/
theorem outside_partial_sum (word : L → K → V)
    (s : Finset K) (hword : ∀ i ∈ s, Function.Injective (fun x => word x i))
    (g : L → ℝ) (A B : ℝ)
    (hpoint : ∀ x, g x ≤ A) (htotal : (∑ x, g x) ≤ B)
    (o : OutsideLabels word s) :
    (∑ x, if outside word s x = o then g x else 0) ≤ partialCap s A B := by
  rcases outside_fiber_classification word s hword o with ⟨hs, hall⟩ | ⟨hs, x, hx⟩
  · simp only [hall, if_true]
    simpa only [partialCap, hs, if_true] using htotal
  · simp_rw [hx]
    simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true, partialCap, hs,
      if_false] using hpoint x

section AffineMDS
variable [AddCommGroup V] [DecidableEq V]
open PaperMDSFiber PaperThinHolder PaperMDSGram

/-- A one-dimensional physical shortening of any additive MDS graph. -/
abbrev AffineShortLine (C : AddSubgroup (K → V)) (offset : K → V)
    (fixed : Finset K) (target : K → V) := AffineFiber C offset fixed target

def affineShortLineCoordinate (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k) (offset : K → V)
    (fixed : Finset K) (target : K → V) (hdim : fixed.card + 1 = k)
    (i : K) (hi : i ∉ fixed) : AffineShortLine C offset fixed target ≃ V :=
  affineCoordinateEquiv C k hk hC offset fixed target hdim i hi

theorem affineShortLine_card (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hC : IsMDS C k) (offset : K → V)
    (fixed : Finset K) (target : K → V) (hdim : fixed.card + 1 = k) :
    Fintype.card (AffineShortLine C offset fixed target) = Fintype.card V := by
  have hc := affine_prescribed_card C k hk hC offset fixed (by omega) target
  have he : k - fixed.card = 1 := by omega
  simpa only [he, pow_one] using hc

end AffineMDS
end AES8.PaperThinLines
