import AESPaper.WordMarkedMoment
import AESConcrete.ActualMarkedCodeDual

/-!
# Actual marked image codes over AES words

The additive source is the actual graph (boundary x,x), shortened at the
physical zero positions. Its image uses the actual marked coordinates.
Only the alphabet-generic selection and information-set transfer lemmas
from ActualMarkedCodeDual are reused. No byte normalization or byte graph
is instantiated here. Fourier moments belong to WordMarkedDual.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordMarkedCode
open AESMixing AESConcrete
open AESMixing.AES (maskSize)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros)
open AESConcrete.ActualMarkedCodeMoment (marked_remaining selected_projection_injective)
open AESConcrete.ActualMarkedCodeDual
  (selectionRange selection_complement_card dual_projection_bijective_of_complement)
attribute [local instance] Classical.propDecidable

/-- Additive subgroup of inputs with the prescribed actual physical zeros. -/
def graphSubgroup (r z : Fin 16) : AddSubgroup (Fin 4 → AES.Word) where
  carrier := {x | graphZeroConditions GroupedRecurrence.boundary.toAddMonoidHom r z x}
  zero_mem' := by constructor <;> intro i _ <;> simp
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i hi
      rw [map_add]
      change GroupedRecurrence.boundary.toAddMonoidHom x i +
        GroupedRecurrence.boundary.toAddMonoidHom y i = 0
      rw [hx.1 i hi, hy.1 i hi, zero_add]
    · intro i hi
      change x i + y i = 0
      rw [hx.2 i hi, hy.2 i hi, zero_add]
  neg_mem' := by
    intro x hx
    constructor
    · intro i hi
      rw [map_neg]
      change -GroupedRecurrence.boundary.toAddMonoidHom x i = 0
      rw [hx.1 i hi, neg_zero]
    · intro i hi
      change -x i = 0
      rw [hx.2 i hi, neg_zero]

instance graphSubgroupFintype (r z : Fin 16) : Fintype (graphSubgroup r z) :=
  Fintype.ofFinite _

/-- The source subtype and additive subgroup have exactly the same inputs. -/
def sourceSubtypeEquiv (m : GraphPosition → Bool) (s : Activity m → Bool) :
    WordMarkedMoment.Source m s ≃ graphSubgroup (outputZeros m s) (inputZeros m s) where
  toFun c := ⟨c.val, c.property⟩
  invFun c := ⟨c.val, c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sourceSubtypeEquiv_apply_val (m : GraphPosition → Bool) (s : Activity m → Bool)
    (c : WordMarkedMoment.Source m s) : (sourceSubtypeEquiv m s c).val = c.val := rfl

/-- Marked coordinates of (boundary x,x); input positions retain their input role. -/
def markedHom (m : GraphPosition → Bool) (s : Activity m → Bool) :
    graphSubgroup (outputZeros m s) (inputZeros m s) →+ (Marked m → AES.Word) where
  toFun c := fun p => graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom c.val p.val
  map_zero' := by
    funext p
    change graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom
      (0 : Fin 4 → AES.Word) p.val = 0
    cases p.val <;> simp [graphCoordinate]
  map_add' x y := by
    funext p
    change graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom (x.val+y.val) p.val =
      graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom x.val p.val +
        graphCoordinate GroupedRecurrence.boundary.toAddMonoidHom y.val p.val
    cases p.val <;> simp [graphCoordinate, map_add]

theorem markedHom_sourceSubtypeEquiv (m : GraphPosition → Bool) (s : Activity m → Bool)
    (c : WordMarkedMoment.Source m s) :
    markedHom m s (sourceSubtypeEquiv m s c) =
      sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c := rfl

/-- The actual image subgroup, rather than an abstract code of matching size. -/
def markedCode (m : GraphPosition → Bool) (s : Activity m → Bool) :
    AddSubgroup (Marked m → AES.Word) := (markedHom m s).range

instance markedCodeFintype (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Fintype (markedCode m s) := Fintype.ofFinite _

theorem markedHom_injective (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m)) :
    Function.Injective (markedHom m s) := by
  exact selected_projection_injective GroupedRecurrence.boundary.toAddMonoidHom
    ActivityKernel.aesBoundary_zeroMDS (outputZeros m s) (inputZeros m s)
    (fun p : Marked m => p.val) Subtype.val_injective
    (fun p => marked_remaining m s p) hhigh

/-- Unit-source enumeration is equivalent to enumeration of its actual image
only in the range where physical MDS projection proves injectivity. -/
def sourceCodeEquiv (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m)) :
    WordMarkedMoment.Source m s ≃ markedCode m s :=
  (sourceSubtypeEquiv m s).trans
    (Equiv.ofBijective (markedHom m s).rangeRestrict
      ⟨fun _ _ h => markedHom_injective m s hhigh (congrArg Subtype.val h),
        (markedHom m s).rangeRestrict_surjective⟩)

theorem sourceCodeEquiv_apply (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m)) (c : WordMarkedMoment.Source m s) :
    (sourceCodeEquiv m s hhigh c).val =
      sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c := rfl

/-- Counting-measure normalization is preserved by the actual source/image
equivalence; this is a unit subgroup indicator, not a probability density. -/
theorem normalized_source_eq_code (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hhigh : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m)) (T : Marked m → AES.Word → AES.Word → ℝ) :
    MixedCodeMoment.normalizedResponse T
        (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s) =
      action (coordinateKernel T) (unitSubgroupIndicator (markedCode m s)) := by
  rw [MixedCodeMoment.subgroup_response]
  funext y
  let e := sourceCodeEquiv m s hhigh
  -- Editorial: congruence descent into the concrete word source unfolds its
  -- equivalence deeply. Reindex the explicit scalar sum before dividing.
  have hsum :
      (∑ c : WordMarkedMoment.Source m s,
        ∏ p : Marked m, T p (y p)
          (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c p)) =
      ∑ c : markedCode m s, ∏ p : Marked m, T p (y p) (c.val p) := by
    calc
      _ = ∑ c : WordMarkedMoment.Source m s,
          ∏ p : Marked m, T p (y p) ((e c).val p) := by
        apply Finset.sum_congr rfl
        intro c _
        rw [show (e c).val =
          sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c from
            sourceCodeEquiv_apply m s hhigh c]
      _ = _ := e.sum_comp (fun c : markedCode m s =>
        ∏ p : Marked m, T p (y p) (c.val p))
  change
    (∑ c : WordMarkedMoment.Source m s,
      ∏ p : Marked m, T p (y p)
        (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c p)) /
        Real.sqrt (Fintype.card (WordMarkedMoment.Source m s)) =
    (∑ c : markedCode m s, ∏ p : Marked m, T p (y p) (c.val p)) /
        Real.sqrt (Fintype.card (markedCode m s))
  rw [Fintype.card_congr e]
  exact congrArg (fun a : ℝ => a / Real.sqrt (Fintype.card (markedCode m s))) hsum

/-- Every actual physical marked information set transfers to the image code. -/
theorem markedCode_projection_bijective {A : Type*} [Fintype A]
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (p : A → Marked m) (hp : Function.Injective p)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card A = 4) :
    Function.Bijective (fun c : markedCode m s => fun a : A => c.val (p a)) := by
  have hs := AESConcrete.ActualMarkedCodeMoment.marked_projection_bijective
    GroupedRecurrence.boundary.toAddMonoidHom ActivityKernel.aesBoundary_zeroMDS
    m s p hp hsize
  constructor
  · intro c d h
    obtain ⟨x,hx⟩ := c.property
    obtain ⟨y,hy⟩ := d.property
    have hxy : x = y := by
      apply hs.1
      funext a
      change markedHom m s x (p a) = markedHom m s y (p a)
      rw [hx, hy]
      exact congrFun h a
    apply Subtype.ext
    exact hx.symm.trans ((congrArg (markedHom m s) hxy).trans hy)
  · intro v
    obtain ⟨x,hx⟩ := hs.2 v
    exact ⟨(markedHom m s).rangeRestrict (sourceSubtypeEquiv m s x), hx⟩

/-- The actual word trace-annihilator restriction comes from its physical
primal complement; no dual information-set or moment premise is assumed. -/
theorem actual_dual_projection_bijective {A : Type*} [Fintype A]
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (p : A → Marked m) (hp : Function.Injective p)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      (Fintype.card (Marked m)-Fintype.card A) = 4) :
    Function.Bijective
      (fun c : (WordFourierCore.wordPairing.product (Marked m)).annihilator (markedCode m s) =>
        fun a : A => c.val (p a)) := by
  apply dual_projection_bijective_of_complement WordFourierCore.wordPairing (markedCode m s) p hp
  have hcard := selection_complement_card p hp
  exact markedCode_projection_bijective m s
    (fun k : {k : Marked m // ¬ selectionRange p k} => k.val)
    Subtype.val_injective (by omega)

end AESPaper.WordMarkedCode
