import AESConcrete.ActualMarkedFrameBound
import AESConcrete.MarkedBlockScale
import Mathlib.Data.Fintype.EquivFin

/-!
# Actual survivor sums as cardinality-indexed Boolean cubes

The actual activity choice keeps its physical zero masks until zero_count
identifies their size with the number of false choices. Index equivalences
preserve that count and the actual tensor inverse frame. Exact finite-sum
reindexing then removes the names of the unmarked positions.

Constructive mathematics only; no attacks, manuscript changes or edits to
frozen sources. This module supplies no numerical cube evaluation and no
signed degree-three improvement.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.SurvivorRelabel
open AESMixing
open AESConcrete.ActivityFrame (frameInverse byteInverse)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.ActualMarkedContractionEnergy (dimension zeta)
open AESConcrete.ActualMarkedFrameBound (survives Surviving survivorBound)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

section Cube
variable {I J : Type*} [Fintype I] [Fintype J]

def falseCount (s : I → Bool) : ℕ := Fintype.card {i : I // s i = false}

def cubeSurvives (ell : ℕ) (s : I → Bool) : Prop :=
  0 < 4 - falseCount s ∧ 4 - falseCount s < ell

-- The complete cube, with explicit zero terms outside the survivor set,
-- is the interface used by the separate exact rational evaluations.
def cubeBound (I : Type*) [Fintype I] (ell : ℕ) : ℝ :=
  ∑ s : I → Bool, if cubeSurvives ell s then
    zeta ell (4 - falseCount s) *
      (∑ t : I → Bool, if cubeSurvives ell t then |frameInverse s t| else 0)
    else 0

/-- Pull back Boolean choices along an equivalence of their index types. -/
def cubeReindex (e : I ≃ J) : (J → Bool) ≃ (I → Bool) where
  toFun s i := s (e i)
  invFun t j := t (e.symm j)
  left_inv s := by funext j; simp
  right_inv t := by funext i; simp

theorem falseCount_comp (e : I ≃ J) (s : J → Bool) :
    falseCount (fun i => s (e i)) = falseCount s := by
  exact Fintype.card_congr (e.subtypeEquiv (fun i => Iff.rfl))

theorem frameInverse_comp (e : I ≃ J) (s t : J → Bool) :
    frameInverse (fun i => s (e i)) (fun i => t (e i)) = frameInverse s t := by
  exact e.prod_comp (fun j => byteInverse (s j) (t j))

theorem cubeSurvives_comp (e : I ≃ J) (ell : ℕ) (s : J → Bool) :
    cubeSurvives ell (fun i => s (e i)) ↔ cubeSurvives ell s := by
  simp only [cubeSurvives, falseCount_comp]

theorem falseCount_reindex (e : I ≃ J) (s : J → Bool) :
    falseCount (cubeReindex e s) = falseCount s := falseCount_comp e s

theorem cubeSurvives_reindex (e : I ≃ J) (ell : ℕ) (s : J → Bool) :
    cubeSurvives ell (cubeReindex e s) ↔ cubeSurvives ell s :=
  cubeSurvives_comp e ell s

theorem frameInverse_reindex (e : I ≃ J) (s t : J → Bool) :
    frameInverse (cubeReindex e s) (cubeReindex e t) = frameInverse s t :=
  frameInverse_comp e s t

/-- Relabeling preserves the full survivor cube sum exactly. -/
theorem cubeBound_equiv (e : I ≃ J) (ell : ℕ) : cubeBound I ell = cubeBound J ell := by
  have hrow (s : J → Bool) :
      (∑ t : I → Bool, if cubeSurvives ell t then
        |frameInverse (cubeReindex e s) t| else 0) =
      ∑ t : J → Bool, if cubeSurvives ell t then |frameInverse s t| else 0 := by
    calc
      _ = ∑ t : J → Bool, if cubeSurvives ell (cubeReindex e t) then
          |frameInverse (cubeReindex e s) (cubeReindex e t)| else 0 :=
        ((cubeReindex e).sum_comp (fun t : I → Bool =>
          if cubeSurvives ell t then |frameInverse (cubeReindex e s) t| else 0)).symm
      _ = _ := by simp only [cubeSurvives_reindex, frameInverse_reindex]
  unfold cubeBound
  calc
    _ = ∑ s : J → Bool, if cubeSurvives ell (cubeReindex e s) then
        zeta ell (4 - falseCount (cubeReindex e s)) *
          (∑ t : I → Bool, if cubeSurvives ell t then
            |frameInverse (cubeReindex e s) t| else 0) else 0 :=
      ((cubeReindex e).sum_comp (fun s : I → Bool =>
        if cubeSurvives ell s then zeta ell (4 - falseCount s) *
          (∑ t : I → Bool, if cubeSurvives ell t then |frameInverse s t| else 0) else 0)).symm
    _ = _ := by simp only [cubeSurvives_reindex, falseCount_reindex, hrow]

theorem not_cubeSurvives_one (s : I → Bool) : ¬ cubeSurvives 1 s := by
  unfold cubeSurvives
  omega

theorem cubeBound_one_eq_zero (I : Type*) [Fintype I] : cubeBound I 1 = 0 := by
  unfold cubeBound
  simp only [not_cubeSurvives_one, ↓reduceIte, Finset.sum_const_zero]

end Cube

section Actual

/-- Exact bridge from survivor subtypes to the complete cube with zero terms. -/
theorem sum_subtype_eq_sum_ite {S : Type*} [Fintype S]
    (P : S → Prop) (f : S → ℝ) :
    (∑ s : {s // P s}, f s.val) = ∑ s : S, if P s then f s else 0 := by
  symm
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

theorem dimension_eq_cube (m : GraphPosition → Bool) (s : Activity m → Bool) :
    dimension m s = 4 - falseCount s := by
  unfold dimension falseCount
  rw [MarkedBlockScale.zero_count]

theorem survives_iff_cube (m : GraphPosition → Bool) (s : Activity m → Bool) :
    survives m s ↔ cubeSurvives (Fintype.card (Marked m)) s := by
  simp only [survives, cubeSurvives, dimension_eq_cube]

/-- The actual physical zero masks have been discharged before relabeling. -/
theorem survivorBound_eq_cubeBound_activity (m : GraphPosition → Bool) :
    survivorBound m = cubeBound (Activity m) (Fintype.card (Marked m)) := by
  have hrow (s : Activity m → Bool) :
      (∑ t : Surviving m, |frameInverse s t.val|) =
      ∑ t : Activity m → Bool, if cubeSurvives (Fintype.card (Marked m)) t then
        |frameInverse s t| else 0 := by
    simpa only [survives_iff_cube] using
      sum_subtype_eq_sum_ite (survives m) (fun t => |frameInverse s t|)
  have hout := sum_subtype_eq_sum_ite (survives m)
    (fun s : Activity m → Bool =>
      zeta (Fintype.card (Marked m)) (dimension m s) *
        ∑ t : Surviving m, |frameInverse s t.val|)
  -- Generic and concrete Pi enumerations need not be definitionally equal.
  -- Their complete finite sets are equal by uniqueness of Fintype data.
  have huniv (f g : Fintype (Activity m → Bool)) :
      @Finset.univ (Activity m → Bool) f = @Finset.univ (Activity m → Bool) g :=
    congrArg (fun a : Fintype (Activity m → Bool) => a.elems) (Subsingleton.elim f g)
  calc
    _ = ∑ s : Activity m → Bool, if cubeSurvives (Fintype.card (Marked m)) s then
        zeta (Fintype.card (Marked m)) (4 - falseCount s) *
          (∑ t : Activity m → Bool, if cubeSurvives (Fintype.card (Marked m)) t then
            |frameInverse s t| else 0) else 0 := by
      simpa only [survivorBound, hrow, dimension_eq_cube, survives_iff_cube] using hout
    _ = _ := by
      unfold cubeBound
      apply Finset.sum_congr (huniv _ _)
      intro s _
      by_cases hs : cubeSurvives (Fintype.card (Marked m)) s
      · simp only [hs, ↓reduceIte]
        apply congrArg (fun row : ℝ => zeta (Fintype.card (Marked m)) (4 - falseCount s) * row)
        exact Finset.sum_congr (huniv _ _) (fun _ _ => rfl)
      · simp only [hs, ↓reduceIte]

theorem activity_card (m : GraphPosition → Bool) (ell : ℕ)
    (hlen : Fintype.card (Marked m) = ell) : Fintype.card (Activity m) = 8 - ell := by
  have h : Fintype.card (Marked m) + Fintype.card (Activity m) = 8 := by
    simpa only [GraphPosition, Fintype.card_sum, Fintype.card_fin] using
      MarkedBlockScale.partition_card m
  omega

/-- The survivor bound depends only on the number of marked positions. -/
theorem survivorBound_eq_cubeBound_fin (m : GraphPosition → Bool) (ell : ℕ)
    (hlen : Fintype.card (Marked m) = ell) :
    survivorBound m = cubeBound (Fin (8 - ell)) ell := by
  let e : Activity m ≃ Fin (8 - ell) := Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, activity_card m ell hlen])
  calc
    _ = cubeBound (Activity m) (Fintype.card (Marked m)) :=
      survivorBound_eq_cubeBound_activity m
    _ = cubeBound (Activity m) ell := by rw [hlen]
    _ = _ := cubeBound_equiv e ell

theorem not_survives_of_card_one (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 1) (s : Activity m → Bool) : ¬ survives m s := by
  unfold survives
  rw [hlen]
  omega

theorem surviving_isEmpty_of_card_one (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 1) : IsEmpty (Surviving m) :=
  ⟨fun s => not_survives_of_card_one m hlen s.val s.property⟩

theorem survivorBound_eq_zero_of_card_one (m : GraphPosition → Bool)
    (hlen : Fintype.card (Marked m) = 1) : survivorBound m = 0 := by
  rw [survivorBound_eq_cubeBound_activity, hlen, cubeBound_one_eq_zero]

end Actual
end AESConcrete.SurvivorRelabel
