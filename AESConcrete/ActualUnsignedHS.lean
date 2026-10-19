import AESConcrete.SurvivorCubeNumbers
import AESConcrete.MarkedDegreeHilbertSchmidt
import AESConcrete.ActualActivityTrace

/-!
# Actual unsigned marked bounds and the remaining three-mark premise

The finite cube evaluation is substituted into the actual marked-block
bound. Exact product-pattern counts then supply every degree HS entry
except total marked degree three. That signed estimate is explicit in
the final conditional assembly and is not assumed as an established fact.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualUnsignedHS
open AESMixing
open ByteOrientations (Orientation)
open HilbertSchmidtEnergy (hs hs_nonneg)
open MarkedBlockVectorization (Marked)
open ActualMarkedFrameBound (centeredPattern survivorBound)
open MarkedDegreeHilbertSchmidt (patternBlock)
open WordMomentAssembly (residual)

attribute [local instance] Classical.propDecidable

theorem marking_nonempty_of_card_pos (m : GraphPosition → Bool)
    (h : 0 < Fintype.card (Marked m)) : ∃ p, m p = true := by
  obtain ⟨p⟩ := Fintype.card_pos_iff.mp h
  exact ⟨p.val,p.property⟩

theorem actual_unsigned_pattern (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (ell : ℕ)
    (hlen : Fintype.card (Marked m) = ell) (hpos : 0 < ell) (hle : ell ≤ 8)
    (hthree : ell ≠ 3) :
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m)^2 ≤
      WordMomentNumbers.markedCap ell := by
  have hm := marking_nonempty_of_card_pos m (by omega)
  calc
    _ ≤ survivorBound m := ActualMarkedFrameBound.actual_centeredPattern_energy_le
      left right inverse m hm
    _ = SurvivorRelabel.cubeBound (Fin (8-ell)) ell :=
      SurvivorRelabel.survivorBound_eq_cubeBound_fin m ell hlen
    _ ≤ _ := SurvivorCubeNumbers.cubeBound_le_markedCap ell hpos hle hthree

def marking (a b : Fin 4 → Bool) : GraphPosition → Bool := Sum.elim a b

def markedSumEquiv (a b : Fin 4 → Bool) : Marked (marking a b) ≃ Marked a ⊕ Marked b where
  toFun p := match p with
    | ⟨Sum.inl i,h⟩ => Sum.inl ⟨i,h⟩
    | ⟨Sum.inr i,h⟩ => Sum.inr ⟨i,h⟩
  invFun p := match p with
    | Sum.inl i => ⟨Sum.inl i.val,i.property⟩
    | Sum.inr i => ⟨Sum.inr i.val,i.property⟩
  left_inv p := by rcases p with ⟨p,h⟩; cases p <;> rfl
  right_inv p := by cases p <;> rfl

theorem marked_card_eq_degree (a : Fin 4 → Bool) :
    Fintype.card (Marked a) = (degreeIndex a).val := by
  simp [Marked, degreeIndex, residualDegree, Fintype.card_subtype]

theorem marking_card (a b : Fin 4 → Bool) :
    Fintype.card (Marked (marking a b)) = (degreeIndex a).val + (degreeIndex b).val := by
  simpa only [Fintype.card_sum, marked_card_eq_degree] using
    Fintype.card_congr (markedSumEquiv a b)

theorem centeredPattern_marking (left right : Orientation) (inverse : Bool)
    (a b : Fin 4 → Bool) :
    centeredPattern left right inverse (marking a b) =
      patternBlock 0 (residual left right inverse) a b := rfl

theorem zero_pattern_bound (left right : Orientation) (inverse : Bool)
    (a b : Fin 4 → Bool) (hzero : (degreeIndex a).val + (degreeIndex b).val = 0) :
    hs (patternBlock 0 (residual left right inverse) a b)^2 ≤
      WordMomentNumbers.markedCap 0 / 4294967296 := by
  have ha : degreeIndex a = 0 := Fin.ext (by omega)
  have hb : degreeIndex b = 0 := Fin.ext (by omega)
  rw [degreeIndex_zero_iff] at ha hb
  subst a
  subst b
  have he : patternBlock 0 (residual left right inverse) (fun _ => false) (fun _ => false) =
      DegreeHilbertSchmidt.block 0 (residual left right inverse) 0 0 := by
    simp only [patternBlock, DegreeHilbertSchmidt.block, degreeKernel_zero]
  rw [he]
  have h := ActualActivityTrace.degree_zero_trace_scaled_lt left right inverse
  change (4294967296 : ℝ) * hs (DegreeHilbertSchmidt.block 0 (residual left right inverse) 0 0)^2 < 71 at h
  norm_num only [WordMomentNumbers.markedCap]
  linarith

theorem pattern_bound_except_three (left right : Orientation) (inverse : Bool)
    (a b : Fin 4 → Bool) (hthree : (degreeIndex a).val + (degreeIndex b).val ≠ 3) :
    hs (patternBlock 0 (residual left right inverse) a b)^2 ≤
      WordMomentNumbers.markedCap ((degreeIndex a).val + (degreeIndex b).val) / 4294967296 := by
  by_cases hz : (degreeIndex a).val + (degreeIndex b).val = 0
  · simpa only [hz] using zero_pattern_bound left right inverse a b hz
  · have h := actual_unsigned_pattern left right inverse (marking a b)
      ((degreeIndex a).val + (degreeIndex b).val) (marking_card a b)
      (by omega) (by have ha := (degreeIndex a).isLt; have hb := (degreeIndex b).isLt; omega) hthree
    rw [centeredPattern_marking] at h
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4294967296)).mpr (by nlinarith)

theorem degree_hs_bound_except_three (left right : Orientation) (inverse : Bool)
    (i j : Fin 5) (hthree : i.val+j.val ≠ 3) :
    hs (DegreeHilbertSchmidt.block 0 (residual left right inverse) i j) ≤
      WordMomentNumbers.hs i j / 65536 := by
  have hb := MarkedDegreeHilbertSchmidt.degree_hs_sq_le (0 : BinaryWord 8)
    (by norm_num [BinaryWord.card]) (residual left right inverse) i j
    (WordMomentNumbers.markedCap (i.val+j.val)/4294967296) (by
      intro a b ha hb
      have hp := pattern_bound_except_three left right inverse a b
        (by simpa only [ha,hb] using hthree)
      simpa only [ha,hb] using hp)
  have hc := div_le_div_of_nonneg_right (WordMomentNumbers.marked_to_degree i j)
    (by norm_num : (0:ℝ) ≤ 4294967296)
  apply (sq_le_sq₀ (hs_nonneg _) (div_nonneg (WordMomentNumbers.hs_nonneg i j)
    (by norm_num))).mp
  calc
    _ ≤ (Nat.choose 4 i.val : ℝ) * Nat.choose 4 j.val *
        (WordMomentNumbers.markedCap (i.val+j.val)/4294967296) := hb
    _ = ((Nat.choose 4 i.val : ℝ) * Nat.choose 4 j.val *
        WordMomentNumbers.markedCap (i.val+j.val))/4294967296 := by ring
    _ ≤ WordMomentNumbers.hs i j ^ 2 / 4294967296 := hc
    _ = _ := by ring

/-- The only remaining marked-block resource for the complete HS table. -/
def HasThreeMarkBounds (left right : Orientation) (inverse : Bool) : Prop :=
  ∀ m : GraphPosition → Bool, Fintype.card (Marked m) = 3 →
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m)^2 ≤ 22

theorem degree_table_of_three_mark_bounds (left right : Orientation) (inverse : Bool)
    (hthree : HasThreeMarkBounds left right inverse) :
    WordMomentAssembly.HasDegreeHSBounds left right inverse := by
  apply MarkedDegreeHilbertSchmidt.degree_table_of_pattern_bounds
  intro a b
  by_cases h : (degreeIndex a).val + (degreeIndex b).val = 3
  · have hm : Fintype.card (Marked (marking a b)) = 3 := (marking_card a b).trans h
    have he := hthree (marking a b) hm
    rw [centeredPattern_marking] at he
    rw [h]
    norm_num only [WordMomentNumbers.markedCap]
    linarith
  · exact pattern_bound_except_three left right inverse a b h

end AESConcrete.ActualUnsignedHS
