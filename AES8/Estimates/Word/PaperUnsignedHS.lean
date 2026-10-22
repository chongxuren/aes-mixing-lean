import AES8.Estimates.Transfer.PaperActivityPrintedScalars
import AES8.Reductions.Graph.PaperMarkedFrameEnergy
import AESConcrete.ActualUnsignedHS

/-!
# Unsigned degree HS aggregation with the printed byte Gram bound

Module role: evaluate the original survivor cube and orthogonal pattern
multiplicities using the owned frame-energy provider. Marking definitions,
the explicit three-mark interface are reused. The zero-degree trace comes from
the printed spectral/trace activity calculation.
Degree three is supplied separately by the signed physical assembly. Source
candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperUnsignedHS
open AESMixing AESConcrete
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.HilbertSchmidtEnergy (hs hs_nonneg)
open AESConcrete.MarkedBlockVectorization (Marked)
open AESConcrete.ActualMarkedFrameBound (centeredPattern survivorBound)
open AESConcrete.MarkedDegreeHilbertSchmidt (patternBlock)
open AESConcrete.WordMomentAssembly (residual)
open AESConcrete.ActualUnsignedHS
  (marking_nonempty_of_card_pos marking marking_card centeredPattern_marking
    HasThreeMarkBounds)
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The zero-pattern trace uses the paper's exact activity formula. -/
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
  have h := PaperActivityPrintedScalars.byte_R00_hs_named left right inverse
  rw [AESConcrete.ActivityTrace.activityBlock_eq_degreeBlock] at h
  norm_num [PaperActivityPrintedScalars.wordQ] at h
  change (4294967296 : ℝ) * hs (DegreeHilbertSchmidt.block 0 (residual left right inverse) 0 0)^2 < 71 at h
  norm_num only [WordMomentNumbers.markedCap]
  linarith

theorem actual_unsigned_pattern (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (ell : ℕ)
    (hlen : Fintype.card (Marked m) = ell) (hpos : 0 < ell) (hle : ell ≤ 8)
    (hthree : ell ≠ 3) :
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m)^2 ≤
      WordMomentNumbers.markedCap ell := by
  have hm := marking_nonempty_of_card_pos m (by omega)
  calc
    _ ≤ survivorBound m := AES8.PaperMarkedFrameEnergy.actual_centeredPattern_energy_le
      left right inverse m hm
    _ = SurvivorRelabel.cubeBound (Fin (8-ell)) ell :=
      SurvivorRelabel.survivorBound_eq_cubeBound_fin m ell hlen
    _ ≤ _ := SurvivorCubeNumbers.cubeBound_le_markedCap ell hpos hle hthree


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


#print axioms actual_unsigned_pattern
#print axioms pattern_bound_except_three
#print axioms degree_hs_bound_except_three
#print axioms degree_table_of_three_mark_bounds
end AES8.PaperUnsignedHS
