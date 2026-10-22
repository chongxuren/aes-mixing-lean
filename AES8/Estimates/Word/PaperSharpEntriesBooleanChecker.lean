import AES8.Estimates.Word.PaperSharpEntriesTransformChecker

/-!
# Boolean finite loops, with exact proposition interfaces

The production evaluator discards each comparison proof before advancing the
loop. Soundness reconstructs the quantified mathematical statement separately.
Stage checks can be proved independently to bound peak kernel memory.
-/

namespace AES8.PaperSharpEntriesBooleanChecker
open AES8.PaperSharpEntriesFinite
open AES8.PaperSharpEntriesFWHT
open AES8.PaperSharpEntriesTransformChecker
set_option autoImplicit false

def checkStage (stages : StageTables) (s : Fin 8) : Bool :=
  (List.finRange 256).all (fun i => decide (
    stageVector stages ⟨s.val+1, by omega⟩ i =
      butterfly s (stageVector stages ⟨s.val, by omega⟩) i))

theorem checkStage_sound (stages : StageTables) (s : Fin 8)
    (hc : checkStage stages s = true) (i : Index) :
    stageVector stages ⟨s.val+1, by omega⟩ i =
      butterfly s (stageVector stages ⟨s.val, by omega⟩) i := by
  exact of_decide_eq_true (List.all_eq_true.mp hc i (List.mem_finRange i))

theorem checkStages_of_stages (stages : StageTables)
    (hc : ∀ s : Fin 8, checkStage stages s = true) : checkStages stages = true := by
  simp only [checkStages, decide_eq_true_eq]
  intro s i
  exact checkStage_sound stages s (hc s) i

def checkInitialBool (stages : StageTables) (f : Vector) : Bool :=
  (List.finRange 256).all (fun i => decide (stageVector stages 0 i = f i))

theorem checkInitialBool_sound (stages : StageTables) (f : Vector)
    (hc : checkInitialBool stages f = true) : checkInitial stages f = true := by
  simp only [checkInitial, decide_eq_true_eq]
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp hc i (List.mem_finRange i))

def checkCapsBool (stages : StageTables) (cap : ℤ) : Bool :=
  (List.finRange 256).all (fun i => decide (stageVector stages 8 i ≤ 256*cap))

theorem checkCapsBool_sound (stages : StageTables) (cap : ℤ)
    (hc : checkCapsBool stages cap = true) : checkCaps stages cap = true := by
  simp only [checkCaps, decide_eq_true_eq]
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp hc i (List.mem_finRange i))

def checkMapBool (p : Byte → ℕ) (B : Byte → Byte)
    (alpha beta : Fin 255) (r cap : ℕ) : Bool :=
  (List.finRange 256).all (fun i => decide (
    mixedSum p B (nonzeroByte alpha) (nonzeroByte beta) (byteOf i) r ≤ cap))

theorem checkMapBool_sound (p : Byte → ℕ) (B : Byte → Byte)
    (alpha beta : Fin 255) (r cap : ℕ)
    (hc : checkMapBool p B alpha beta r cap = true) (gamma : Byte) :
    mixedSum p B (nonzeroByte alpha) (nonzeroByte beta) gamma r ≤ cap := by
  exact of_decide_eq_true (List.all_eq_true.mp hc gamma.bits.toFin
    (List.mem_finRange gamma.bits.toFin))

end AES8.PaperSharpEntriesBooleanChecker
