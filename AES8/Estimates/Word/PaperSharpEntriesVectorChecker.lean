import AES8.Estimates.Word.PaperSharpEntriesBooleanChecker

/-! Function-valued transcripts allow balanced literal lookups. Encoding as
arrays is used only in the generic proof bridge, never in the numeric loop. -/
namespace AES8.PaperSharpEntriesVectorChecker
open AES8.PaperSharpEntriesFWHT AES8.PaperSharpEntriesTransformChecker
open AES8.PaperSharpEntriesBooleanChecker
set_option autoImplicit false

abbrev VectorStages := Fin 9 → Vector
def encode (stages : VectorStages) : StageTables := fun s => Array.ofFn (stages s)

theorem encode_apply (stages : VectorStages) (s : Fin 9) (i : Index) :
    stageVector (encode stages) s i = stages s i := by
  simp [stageVector, encode]

def checkStage (stages : VectorStages) (s : Fin 8) : Bool :=
  (List.finRange 256).all (fun i => decide (
    stages ⟨s.val+1, by omega⟩ i = butterfly s (stages ⟨s.val, by omega⟩) i))

theorem stage_sound (stages : VectorStages) (s : Fin 8)
    (hc : checkStage stages s = true) (i : Index) :
    stageVector (encode stages) ⟨s.val+1, by omega⟩ i =
      butterfly s (stageVector (encode stages) ⟨s.val, by omega⟩) i := by
  have he : stages ⟨s.val+1, by omega⟩ i =
      butterfly s (stages ⟨s.val, by omega⟩) i :=
    of_decide_eq_true (List.all_eq_true.mp hc i (List.mem_finRange i))
  have hv (j : Fin 9) : stageVector (encode stages) j = stages j := funext (encode_apply stages j)
  simpa only [hv] using he

theorem stages_sound (stages : VectorStages)
    (hc : ∀ s, checkStage stages s = true) : checkStages (encode stages) = true := by
  simp only [checkStages, decide_eq_true_eq]
  intro s i
  exact stage_sound stages s (hc s) i

def checkInitial (stages : VectorStages) (f : Vector) : Bool :=
  (List.finRange 256).all (fun i => decide (stages 0 i = f i))

theorem initial_sound (stages : VectorStages) (f : Vector)
    (hc : checkInitial stages f = true) :
    PaperSharpEntriesFWHT.checkInitial (encode stages) f = true := by
  simp only [PaperSharpEntriesFWHT.checkInitial, decide_eq_true_eq]
  intro i
  rw [encode_apply]
  exact of_decide_eq_true (List.all_eq_true.mp hc i (List.mem_finRange i))

def checkCaps (stages : VectorStages) (cap : ℤ) : Bool :=
  (List.finRange 256).all (fun i => decide (stages 8 i ≤ 256*cap))

theorem caps_sound (stages : VectorStages) (cap : ℤ)
    (hc : checkCaps stages cap = true) :
    PaperSharpEntriesTransformChecker.checkCaps (encode stages) cap = true := by
  simp only [PaperSharpEntriesTransformChecker.checkCaps, decide_eq_true_eq]
  intro i
  rw [encode_apply]
  exact of_decide_eq_true (List.all_eq_true.mp hc i (List.mem_finRange i))

end AES8.PaperSharpEntriesVectorChecker
