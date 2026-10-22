import AES8.Reductions.Graph.PaperSlopeLinearGraph
import AES8.Math.PaperSlopeOutputFrame
import AES8.Math.PaperActivityArrayResidual

/-! Finite coordinate interfaces for the physical degree-two energy.
The six residual masks and twenty surviving frame labels use the literal
graph coordinates. No field enumeration or analytic estimate occurs here. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSlopeEnergyLabels
open AESMixing PaperActivityInputCoordinates PaperSlopeLinearGraph
open PaperSlopeCoincidences PaperSlopeCoincidenceMatrix PaperSlopeOutputFrame
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

def firstOutput (p : Fin 6) : Fin 4 := ![0,1,2,3,0,1] p
def secondOutput (p : Fin 6) : Fin 4 := ![1,2,3,0,2,3] p
def outputPair (p : Fin 6) : Finset (Fin 4) := {firstOutput p,secondOutput p}

theorem output_distinct (p : Fin 6) : firstOutput p ≠ secondOutput p := by
  fin_cases p <;> decide

theorem firstOutput_eq (p : Fin 6) :
    outputPos (firstOutput p) = PaperSlopePhysicalLabels.firstMark p := by
  fin_cases p <;> decide

theorem secondOutput_eq (p : Fin 6) :
    outputPos (secondOutput p) = PaperSlopePhysicalLabels.secondMark p := by
  fin_cases p <;> decide

def pairPosition (p : Fin 6) : PaperActivityArrayResidual.Position 2 :=
  ⟨residualMask (outputPair p),by fin_cases p <;> decide⟩

def pairsEquiv : Fin 6 ≃ PaperActivityArrayResidual.Position 2 :=
  Equiv.ofBijective pairPosition (by decide)

def unmarkedOutput (p : Fin 6) (i : Fin 2) : ↥((outputPair p)ᶜ) :=
  ⟨⟨((if i = 0 then (if pairType p then 1 else 2) else 3) + rotation p)%4,
      Nat.mod_lt _ (by decide)⟩,by fin_cases p <;> fin_cases i <;> decide⟩

def outsideEquiv (p : Fin 6) : Fin 2 ≃ ↥((outputPair p)ᶜ) :=
  Equiv.ofBijective (unmarkedOutput p) (by fin_cases p <;> decide)

def outsideBits (p : Fin 6) (b : Fin 2 → Bool) : ↥((outputPair p)ᶜ) → Bool :=
  fun i => b ((outsideEquiv p).symm i)

def outsideBitsEquiv (p : Fin 6) : (Fin 2 → Bool) ≃ (↥((outputPair p)ᶜ) → Bool) :=
  Equiv.arrowCongr (outsideEquiv p) (Equiv.refl Bool)

theorem outsideBitsEquiv_apply (p : Fin 6) (b : Fin 2 → Bool) :
    outsideBitsEquiv p b = outsideBits p b := rfl

def retainedLabel {F : Type*} (p : Fin 6) (y : F × F) : outputPair p → F :=
  pairOutputLabel (firstOutput p) (secondOutput p) y

def retainedLabelEquiv (F : Type*) (p : Fin 6) : (F × F) ≃ (outputPair p → F) where
  toFun := retainedLabel p
  invFun y := (y ⟨firstOutput p,by simp [outputPair]⟩,
    y ⟨secondOutput p,by simp [outputPair]⟩)
  left_inv y := by simp [retainedLabel,pairOutputLabel,output_distinct,Ne.symm]
  right_inv y := by
    funext i
    have hi : i.val = firstOutput p ∨ i.val = secondOutput p := by
      simpa only [outputPair,Finset.mem_insert,Finset.mem_singleton] using i.property
    rcases hi with hi | hi
    · have hie : i = ⟨firstOutput p,by simp [outputPair]⟩ := Subtype.ext hi
      rw [hie]
      simp [retainedLabel,pairOutputLabel]
    · have hie : i = ⟨secondOutput p,by simp [outputPair]⟩ := Subtype.ext hi
      rw [hie]
      simp [retainedLabel,pairOutputLabel,Ne.symm (output_distinct p)]

abbrev FullChoice := Interior × (Fin 2 → Bool)

def inputBits (A : Interior) : Fin 4 → Bool := fun i => decide (i ∈ A.val)

def uniformOf (p : Fin 6) (c : FullChoice) : Finset (Fin 8) :=
  (c.1.val.image inputPos) ∪
    ((Finset.univ.filter (fun i : Fin 2 => c.2 i)).image
      (fun i => outputPos (unmarkedOutput p i).val))

theorem uniformOf_disjoint (p : Fin 6) (c : FullChoice) :
    Disjoint (PaperSlopePhysicalContraction.marks
      (outputPos (firstOutput p)) (outputPos (secondOutput p))) (uniformOf p c) := by
  fin_cases p <;> revert c <;> decide

theorem uniformOf_inputFrame (p : Fin 6) (c : FullChoice) :
    inputFrame (uniformOf p c) = inputBits c.1 := by
  fin_cases p <;> revert c <;> decide

theorem uniformOf_outputFrame (p : Fin 6) (c : FullChoice) :
    (fun j : ↥((outputPair p)ᶜ) => outputFrame (uniformOf p c) j.val) =
      outsideBits p c.2 := by
  funext j
  obtain ⟨i,rfl⟩ := (outsideEquiv p).surjective j
  simp only [outsideBits,Equiv.symm_apply_apply]
  change outputFrame (uniformOf p c) (unmarkedOutput p i).val = c.2 i
  fin_cases p <;> fin_cases i <;> revert c <;> decide

abbrev Choice (p : Fin 6) := {c : FullChoice // (uniformOf p c).card = 3}

def tripleChoice (p : Fin 6) (k : Fin 20) : Choice p :=
  ⟨(inputIndex p k,outputBits p k),by fin_cases p <;> fin_cases k <;> decide⟩

def triplesEquiv (p : Fin 6) : Fin 20 ≃ Choice p :=
  Equiv.ofBijective (tripleChoice p) (by fin_cases p <;> decide)

theorem uniformOf_tripleChoice (p : Fin 6) (k : Fin 20) :
    uniformOf p (tripleChoice p k).val = PaperSlopePhysicalLabels.uniform p k := by
  fin_cases p <;> fin_cases k <;> decide

end AES8.PaperSlopeEnergyLabels
