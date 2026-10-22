import AES8.Reductions.Graph.PaperSlopePhysicalContraction

/-!
# Generic graph-code family with the paper's slope coincidences

This interface retains the original linear MDS code and asks only for the
geometric equality classes of its derived nonzero slopes.  Thus it applies
to every circulant finite-field graph with these classes; it does not make
an AES-only or analytic-bound assumption.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopePhysicalFamily
open PaperSlopePhysicalContraction
set_option autoImplicit false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem label_disjoint (p : Fin 6) (k : Fin 20) :
    Disjoint (marks (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p)) (PaperSlopePhysicalLabels.uniform p k) := by
  exact PaperSlopePhysicalLabels.uniform_disjoint p k

theorem label_zero_card (p : Fin 6) (k : Fin 20) :
    (zeroPositions (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p) (PaperSlopePhysicalLabels.uniform p k)).card = 3 := by
  have h := zero_card_plus (PaperSlopePhysicalLabels.marks_distinct p) (PaperSlopePhysicalLabels.uniform p k) (label_disjoint p k)
  rw [PaperSlopePhysicalLabels.uniform_card] at h
  omega

def physicalSlope (C : Submodule F (Position → F)) (hC : PaperMDSGram.IsMDS C.toAddSubgroup 4)
    (p : Fin 6) (k : Fin 20) : F :=
  lineSlope C hC _ (label_zero_card p k) (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p)
    (mark_not_zero (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p) (PaperSlopePhysicalLabels.uniform p k)).1

theorem physicalSlope_ne_zero (C : Submodule F (Position → F))
    (hC : PaperMDSGram.IsMDS C.toAddSubgroup 4) (p : Fin 6) (k : Fin 20) :
    physicalSlope C hC p k ≠ 0 :=
  lineSlope_ne_zero C hC _ (label_zero_card p k) _ _
    (mark_not_zero (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p) (PaperSlopePhysicalLabels.uniform p k)).1
    (mark_not_zero (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p) (PaperSlopePhysicalLabels.uniform p k)).2

theorem physical_contraction_eq (C : Submodule F (Position → F))
    (hC : PaperMDSGram.IsMDS C.toAddSubgroup 4) (p : Fin 6) (k : Fin 20) (y : F × F) :
    contraction C.toAddSubgroup (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p) (PaperSlopePhysicalLabels.uniform p k) y =
      PaperSlopeLineGram.response (physicalSlope C hC p k) y := by
  exact contraction_line C hC (PaperSlopePhysicalLabels.marks_distinct p) (PaperSlopePhysicalLabels.uniform p k)
    (label_disjoint p k) (PaperSlopePhysicalLabels.uniform_card p k) y

/-- This premise concerns only equality of actual geometric line slopes. -/
def SameSlopeClasses (C : Submodule F (Position → F))
    (hC : PaperMDSGram.IsMDS C.toAddSubgroup 4) : Prop :=
  ∀ (p : Fin 6) (k l : Fin 20), physicalSlope C hC p k = physicalSlope C hC p l ↔
    PaperSymbolicSlopeTable.slopeClass (PaperSlopeCoincidences.pairType p) k =
      PaperSymbolicSlopeTable.slopeClass (PaperSlopeCoincidences.pairType p) l

/-- Exact physical pair response Gram, with its derived q^(-3/2) scale. -/
theorem physical_scaled_gram (C : Submodule F (Position → F))
    (hC : PaperMDSGram.IsMDS C.toAddSubgroup 4) (hclasses : SameSlopeClasses C hC)
    (p : Fin 6) (k l : Fin 20) :
    (Fintype.card F : ℝ)^4 *
      (∑ y : F × F,
        contraction C.toAddSubgroup (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p) (PaperSlopePhysicalLabels.uniform p k) y *
        contraction C.toAddSubgroup (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p) (PaperSlopePhysicalLabels.uniform p l) y) =
      (Fintype.card F : ℝ)*(Fintype.card F-1)*
        (if PaperSymbolicSlopeTable.slopeClass (PaperSlopeCoincidences.pairType p) k =
          PaperSymbolicSlopeTable.slopeClass (PaperSlopeCoincidences.pairType p) l then 1 else 0)-Fintype.card F := by
  simp_rw [physical_contraction_eq C hC]
  rw [PaperSlopeLineGram.scaled_inner _ _ (physicalSlope_ne_zero C hC p k)
    (physicalSlope_ne_zero C hC p l)]
  simp only [hclasses p k l]

end AES8.PaperSlopePhysicalFamily
