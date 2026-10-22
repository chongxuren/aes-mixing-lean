import AES8.Reductions.Graph.PaperSlopeGraphInvertible
import AES8.Math.PaperSymbolicRotation

/-! The symbolic matrix's graph as the generic original linear MDS code.
The geometric slope classes are derived from symbolic shortening equations.
No field-value slope enumeration or analytic endpoint is assumed. -/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperSlopeSymbolicGraph
open AESMixing PaperMDSGram PaperWordGraphCode
open PaperSlopePhysicalContraction PaperSlopePhysicalFamily
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]

def diffusionLinearMap (a : F) : (Fin 4 → F) →ₗ[F] (Fin 4 → F) where
  toFun x := PaperSymbolicDiffusion.matrix a *ᵥ x
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' t x := Matrix.mulVec_smul _ t x

theorem graphWord_eq (a : F) (x : Fin 4 → F) (i : Fin 8) :
    PaperSlopeLinearGraph.graphWord (diffusionLinearMap a) x i =
      PaperSymbolicMDS.graphWord a x i := by
  fin_cases i <;>
    simp [PaperSlopeLinearGraph.graphWord,diffusionLinearMap,
      PaperSymbolicMDS.graphWord,PaperSymbolicMDS.graphMatrix,
      PaperSymbolicDiffusion.matrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

abbrev code (a : F) : Submodule F (Fin 8 → F) :=
  PaperSlopeLinearGraph.graphCode (diffusionLinearMap a)

theorem graphEquiv_word (a : F) (x : Fin 4 → F) (i : Fin 8) :
    (PaperSlopeLinearGraph.graphEquiv (diffusionLinearMap a) x).val i =
      PaperSymbolicMDS.graphWord a x i := graphWord_eq a x i

/-- Every original information-set bijection is inherited literally from
the symbolic matrix, with its physical coordinate labels unchanged. -/
theorem code_isMDS (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree) :
    IsMDS (code a).toAddSubgroup 4 := by
  apply PaperSlopeLinearGraph.graph_isMDS_of_informationSets
  intro s hs
  simpa only [graphWord_eq] using PaperSymbolicMDS.graph_mds a ha s hs

/-- No inverse-map premise is added: the four output positions are an
information set of the same original graph code. -/
def diffusionEquiv (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree) :
    (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) :=
  PaperSlopeGraphInvertible.diffusionEquiv (diffusionLinearMap a) (code_isMDS a ha)

@[simp] theorem diffusionEquiv_toLinearMap
    (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree) :
    (diffusionEquiv a ha).toLinearMap = diffusionLinearMap a := rfl

theorem diffusionEquiv_isMDS
    (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree) :
    IsMDS (PaperSlopeLinearGraph.graphCode (diffusionEquiv a ha).toLinearMap).toAddSubgroup 4 :=
  code_isMDS a ha

theorem rotation_eq (p : Fin 6) (i : Fin 8) :
    PaperSlopePhysicalLabels.rotate (PaperSlopeCoincidences.rotation p) i =
      PaperSymbolicRotation.rotation (PaperSymbolicRotation.pairRotation p) i := by
  fin_cases p <;> fin_cases i <;> decide

theorem firstMark_eq (p : Fin 6) : PaperSlopePhysicalLabels.firstMark p =
    PaperSymbolicRotation.rotation (PaperSymbolicRotation.pairRotation p) 4 :=
  rotation_eq p 4

theorem secondMark_eq (p : Fin 6) : PaperSlopePhysicalLabels.secondMark p =
    PaperSymbolicRotation.rotation (PaperSymbolicRotation.pairRotation p)
      (PaperSymbolicShortening.secondMark (PaperSlopeCoincidences.pairType p)) := by
  fin_cases p <;> decide

theorem shortened_equation (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (p : Fin 6) (k : Fin 20)
    (x : zeroShortening (code a).toAddSubgroup
      (zeroPositions (PaperSlopePhysicalLabels.firstMark p) (PaperSlopePhysicalLabels.secondMark p)
        (PaperSlopePhysicalLabels.uniform p k))) :
    x.val (PaperSlopePhysicalLabels.secondMark p) =
      PaperSymbolicSlopeTable.slope a (PaperSlopeCoincidences.pairType p) k *
        x.val (PaperSlopePhysicalLabels.firstMark p) := by
  obtain ⟨v,hv⟩ := x.property.1
  have he (i : Fin 8) : x.val i = PaperSymbolicMDS.graphWord a v i := by
    rw [← graphWord_eq a v i]
    exact (congrFun hv i).symm
  have hz : PaperSymbolicRotation.RotatedShortened a
      (PaperSlopeCoincidences.pairType p) (PaperSymbolicRotation.pairRotation p) k v := by
    intro i hi
    rw [← he]
    apply x.property.2
    have hz := PaperSlopePhysicalLabels.zeros_representative p k
    change PaperSlopePhysicalLabels.zeros p k = _ at hz
    rw [← rotation_eq p i]
    change PaperSlopePhysicalLabels.rotate (PaperSlopeCoincidences.rotation p) i ∈
      PaperSlopePhysicalLabels.zeros p k
    rw [hz]
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  rw [he,he,firstMark_eq,secondMark_eq]
  exact (PaperSymbolicRotation.rotated_marked_image a ha
    (PaperSlopeCoincidences.pairType p) (PaperSymbolicRotation.pairRotation p) k _ _).mp
      ⟨v,hz,rfl,rfl⟩

theorem physicalSlope_eq (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (p : Fin 6) (k : Fin 20) : physicalSlope (code a) (code_isMDS a ha) p k =
      PaperSymbolicSlopeTable.slope a (PaperSlopeCoincidences.pairType p) k := by
  exact lineSlope_eq_of_equation (code a) (code_isMDS a ha) _ (label_zero_card p k) _ _ _ _
    (shortened_equation a ha p k)

theorem sameSlopeClasses (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree) :
    SameSlopeClasses (code a) (code_isMDS a ha) := by
  intro p k l
  simp only [physicalSlope_eq a ha]
  exact PaperSymbolicSlopeTable.slope_eq_iff a ha _ k l

theorem diffusionEquiv_sameSlopeClasses
    (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree) :
    SameSlopeClasses (PaperSlopeLinearGraph.graphCode (diffusionEquiv a ha).toLinearMap)
      (diffusionEquiv_isMDS a ha) := sameSlopeClasses a ha

end AES8.PaperSlopeSymbolicGraph
