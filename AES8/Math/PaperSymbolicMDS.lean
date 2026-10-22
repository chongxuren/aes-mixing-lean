import Mathlib.Algebra.Field.ZMod
import AES8.Math.PaperSymbolicMinors

noncomputable section
namespace AES8.PaperSymbolicMDS
open Polynomial PaperSymbolicDiffusion PaperSymbolicSlopeTable
open scoped Matrix BigOperators CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192

variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

theorem eval_graphMatrix (a : F) (i : Fin 8) (j : Fin 4) :
    aeval a (graphMatrix (X : P) i j) = graphMatrix a i j := by
  fin_cases i <;> fin_cases j <;> simp [graphMatrix]

theorem eval_infoMatrix (a : F) (s : InformationSet) :
    (aeval a).mapMatrix (infoMatrix (X : P) s) = infoMatrix a s := by
  ext i j
  exact eval_graphMatrix a _ _

theorem information_det_ne_zero (a : F)
    (ha : 6 < (minpoly (ZMod 2) a).natDegree) (s : InformationSet) :
    (infoMatrix a s).det ≠ 0 := by
  have hn := PaperAlgebraicSpecialization.eval_ne_zero (K := ZMod 2) (F := F) a (infoMatrix (X : P) s).det
    (information_minors s).1 (by have := (information_minors s).2; omega)
  rw [AlgHom.map_det, eval_infoMatrix] at hn
  exact hn

theorem information_mulVec_bijective (a : F)
    (ha : 6 < (minpoly (ZMod 2) a).natDegree) (s : InformationSet) :
    Function.Bijective (fun x => infoMatrix a s *ᵥ x) := by
  have hu : IsUnit (infoMatrix a s) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr (information_det_ne_zero a ha s))
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,
    Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩

/-- The graph of M(a) is MDS: any four physical coordinates determine a
unique input, and every assignment on those coordinates is attained. -/
theorem graph_mds (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (s : Finset (Fin 8)) (hs : s.card = 4) :
    Function.Bijective (fun x : Fin 4 → F => fun i : s => graphWord a x i.val) := by
  let e := s.orderIsoOfFin hs
  have hb := information_mulVec_bijective a ha ⟨s,hs⟩
  constructor
  · intro x y h
    apply hb.injective
    funext i
    exact congrFun h (e i)
  · intro y
    obtain ⟨x, hx⟩ := hb.surjective (fun i => y (e i))
    refine ⟨x, ?_⟩
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun hx j

theorem graph_zero_of_four (a : F) (ha : 6 < (minpoly (ZMod 2) a).natDegree)
    (s : Finset (Fin 8)) (hs : s.card = 4) (x : Fin 4 → F)
    (hx : ∀ i ∈ s, graphWord a x i = 0) : x = 0 := by
  apply (graph_mds a ha s hs).injective
  funext i
  simpa [graphWord] using hx i.val i.property

end AES8.PaperSymbolicMDS
