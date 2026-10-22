import AES8.Math.PaperSymbolicInformation

noncomputable section
namespace AES8.PaperSymbolicMDS
open Polynomial PaperSymbolicDiffusion PaperSymbolicSlopeTable
open scoped Matrix BigOperators CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192

theorem information_minors_0 (k : Fin 10) :
    (infoMatrix (X : P) (informationSets ⟨0+k.val, by omega⟩)).det ≠ 0 ∧
      (infoMatrix (X : P) (informationSets ⟨0+k.val, by omega⟩)).det.natDegree ≤ 3 := by
  rw [infoMatrix_rows]
  fin_cases k <;>
    simp [informationRows, graphMatrix, Matrix.det_succ_row_zero, Matrix.det_fin_three,
      Fin.sum_univ_succ, Matrix.submatrix_apply] <;> ring_nf <;> (try simp) <;>
    (repeat' apply And.intro) <;> first | (compute_degree!; done) | symbolic_poly_ne

end AES8.PaperSymbolicMDS
