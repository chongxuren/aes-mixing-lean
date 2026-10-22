import AES8.Math.PaperSymbolicMinors00
import AES8.Math.PaperSymbolicMinors10
import AES8.Math.PaperSymbolicMinors20
import AES8.Math.PaperSymbolicMinors30
import AES8.Math.PaperSymbolicMinors40
import AES8.Math.PaperSymbolicMinors50
import AES8.Math.PaperSymbolicMinors60

noncomputable section
namespace AES8.PaperSymbolicMDS
open Polynomial PaperSymbolicDiffusion PaperSymbolicSlopeTable
open scoped Matrix BigOperators CharTwo
set_option autoImplicit false
set_option maxRecDepth 8192

/-- Every physical information determinant is nonzero and has degree at most three. -/
theorem information_minors (s : InformationSet) :
    (infoMatrix (X : P) s).det ≠ 0 ∧ (infoMatrix (X : P) s).det.natDegree ≤ 3 := by
  obtain ⟨i, rfl⟩ := informationSets_surjective s
  by_cases h0 : i.val < 10
  · let k : Fin 10 := ⟨i.val-0, by omega⟩
    have hk : (⟨0+k.val, by omega⟩ : Fin 70) = i := Fin.ext (by dsimp [k]; omega)
    rw [← hk]
    exact information_minors_0 k
  by_cases h10 : i.val < 20
  · let k : Fin 10 := ⟨i.val-10, by omega⟩
    have hk : (⟨10+k.val, by omega⟩ : Fin 70) = i := Fin.ext (by dsimp [k]; omega)
    rw [← hk]
    exact information_minors_10 k
  by_cases h20 : i.val < 30
  · let k : Fin 10 := ⟨i.val-20, by omega⟩
    have hk : (⟨20+k.val, by omega⟩ : Fin 70) = i := Fin.ext (by dsimp [k]; omega)
    rw [← hk]
    exact information_minors_20 k
  by_cases h30 : i.val < 40
  · let k : Fin 10 := ⟨i.val-30, by omega⟩
    have hk : (⟨30+k.val, by omega⟩ : Fin 70) = i := Fin.ext (by dsimp [k]; omega)
    rw [← hk]
    exact information_minors_30 k
  by_cases h40 : i.val < 50
  · let k : Fin 10 := ⟨i.val-40, by omega⟩
    have hk : (⟨40+k.val, by omega⟩ : Fin 70) = i := Fin.ext (by dsimp [k]; omega)
    rw [← hk]
    exact information_minors_40 k
  by_cases h50 : i.val < 60
  · let k : Fin 10 := ⟨i.val-50, by omega⟩
    have hk : (⟨50+k.val, by omega⟩ : Fin 70) = i := Fin.ext (by dsimp [k]; omega)
    rw [← hk]
    exact information_minors_50 k
  let k : Fin 10 := ⟨i.val-60, by omega⟩
  have hk : (⟨60+k.val, by omega⟩ : Fin 70) = i := Fin.ext (by dsimp [k]; omega)
  rw [← hk]
  exact information_minors_60 k

end AES8.PaperSymbolicMDS
