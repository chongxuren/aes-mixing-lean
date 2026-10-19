import AESPaper.CappedSourceGram
import AESPaper.LocalAES
import AESPaper.StartingWord
import AESPaper.BoundarySourceCoordinates

/-!
# Actual capped residual responses to one source word

Every residual coordinate uses its own source permutation but retains the
same original source word. The column cap and whole second Gram moment are
supplied by the checked AES resources; arbitrary coordinate maps are never
assumed to preserve individual Gram entries. The source atom cap is proved
for the actual first word law. These are response bounds, prior to inserting
the activity factors and grouping residual-position patterns in the profile.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.OneSourceResidual
open AESMixing AESConcrete
open AESPaper.StartingWord (q wordLaw)

def R : AES.Word → AES.Word → ℝ := residualMatrix AES.wordSuperboxKernel 0

theorem R_column (x : AES.Word) : gram R x x ≤ 2/(15*q) := by
  have h := (LocalAES.local_column_energy false false x).le
  change (∑ y, R y x ^ 2) ≤ 2/(15*q) at h
  simpa only [gram, pow_two] using h

theorem R_moment : (∑ x, ∑ z, gram R x z ^ 2) ≤ (300/q)^2 := by
  exact LocalAES.local_gram_moment false false

/-- All analytic premises of the capped-source theorem are discharged for
actual AES residuals and the actual source law. Width is `n+2`. -/
theorem residual_response_energy (n : ℕ) (e : Fin (n+2) → Equiv.Perm AES.Word)
    (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, WordColumnGram.tensorResponse (fun _ : Fin (n+2) => R)
      (fun x i => e i x) (wordLaw a) y ^ 2) ≤
      (20/q)^2 * (300/q)^2 * (2/(15*q))^n := by
  apply CappedSourceGram.tensorResponse_capped n (fun _ => R) e (wordLaw a)
    (20/q) (300/q) (2/(15*q))
  · norm_num [q]
  · norm_num [q]
  · intro x
    exact (StartingWord.wordLaw_abs_point_lt a x ha).le
  · intro i x
    exact R_column x
  · intro i
    exact R_moment

/-- Each selected physical output word receives the proved forward boundary
permutation of the common source; repeated selections are also permitted. -/
theorem boundary_residual_response_energy (n : ℕ) (k : Fin 4)
    (c : Fin (n+2) → Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, WordColumnGram.tensorResponse (fun _ : Fin (n+2) => R)
      (fun x i => BoundarySourceCoordinates.outputEquiv k (c i) x) (wordLaw a) y ^ 2) ≤
      (20/q)^2 * (300/q)^2 * (2/(15*q))^n :=
  residual_response_energy n (fun i => BoundarySourceCoordinates.outputEquiv k (c i)) a ha

end AESPaper.OneSourceResidual
