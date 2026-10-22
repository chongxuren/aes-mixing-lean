import AES8.Estimates.Word.PaperExceptionalWordBounds
import AES8.Estimates.Word.WordMixedNonexceptionalCap

/-!
# Unconditional one-sided word fourth moments

The actual nonexceptional point cap is joined to the literal exceptional
block identity and support enumeration. All three one-sided fourth-moment
conclusions have no entry, block-identification, or support-count premise.
Constructive only; no attacks, manuscript changes or proof bypasses.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperExceptionalWordFourth
open AESMixing
open AES8.OneSidedWordEnergy (rightMixed)
open AES8.PaperExceptionalWordBounds (exceptionalInputs oneActiveWords
  mem_exceptionalInputs mem_oneActiveWords_iff_support)

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 200000
set_option linter.constructorNameAsVariable false

theorem nonexceptional_entry_lt (adjoint : Bool) (y x : AES.Word)
    (hx : x ∉ exceptionalInputs y) :
    |rightMixed adjoint y x| < (1152 / 4294967296 : ℝ) := by
  classical
  refine AES8.WordMixedNonexceptionalCap.rightMixed_lt adjoint x y ?_
  intro h
  have hxone : x ∈ oneActiveWords := (mem_oneActiveWords_iff_support x).mpr h.1
  have hyone : y ∈ oneActiveWords := (mem_oneActiveWords_iff_support y).mpr h.2
  apply hx
  rw [mem_exceptionalInputs]
  exact ⟨hyone, hxone⟩

theorem row_fourth_lt (adjoint : Bool) (y : AES.Word) :
    (∑ x, rightMixed adjoint y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) :=
  AES8.PaperExceptionalWordBounds.row_fourth_lt adjoint y
    (fun x hx => (nonexceptional_entry_lt adjoint y x hx).le)

theorem column_fourth_lt (adjoint : Bool) (x : AES.Word) :
    (∑ y, rightMixed adjoint y x ^ 4) <
      (2100 / 4294967296 : ℝ) ^ 2 * (2 / (15 * 4294967296)) := by
  classical
  apply AES8.PaperExceptionalWordBounds.column_fourth_lt adjoint x
  intro y hy
  apply le_of_lt
  apply AES8.WordMixedNonexceptionalCap.rightMixed_lt adjoint x y
  intro h
  have hxone : x ∈ oneActiveWords := (mem_oneActiveWords_iff_support x).mpr h.1
  have hyone : y ∈ oneActiveWords := (mem_oneActiveWords_iff_support y).mpr h.2
  apply hy
  rw [mem_exceptionalInputs]
  exact ⟨hxone, hyone⟩

theorem total_fourth_lt (adjoint : Bool) :
    (∑ y, ∑ x, rightMixed adjoint y x ^ 4) <
      (1200 / 4294967296 : ℝ) ^ 2 * (4251 / 4294967296) :=
  AES8.PaperExceptionalWordBounds.total_fourth_lt adjoint
    (fun y x hx => (nonexceptional_entry_lt adjoint y x hx).le)

end AES8.PaperExceptionalWordFourth
