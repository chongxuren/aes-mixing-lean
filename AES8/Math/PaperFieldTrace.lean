import Mathlib.RingTheory.Trace.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import AESMixing.CharacterGram
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.CharP.Two

/-! The absolute trace character on arbitrary finite characteristic-two fields.
Concrete AES trace identification is kept in its separate model module. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperFieldTrace
open AESMixing
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

def trace (x : F) : ZMod 2 := Algebra.trace (ZMod 2) F x

theorem trace_zero : trace (0 : F) = 0 := map_zero _

theorem trace_add (x y : F) : trace (x+y) = trace x+trace y := map_add _ x y

theorem trace_nonzero : ∃ w : F, trace w ≠ 0 := by
  have h := (traceForm_nondegenerate (ZMod 2) F).1 (1 : F)
  simp only [Algebra.traceForm_apply, one_mul] at h
  by_contra! hn
  exact one_ne_zero (h hn)

def character (x : F) : ℝ := if trace x=0 then 1 else -1

theorem character_zero : character (0 : F) = 1 := by simp [character, trace_zero]

theorem character_add (x y : F) : character (x+y) = character x*character y := by
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hcases (trace x) with hx | hx <;>
    rcases hcases (trace y) with hy | hy <;>
    simp [character, trace_add, hx, hy, CharTwo.add_self_eq_zero]

theorem character_witness : ∃ w : F, character w = -1 := by
  obtain ⟨w,hw⟩ := trace_nonzero (F := F)
  exact ⟨w, by simp [character, hw]⟩

theorem character_sum : (∑ x : F, character x) = 0 := by
  obtain ⟨w,hw⟩ := character_witness (F := F)
  exact real_character_sum_zero character character_add w hw

theorem trace_polynomial (x : F) :
    algebraMap (ZMod 2) F (trace x) =
      ∑ i ∈ Finset.range (Module.finrank (ZMod 2) F), x^(2^i) := by
  -- Specialization of Mathlib's finite-field trace formula at its pinned revision.
  -- Its proof uses the complete Frobenius enumeration of field automorphisms.
  unfold trace
  rw [trace_eq_sum_automorphisms, Finset.sum_range]
  exact Eq.symm <| Fintype.sum_bijective _
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod 2) F) _ _
    (fun i => by rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]; simp)

theorem trace_sq (x : F) : trace (x^2) = trace x := by
  simpa [trace, FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using
    (Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) x)

theorem trace_artin_schreier (x : F) : trace (x^2+x) = 0 := by
  rw [trace_add, trace_sq, CharTwo.add_self_eq_zero]

end AES8.PaperFieldTrace
