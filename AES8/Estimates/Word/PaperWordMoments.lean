import AES8.Estimates.Word.PaperUnsignedHS
import AES8.Reductions.Graph.PaperThreeMarkedPairs
import AESConcrete.SignedThreeAssembly

/-!
# Physical word HS and moments on the printed byte Gram route

Module role: join the unsigned survivor bounds and the signed three-mark
physical estimate, then expose the existing complete degree HS interface.
The signed pair bounds use the repaired per-leg paper route with the exact
left/right physical specialization, including input adjoints. The orthogonal
trace assembly retains its explicit degree-table boundary. Second Gram moments
belong to the separate PaperWordTwoSwaps assembly.
Source candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperWordMoments
open AESMixing AESConcrete
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.MarkedBlockVectorization (Marked)
open AESConcrete.ActualMarkedFrameBound (centeredPattern)
open AESConcrete.HilbertSchmidtEnergy (hs)
open AESConcrete.WordMomentAssembly (residual)
set_option autoImplicit false
set_option maxRecDepth 100000

/-- The common left/right family specializes the repaired per-leg pair route. -/
theorem actual_three_mark_strict (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (hlen : Fintype.card (Marked m) = 3) :
    (4294967296 : ℝ) * hs (centeredPattern left right inverse m)^2 < 22 := by
  apply SignedThreeAssembly.centered_energy_lt_twenty_two left right inverse m hlen
  intro s t
  have h := PaperThreeMarkedPairs.surviving_pair_estimate inverse m
    (ActualMarkedCodeMoment.markedOrientation left right m) hlen
    s.val t.val s.property t.property
  rw [PaperThreeMarkedPairs.physical_scaledPair] at h
  exact h

theorem actual_three_mark_bound (left right : Orientation) (inverse : Bool) :
    ActualUnsignedHS.HasThreeMarkBounds left right inverse := by
  intro m hlen
  exact (actual_three_mark_strict left right inverse m hlen).le

/-- All twenty-five blocks use the owned unsigned/signed providers. -/
theorem actual_degree_hs_bounds (left right : Orientation) (inverse : Bool) :
    WordMomentAssembly.HasDegreeHSBounds left right inverse :=
  PaperUnsignedHS.degree_table_of_three_mark_bounds left right inverse
    (actual_three_mark_bound left right inverse)

theorem actual_trace_bound (left right : Orientation) (inverse : Bool) :
    (∑ y, ∑ x, residual left right inverse y x ^ 2) < 4251 / 4294967296 :=
  WordMomentAssembly.trace_lt_of_degree_bounds left right inverse
    (actual_degree_hs_bounds left right inverse)

#print axioms actual_three_mark_strict
#print axioms actual_degree_hs_bounds
#print axioms actual_trace_bound
end AES8.PaperWordMoments
