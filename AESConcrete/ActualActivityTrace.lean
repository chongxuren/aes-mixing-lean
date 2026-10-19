import AESConcrete.ActivityTrace
import AESConcrete.ActivityTraceNumbers
import AESConcrete.WordMomentNumbers
import AESMixing.Generated.GramTable_F
import AESMixing.Generated.GramTable_I

/-!
# Exact centered AES activity trace

The semantic inverse-frame trace and the rational scalar evaluation meet
here. Both diffusion directions and independently chosen byte orientations
are included. This supplies only the degree-(0,0) HS resource; it does not
assert the remaining degree table or the whole-word trace/Gram targets.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualActivityTrace
open AESMixing
open ByteOrientations (Orientation)
open WordOrientationClosure (wordKernel)
open HilbertSchmidtEnergy (hs hs_sq)

theorem traceForm_cast (N : Fin 16 → Fin 16 → ℤ) :
    ActivityTrace.traceForm (fun a b => (N a b : ℝ)/255^4) =
      ((∑ a : Fin 16, ∑ b : Fin 16, ActivityTraceNumbers.traceEntry N a b : ℚ) : ℝ) := by
  simp only [ActivityTrace.traceForm, ActivityTrace.maskInverse, Rat.cast_sum]
  simp_rw [ActivityTraceNumbers.traceEntry_cast]

theorem raw_trace_exact (inverse : Bool) :
    ActivityTrace.traceForm (ActivityTrace.rawActivityGram inverse) =
      (68*256^2+264*256+68 : ℝ)/255^6 := by
  cases inverse
  · have he : ActivityTrace.rawActivityGram false =
        fun a b => (GramNumeric.F0.numerator a b : ℝ)/255^4 := by
      funext a b
      exact GramTable.F.numeric_entries_0 a b
    rw [he, traceForm_cast, ActivityTraceNumbers.forward_trace_number]
    norm_num
  · have he : ActivityTrace.rawActivityGram true =
        fun a b => (GramNumeric.I0.numerator a b : ℝ)/255^4 := by
      funext a b
      exact GramTable.I.numeric_entries_0 a b
    rw [he, traceForm_cast, ActivityTraceNumbers.inverse_trace_number]
    norm_num

theorem degree_zero_trace_exact (left right : Orientation) (inverse : Bool) :
    hs (DegreeHilbertSchmidt.block 0 (residualMatrix (wordKernel left right inverse) 0) 0 0)^2 =
      (68*256^2+264*256+68 : ℝ)/255^6 := by
  rw [ActivityTrace.actual_degree_zero_trace, raw_trace_exact]

theorem degree_zero_trace_scaled_lt (left right : Orientation) (inverse : Bool) :
    (4294967296 : ℝ) *
      hs (DegreeHilbertSchmidt.block 0 (residualMatrix (wordKernel left right inverse) 0) 0 0)^2 < 71 := by
  rw [degree_zero_trace_exact]
  norm_num

theorem degree_zero_hs_table (left right : Orientation) (inverse : Bool) :
    hs (DegreeHilbertSchmidt.block 0 (residualMatrix (wordKernel left right inverse) 0) 0 0) ≤
      WordMomentNumbers.hs 0 0 / 65536 := by
  apply (sq_le_sq₀ (HilbertSchmidtEnergy.hs_nonneg _)
    (by norm_num [WordMomentNumbers.hs])).mp
  rw [degree_zero_trace_exact]
  norm_num [WordMomentNumbers.hs]

end AESConcrete.ActualActivityTrace
