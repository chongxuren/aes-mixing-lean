import AES8.Recurrence.PaperFirstReturnComparison

/-!
# Literal real first-return comparisons

Frozen paper f902bb94, eq. aesasm-first-return-targets and lem. finite-comparisons.
The coefficient below uses the Q^3-scaled return graph and a fixed input support.
The only position factor is sqrt(positionCount(i,t) * choose(1,j)); in particular,
there is no choice of an input support among four positions.  The rounded roots
are upper bounds, never identities.  This module supplies scalar comparisons;
physical source lengths and the all-bit entry premise are separate obligations.
-/
noncomputable section
namespace AES8.PaperFirstReturnReal
open AESMixing PaperComparison PaperExactSupportLift PaperRationalSupportLift
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- The literal Q^3-scaled fixed-input-support coefficient C^[1]_{alpha,j}. -/
def coefficient (i t j : ℕ) : ℝ :=
  Real.sqrt ((positionCount i t : ℝ) * (Nat.choose 1 j : ℝ)) *
    Real.sqrt (PaperComparison.eta : ℝ) ^ (t-i+(1-j)) *
      (PaperComparison.supportSum i t j 1 returnGraph : ℝ)

theorem q_cube_pos : 0 < (PaperComparison.q : ℝ)^3 := by
  norm_num [PaperComparison.q]

/-- The literal coefficient is Q^3 times the unscaled fixed-support lift.
The displayed root retains only the output multiplicity and choose(1,j). -/
theorem coefficient_eq_scaled_fixedBound (i t : ℕ) (j : Fin 2) :
    coefficient i t j.val =
      (PaperComparison.q : ℝ)^3 *
        (fixedBound AES.Word i t j.val 1
            (PaperAESSupportReturnBound.graphCap i j.val) *
          Real.sqrt ((positionCount i t : ℝ) * (Nat.choose 1 j.val : ℝ))) := by
  have hj : j.val ≤ 1 := by omega
  unfold coefficient fixedBound PaperAESSupportReturnBound.graphCap
  rw [supportSum_div, supportSum_cast i t j.val 1 hj, eta_eq]
  let r := Real.sqrt ((positionCount i t : ℝ) * (Nat.choose 1 j.val : ℝ))
  let p := Real.sqrt (PaperComparison.eta : ℝ) ^ (t-i+(1-j.val))
  let s : ℝ := (PaperComparison.supportSum i t j.val 1 returnGraph : ℝ)
  change r*p*s = (PaperComparison.q : ℝ)^3 *
    ((p * (s / (PaperComparison.q : ℝ)^3)) * r)
  calc
    r*p*s = r*p*((s / (PaperComparison.q : ℝ)^3) *
        (PaperComparison.q : ℝ)^3) := by
      rw [div_mul_cancel₀ _ (ne_of_gt q_cube_pos)]
    _ = _ := by ring

theorem coefficient_nonneg (i t j : ℕ) : 0 ≤ coefficient i t j := by
  unfold coefficient
  apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
  exact supportSum_nonneg i t j 1 returnGraph
    (fun a b => returnGraph_nonneg i a j b)

/-- Cast the independently checked rational fixed-support coefficient cap. -/
theorem coefficient_le (i t : Fin 5) (j : Fin 2) :
    coefficient i.val t.val j.val ≤
      (PaperOneSourceReturn.coefficient i.val t.val j.val : ℝ) := by
  rw [coefficient_eq_scaled_fixedBound]
  calc
    _ ≤ (PaperComparison.q : ℝ)^3 *
        ((PaperOneSourceReturn.coefficient i.val t.val j.val : ℝ) /
          (PaperComparison.q : ℝ)^3) := by
      apply mul_le_mul_of_nonneg_left _ q_cube_pos.le
      simpa only [positionCount] using PaperOneSourceReturn.coefficient_le i t j
    _ = ((PaperOneSourceReturn.coefficient i.val t.val j.val : ℝ) /
        (PaperComparison.q : ℝ)^3) * (PaperComparison.q : ℝ)^3 := mul_comm _ _
    _ = _ := div_mul_cancel₀ _ (ne_of_gt q_cube_pos)

theorem q_root_le :
    Real.sqrt ((PaperComparison.q : ℝ) / ((PaperComparison.q : ℝ)-1)) ≤
      (1000001 : ℝ)/1000000 := by
  apply Real.sqrt_le_iff.mpr
  constructor <;> norm_num [PaperComparison.q]

theorem two_fifteenths_root_le :
    Real.sqrt ((2 : ℝ)/15) ≤ (183 : ℝ)/500 := by
  apply Real.sqrt_le_iff.mpr
  constructor <;> norm_num

theorem type_bounds (a : Fin 14) :
    (typeOf a).1 < 5 ∧ (typeOf a).2 < 5 := by
  fin_cases a <;> norm_num [typeOf]

/-- The paper's one-source expression with its exact real roots. -/
def oneSource (a : Fin 14) : ℝ :=
  let (i,t) := typeOf a
  64 / (125 * (scales a : ℝ)) *
    (coefficient i t 0 *
        Real.sqrt ((PaperComparison.q : ℝ) / ((PaperComparison.q : ℝ)-1)) +
      coefficient i t 1 * Real.sqrt ((2 : ℝ)/15))

/-- Literal real one-source comparisons for all fourteen current output types.
This conclusion has no physical entry or source-length hypothesis. -/
theorem one_source_le (a : Fin 14) : oneSource a ≤ (firstReturn a : ℝ) := by
  rcases htype : typeOf a with ⟨i,t⟩
  have hb := type_bounds a
  rw [htype] at hb
  have hc0 := coefficient_le (⟨i,hb.1⟩ : Fin 5) (⟨t,hb.2⟩ : Fin 5) (0 : Fin 2)
  have hc1 := coefficient_le (⟨i,hb.1⟩ : Fin 5) (⟨t,hb.2⟩ : Fin 5) (1 : Fin 2)
  have hterm0 := mul_le_mul hc0 q_root_le (Real.sqrt_nonneg _)
    ((coefficient_nonneg i t 0).trans hc0)
  have hterm1 := mul_le_mul hc1 two_fifteenths_root_le (Real.sqrt_nonneg _)
    ((coefficient_nonneg i t 1).trans hc1)
  have hs : (0 : ℝ) < (scales a : ℝ) := by
    exact_mod_cast scales_pos a
  have hp : 0 ≤ (64 : ℝ)/(125 * (scales a : ℝ)) := by positivity
  have hcast : (PaperFirstReturnComparison.oneSource a : ℝ) ≤ (firstReturn a : ℝ) := by
    exact_mod_cast PaperFirstReturnComparison.one_source_le a
  apply le_trans _ hcast
  simp only [oneSource, PaperFirstReturnComparison.oneSource, htype]
  push_cast
  exact mul_le_mul_of_nonneg_left (add_le_add hterm0 hterm1) hp

/-- Expanded statement matching the one-source part of lem. finite-comparisons. -/
theorem finite_comparisons (a : Fin 14) :
    let (i,t) := typeOf a
    64 / (125 * (scales a : ℝ)) *
      (coefficient i t 0 *
          Real.sqrt ((PaperComparison.q : ℝ) / ((PaperComparison.q : ℝ)-1)) +
        coefficient i t 1 * Real.sqrt ((2 : ℝ)/15)) ≤ (firstReturn a : ℝ) :=
  one_source_le a

end AES8.PaperFirstReturnReal
