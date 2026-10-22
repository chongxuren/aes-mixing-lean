import AES8.Recurrence.PaperComparisonMaps

/-! Exact rational margins for the current four-round component proof.
These are scalar consequences of the paper's source-energy formulas. The
actual-source inequalities are separate hypotheses in the later adapter. -/
namespace AES8.PaperStartupScalars
open PaperComparison
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def collision : ℚ := 17/(15*q)
def point : ℚ := 14/q
def columnEnergy : ℚ := 2/(15*q)
def normSquared : ℚ := (52/(5*65536))^2

/-- Squared Q^(5/2)-scaled positive-residual bound, eq. initial-residual. -/
def residualSquared (i t w : ℕ) : ℚ :=
  let z := 4-t
  let k := min (w-z) i
  (positionCount i t : ℚ) * q^5 * (1/(q-1))^(t-i) * point^(2*z) *
    (collision*normSquared)^k * columnEnergy^(i-k)

/-- Capped-source common bound for full support and degree at least two. -/
def commonSquared (i : ℕ) : ℚ :=
  (Nat.choose 4 i : ℚ) * (q/(q-1))^(4-i) *
    (2/15)^(i-2) * (17640000/q)

def allowance (c : Fin 14) : ℚ := 900*scales c*startup0 c

theorem proper_residual_allowance (c : Fin 14) (w : Fin 5)
    (hi : 0 < (typeOf c).1) (ht : (typeOf c).2 < 4)
    (hw : 4-(typeOf c).2 < w.val) :
    residualSquared (typeOf c).1 (typeOf c).2 w.val ≤ allowance c^2 := by
  fin_cases c <;> fin_cases w
  all_goals first
    | (exfalso; revert hi ht hw; decide)
    | decide +kernel

theorem full_degree_one_allowance (w : Fin 5) (hw : 0 < w.val) :
    residualSquared 1 4 w.val ≤ allowance 7^2 := by
  fin_cases w
  all_goals first
    | (exfalso; revert hw; decide)
    | decide +kernel

theorem several_full_le_common (i : Fin 5) (w : Fin 5)
    (hi : 2 ≤ i.val) (hw : 2 ≤ w.val) :
    residualSquared i.val 4 w.val ≤ commonSquared i.val := by
  fin_cases i <;> fin_cases w
  all_goals first
    | (exfalso; revert hi hw; decide)
    | decide +kernel

theorem common_allowance (c : Fin 14)
    (hi : 2 ≤ (typeOf c).1) (ht : (typeOf c).2 = 4) :
    commonSquared (typeOf c).1 ≤ allowance c^2 := by
  fin_cases c
  all_goals first
    | (exfalso; revert hi ht; decide)
    | decide +kernel

def properActivitySquared (t : ℕ) : ℚ :=
  (Nat.choose 4 t : ℚ) * q^5 * (collision*point^(3-t))^2 / (q-1)^t

def fullActivitySquared : ℚ := q^5 * (4*collision)^2 / (q-1)^4

theorem proper_activity_allowance (c : Fin 14)
    (hi : (typeOf c).1 = 0) (ht : (typeOf c).2 < 4) :
    properActivitySquared (typeOf c).2 ≤ allowance c^2 := by
  fin_cases c
  all_goals first
    | (exfalso; revert hi ht; decide)
    | decide +kernel

theorem full_activity_allowance : fullActivitySquared ≤ allowance 3^2 := by decide +kernel

theorem allowance_pos (c : Fin 14) : 0 < allowance c := by
  fin_cases c <;> decide +kernel

end AES8.PaperStartupScalars
