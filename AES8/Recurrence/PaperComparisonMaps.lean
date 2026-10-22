import AES8.Recurrence.PaperComparisonGraphs

/-!
# Literal rational comparison maps and current startup data

Frozen paper f902bb94, eqs. rational-activity-bound,
rational-component-bounds, maps and parity-initial-profiles.
No Historical/Data matrix or historical startup is imported here.
The rational maps require separate physical block-norm instantiation.
-/
open scoped BigOperators
namespace AES8.PaperComparison

def typeOf : Fin 14 → ℕ × ℕ :=
  ![(0,1),(0,2),(0,3),(0,4),(1,1),(1,2),(1,3),(1,4),
    (2,2),(2,3),(2,4),(3,3),(3,4),(4,4)]
def scales : QProfile :=
  ![815/1000,1,815/1000,815/32768000,247/100000,138/100000,
    138/100000,247/100000,243/1000000,178/1000000,243/1000000,
    189/10000000,189/10000000,777/10000000000]
def firstReturn : QProfile := ![1,3,450,450,1,25,900,15000,1,25,450,2,10,5]
def startup0 : QProfile := ![1,1,1,1,1,1,1,10,1,1,1,1,3,130]
def evenEnvelope : QProfile := ![342,45,39,39,133,74,81,39,37,163,97,37,316,179]
def oddEnvelope : QProfile := ![76,130,30,30,528,64,49,44,48,51,56,29,73,90]
def ratioPermille : QProfile := ![985,983,978,978,989,949,949,962,975,973,986,978,979,982]

/-- Exact-support activity-count polynomials, eq. activity-support-counts. -/
def activityCount : ℕ → ℚ
  | 0 => 1
  | 5 => q-1
  | 6 => (q-1)*(q-5)
  | 7 => (q-1)*(q^2-6*q+15)
  | 8 => (q-1)*(q^3-7*q^2+21*q-35)
  | _ => 0

def activityBound (t w : ℕ) : ℚ :=
  rootUpper (Nat.choose 4 t) * rootUpper (Nat.choose 4 w) *
    eta^(t+w) * qp (2-(t:ℤ)-w) *
    |activityCount (t+w) - (q-1)^(t+w)/(q^4-1)|

def activityInput : ℕ → ℚ
  | 1 => 0
  | 2 => 389/10000
  | 3 => 134/10000
  | 4 => 1728/1000000
  | _ => 0

def stepComponent (i t j w : ℕ) : ℚ :=
  if i = 0 ∧ j = 0 then activityBound t w
  else if j = 0 then min (support i t j w stepGraph) (activityInput i / q)
  else support i t j w stepGraph

/-- Paper's step comparison matrix, with zero high-degree input columns. -/
def stepMatrix (alpha beta : Fin 14) : ℚ :=
  let (i,t) := typeOf alpha
  let (j,w) := typeOf beta
  if j ≤ 2 then 512 * (scales beta/scales alpha) * stepComponent i t j w else 0

/-- Paper's return comparison matrix, in Q^3-scaled graph units. -/
def returnMatrix (alpha beta : Fin 14) : ℚ :=
  let (i,t) := typeOf alpha
  let (j,w) := typeOf beta
  (1/16384) * (scales beta/scales alpha) * support i t j w returnGraph

def mv (m : QMatrix) (x : QProfile) : QProfile := fun i => ∑ j, m i j * x j

def startup1 : QProfile := mv stepMatrix startup0 + firstReturn
def startup2 : QProfile := mv stepMatrix startup1 + mv returnMatrix startup0
def startup3 : QProfile := mv stepMatrix startup2 + mv returnMatrix startup1
def invariantEven : QProfile := mv stepMatrix oddEnvelope + mv returnMatrix evenEnvelope
def invariantOdd : QProfile := mv stepMatrix evenEnvelope + mv returnMatrix oddEnvelope

theorem scales_pos (i : Fin 14) : 0 < scales i := by
  fin_cases i <;> norm_num [scales]
theorem envelopes_pos (i : Fin 14) : 0 < evenEnvelope i ∧ 0 < oddEnvelope i := by
  fin_cases i <;> norm_num [evenEnvelope, oddEnvelope]
theorem ratioPermille_lt (i : Fin 14) : ratioPermille i < 990 := by
  fin_cases i <;> norm_num [ratioPermille]
theorem step_high_columns (i : Fin 14) (j : Fin 3) :
    stepMatrix i (⟨j.val+11, by omega⟩ : Fin 14) = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [stepMatrix, typeOf]

end AES8.PaperComparison
