import AESConcrete.ActivityFrame
import AESConcrete.ByteLineBounds
import AESConcrete.MixedCodeBounds
import AESConcrete.ContainmentCodeBounds
import Mathlib.Tactic.IntervalCases

/-!
# Finite inverse-frame combination of activity pair intervals

The hypotheses are local pair intervals for five-position activity choices.
Only total choice weights two and three survive.  Combining the four Bool
output-frame entries with the actual byte inverse metric gives the nine
compressed intervals.  This conditional finite analysis is separate from
the actual AES activity-label/shortening correspondence and word assembly.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityPairIntervals
open AESMixing
open AESMixing.AES (maskSize)

def xi : ℝ := 1 / 16
def frameFactor : ℝ := 256 / 255

/-- Keep the finite combination independent of the numerical resource proof. -/
structure Resources where
  a3 : ℝ
  eta1 : ℝ
  eta2 : ℝ
  z3 : ℝ
  h3 : ℝ
  f3 : ℝ
  b3 : ℝ

def concreteResources : Resources where
  a3 := ByteLineBounds.a3
  eta1 := LineOverlap.eta1
  eta2 := LineOverlap.eta2
  z3 := ContainmentCodeBounds.z3
  h3 := ContainmentCodeBounds.h3
  f3 := MixedCodeBounds.f3
  b3 := ByteLineBounds.b3

def inInterval (I : ℝ × ℝ) (x : ℝ) : Prop := I.1 ≤ x ∧ x ≤ I.2
def scaleInterval (c : ℝ) (I : ℝ × ℝ) : ℝ × ℝ := (c*I.1, c*I.2)
def boolBit (b : Bool) : ℕ := if b then 1 else 0

/-- The permitted local pair table. For valid five-position choices,
equal weights and full intersection mean the same choice. All unsupported
weights vanish. Invalid size/intersection triples also receive zero here;
they are never needed in the combination theorem's valid parameter range. -/
def pairInterval (R : Resources) (w v j : ℕ) : ℝ × ℝ :=
  if (w = 2 ∨ w = 3) ∧ (v = 2 ∨ v = 3) then
    if w = v then
      if j = w then (0, R.a3)
      else if j+1 = w then (-R.eta1, R.eta1)
      else if j+2 = w then (-R.eta2, R.eta2)
      else (0, 0)
    else if j = 2 then (R.z3-R.h3, R.z3+R.h3)
    else if j = 1 then (-R.f3, R.f3)
    else if j = 0 then (-R.b3, R.b3)
    else (0, 0)
  else (0, 0)

/-- Nine base cases, with transposition and simultaneous complement cases
listed explicitly. The complement intersection uses (4+j)-(w+v), not an
iterated truncated subtraction. No equality of complemented pair values
is asserted by this endpoint table. -/
def compressedInterval (R : Resources) : ℕ → ℕ → ℕ → ℝ × ℝ
  | 1, 1, 1 | 3, 3, 3 => (0, R.a3)
  | 1, 1, 0 | 3, 3, 2 => (-R.eta1, R.eta1)
  | 1, 2, 1 | 2, 1, 1 | 2, 3, 2 | 3, 2, 2 =>
      (R.z3-R.h3-xi*R.eta1, R.z3+R.h3+xi*R.eta1)
  | 1, 2, 0 | 2, 1, 0 | 2, 3, 1 | 3, 2, 1 =>
      (-(R.f3+xi*R.eta2), R.f3+xi*R.eta2)
  | 1, 3, 1 | 3, 1, 1 => (-xi*R.f3, xi*R.f3)
  | 1, 3, 0 | 3, 1, 0 => (-xi*R.b3, xi*R.b3)
  | 2, 2, 2 => (-2*xi*(R.z3+R.h3), 2*R.a3-2*xi*(R.z3-R.h3))
  | 2, 2, 1 => (-(2*R.eta1+2*xi*R.f3), 2*R.eta1+2*xi*R.f3)
  | 2, 2, 0 => (-(2*R.eta2+2*xi*R.b3), 2*R.eta2+2*xi*R.b3)
  | _, _, _ => (0, 0)

def reducedCompression (p : Bool → Bool → ℝ) : ℝ :=
  p false false + p true true - xi*(p false true + p true false)

def inverseCompression (p : Bool → Bool → ℝ) : ℝ :=
  ∑ b : Bool, ∑ c : Bool, ActivityFrame.byteInverse b c * p b c

/-- The exact inverse metric has negative off-diagonal coefficients. -/
theorem inverseCompression_eq (p : Bool → Bool → ℝ) :
    inverseCompression p = frameFactor*reducedCompression p := by
  simp [inverseCompression, ActivityFrame.byteInverse, frameFactor, reducedCompression, xi]
  ring

/-- Complete finite combination theorem. Its premises are the four local
pair bounds, not the desired compressed bounds. The numeric case split is
only over subset sizes in {0,...,4}, never over byte values or code points. -/
theorem reducedCompression_mem
    (R : Resources) (w v j : ℕ) (hw : w ≤ 4) (hv : v ≤ 4)
    (hjw : j ≤ w) (hjv : j ≤ v) (hunion : w+v ≤ 4+j)
    (p : Bool → Bool → ℝ)
    (hp : ∀ b c, inInterval
      (pairInterval R (w+boolBit b) (v+boolBit c) (j+boolBit (b && c))) (p b c)) :
    inInterval (compressedInterval R w v j) (reducedCompression p) := by
  rcases hp false false with ⟨h00l, h00u⟩
  rcases hp false true with ⟨h01l, h01u⟩
  rcases hp true false with ⟨h10l, h10u⟩
  rcases hp true true with ⟨h11l, h11u⟩
  have hj : j ≤ 4 := le_trans hjw hw
  interval_cases w <;> interval_cases v <;> interval_cases j
  all_goals try omega
  all_goals
    norm_num [inInterval, pairInterval, compressedInterval, boolBit, reducedCompression, xi]
      at h00l h00u h01l h01u h10l h10u h11l h11u ⊢
  all_goals constructor <;> linarith

/-- All nine intervals with the actual positive inverse-frame factor. -/
theorem inverseCompression_mem
    (R : Resources) (w v j : ℕ) (hw : w ≤ 4) (hv : v ≤ 4)
    (hjw : j ≤ w) (hjv : j ≤ v) (hunion : w+v ≤ 4+j)
    (p : Bool → Bool → ℝ)
    (hp : ∀ b c, inInterval
      (pairInterval R (w+boolBit b) (v+boolBit c) (j+boolBit (b && c))) (p b c)) :
    inInterval (scaleInterval frameFactor (compressedInterval R w v j))
      (inverseCompression p) := by
  rcases reducedCompression_mem R w v j hw hv hjw hjv hunion p hp with ⟨hl, hu⟩
  rw [inverseCompression_eq]
  constructor
  · exact mul_le_mul_of_nonneg_left hl (by norm_num [frameFactor])
  · exact mul_le_mul_of_nonneg_left hu (by norm_num [frameFactor])

theorem compressedInterval_swap (R : Resources) (w v j : ℕ)
    (hw : w ≤ 4) (hv : v ≤ 4) (hj : j ≤ 4) :
    compressedInterval R v w j = compressedInterval R w v j := by
  interval_cases w <;> interval_cases v <;> interval_cases j <;> rfl

/-- Simultaneous complementation is an equality of the interval rules.
It is not an assumed equality between the underlying pair quantities. -/
theorem compressedInterval_complement (R : Resources) (w v j : ℕ)
    (hw : w ≤ 4) (hv : v ≤ 4) (hjw : j ≤ w) (hjv : j ≤ v)
    (hunion : w+v ≤ 4+j) :
    compressedInterval R (4-w) (4-v) ((4+j)-(w+v)) = compressedInterval R w v j := by
  have hj : j ≤ 4 := le_trans hjw hw
  interval_cases w <;> interval_cases v <;> interval_cases j
  all_goals first | omega | rfl

abbrev ActivityLabel := Fin 16 × Bool

def weight (A : Fin 16) (b : Bool) : ℕ := maskSize A + boolBit b

def intersection (A B : Fin 16) (b c : Bool) : ℕ :=
  maskSize (maskIntersection A B) + boolBit (b && c)

/-- Conditional local-pair interface. The actual graph/shortening geometry
must establish this hypothesis separately for its concrete Gram quantities. -/
def PairBounds (R : Resources) (P : ActivityLabel → ActivityLabel → ℝ) : Prop :=
  ∀ (A B : Fin 16) (b c : Bool),
    inInterval (pairInterval R (weight A b) (weight B c) (intersection A B b c))
      (P (A, b) (B, c))

def compressedPair (P : ActivityLabel → ActivityLabel → ℝ) (A B : Fin 16) : ℝ :=
  inverseCompression (fun b c => P (A, b) (B, c))

set_option maxRecDepth 100000 in
theorem mask_parameters : ∀ A B : Fin 16,
    maskSize A ≤ 4 ∧ maskSize B ≤ 4 ∧
      maskSize (maskIntersection A B) ≤ maskSize A ∧
      maskSize (maskIntersection A B) ≤ maskSize B ∧
      maskSize A + maskSize B ≤ 4 + maskSize (maskIntersection A B) := by decide

/-- Generic finite activity-label pair intervals compressed with byteInverse.
One residual triple contributes the frameFactor multiple of the nine-case
table. Summing four triples is a separate assembly obligation. -/
theorem compressedPair_mem (R : Resources) (P : ActivityLabel → ActivityLabel → ℝ)
    (hP : PairBounds R P) (A B : Fin 16) :
    inInterval (scaleInterval frameFactor
      (compressedInterval R (maskSize A) (maskSize B) (maskSize (maskIntersection A B))))
      (compressedPair P A B) := by
  rcases mask_parameters A B with ⟨hw, hv, hjw, hjv, hunion⟩
  exact inverseCompression_mem R _ _ _ hw hv hjw hjv hunion _ (hP A B)

theorem concrete_compressedPair_mem (P : ActivityLabel → ActivityLabel → ℝ)
    (hP : PairBounds concreteResources P) (A B : Fin 16) :
    inInterval (scaleInterval frameFactor
      (compressedInterval concreteResources (maskSize A) (maskSize B)
        (maskSize (maskIntersection A B)))) (compressedPair P A B) :=
  compressedPair_mem concreteResources P hP A B

/-- Actual symmetry of the compressed values requires symmetry of P.
The interval transposition identity above needs no such additional premise. -/
theorem compressedPair_symmetric (P : ActivityLabel → ActivityLabel → ℝ)
    (hP : ∀ a b, P a b = P b a) (A B : Fin 16) :
    compressedPair P A B = compressedPair P B A := by
  unfold compressedPair inverseCompression
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  change ActivityFrame.byteInverse c b * P (A, c) (B, b) =
    ActivityFrame.byteInverse b c * P (B, b) (A, c)
  rw [ActivityFrame.byteInverse_symmetric c b, hP (A, c) (B, b)]

end AESConcrete.ActivityPairIntervals
