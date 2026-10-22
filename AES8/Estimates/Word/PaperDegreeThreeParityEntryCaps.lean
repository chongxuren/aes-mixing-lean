import AES8.Estimates.Word.PaperDegreeThreeParityResponse

/-! The paper's comparable/noncomparable mixed-parity entry caps.
All displayed decimal constants are exact rationals. The bounds are transferred
from the actual physical Gram intervals, including the positive comparable
slack sign; the desired operator bound is not supplied as a premise. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeThreeParityEntryCaps
open AESMixing AESMixing.AES AESConcrete
open AESConcrete.ActivityEffectiveMetric AESConcrete.ActivityGramDominance
open PaperDegreeThreeParityCounts PaperDegreeThreeParityResponse
set_option autoImplicit false
set_option maxRecDepth 100000

def Comparable (A B : Fin 16) : Prop :=
  maskSize (maskIntersection A B) = min (maskSize A) (maskSize B)
instance (A B : Fin 16) : Decidable (Comparable A B) := inferInstanceAs (Decidable (_ = _))

def comparableCap : ℝ := comparisonLambda*(xi-xi^3) -
  (1024/255)*((185/10000)-xi*(305/100000))
def noncomparableCap : ℝ := comparisonLambda*xi^5 +
  (1024/255)*((53/1000)+xi*(23/1000))

theorem cap_arithmetic :
    crossRadius 1 2 1 ≤ comparableCap ∧
    crossRadius 3 2 2 ≤ comparableCap ∧
    crossRadius 1 2 0 ≤ noncomparableCap ∧
    crossRadius 3 2 1 ≤ noncomparableCap ∧
    0 < comparisonLambda*sizeMetric 1 2 1 - (sizeInterval 1 2 1).2 ∧
    0 < comparisonLambda*sizeMetric 3 2 2 - (sizeInterval 3 2 2).2 ∧
    comparableCap+noncomparableCap < (5/6 : ℝ) := by
  norm_num [comparableCap, noncomparableCap, crossRadius, sizeMetric, sizeInterval,
    ActivityPairIntervals.scaleInterval, ActivityPairIntervals.compressedInterval,
    ActivityPairIntervals.concreteResources, ActivityPairIntervals.frameFactor,
    ActivityPairIntervals.xi, xi, comparisonLambda, ByteLineBounds.a3,
    ByteLineBounds.cubeBound, ByteGramResources.cubeNumerator, ByteLineBounds.b3,
    ByteLineBounds.mixedCubeBound, LineOverlap.eta1, LineOverlap.eta2,
    LineOverlap.delta, LineOverlap.offdiag, MixedCodeBounds.f3,
    ContainmentCodeBounds.z3, ContainmentCodeBounds.h3]

theorem cross_size_cases (A : Odd) (B : Even) :
    (maskSize A.val = 1 ∧ maskSize (maskIntersection A.val B.val) = 0) ∨
    (maskSize A.val = 1 ∧ maskSize (maskIntersection A.val B.val) = 1) ∨
    (maskSize A.val = 3 ∧ maskSize (maskIntersection A.val B.val) = 1) ∨
    (maskSize A.val = 3 ∧ maskSize (maskIntersection A.val B.val) = 2) := by
  have hp := ActivityPairIntervals.mask_parameters A.val B.val
  have hB := B.property
  have hA := A.property
  unfold IsOdd at hA
  unfold IsEven at hB
  omega

theorem cross_entry_caps (G : Fin 16 → Fin 16 → ℝ) (hG : EntryBounds G)
    (A : Odd) (B : Even) :
    (Comparable A.val B.val →
      0 < residualEntry G A.val B.val ∧ |residualEntry G A.val B.val| ≤ comparableCap) ∧
    (¬ Comparable A.val B.val → |residualEntry G A.val B.val| ≤ noncomparableCap) := by
  have hr := residual_abs_le_offRadius G hG
    ⟨A.val, odd_interior A⟩ ⟨B.val, even_interior B⟩
  rw [offRadius_eq] at hr
  have hu := (hG ⟨A.val, odd_interior A⟩ ⟨B.val, even_interior B⟩).2
  change G A.val B.val ≤ (sizeInterval (maskSize A.val) (maskSize B.val)
    (maskSize (maskIntersection A.val B.val))).2 at hu
  have hm : effectiveMetric A.val B.val = sizeMetric (maskSize A.val)
      (maskSize B.val) (maskSize (maskIntersection A.val B.val)) := by
    rw [effectiveMetric_formula]
    rfl
  have hB : maskSize B.val = 2 := B.property
  rcases cross_size_cases A B with ⟨hA,hj⟩ | ⟨hA,hj⟩ | ⟨hA,hj⟩ | ⟨hA,hj⟩
  all_goals rw [hA,hB,hj] at hr hu hm
  all_goals simp only [Comparable, hA, hB, hj, Nat.min_eq_left (by omega : 1 ≤ 2),
    Nat.min_eq_right (by omega : 2 ≤ 3)]
  · constructor
    · intro h; norm_num at h
    · intro _; exact hr.trans cap_arithmetic.2.2.1
  · constructor
    · intro _
      refine ⟨?_, hr.trans cap_arithmetic.1⟩
      have hp := cap_arithmetic.2.2.2.2.1
      unfold residualEntry
      rw [hm]
      linarith
    · intro h; exact (h True.intro).elim
  · constructor
    · intro h; norm_num at h
    · intro _; exact hr.trans cap_arithmetic.2.2.2.1
  · constructor
    · intro _
      refine ⟨?_, hr.trans cap_arithmetic.2.1⟩
      have hp := cap_arithmetic.2.2.2.2.2.1
      unfold residualEntry
      rw [hm]
      linarith
    · intro h; exact (h True.intro).elim

theorem actual_cross_entry_caps (left right : ByteOrientations.Orientation)
    (inverse : Bool) (A : Odd) (B : Even) :
    (Comparable A.val B.val →
      0 < residualEntry (ActualDegreeThreeGram.degreeThreeGram left right inverse)
        A.val B.val ∧
      |residualEntry (ActualDegreeThreeGram.degreeThreeGram left right inverse)
        A.val B.val| ≤ comparableCap) ∧
    (¬ Comparable A.val B.val →
      |residualEntry (ActualDegreeThreeGram.degreeThreeGram left right inverse)
        A.val B.val| ≤ noncomparableCap) :=
  cross_entry_caps _ (PaperDegreeThreeGramPrinted.actual_entry_bounds left right inverse) A B

end AES8.PaperDegreeThreeParityEntryCaps
