import AESMixing.ActivityColumns

/-! The input metric of the sixteen unnormalized support indicators.
The formula is exact and does not treat this spanning family as orthogonal. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES

def maskIntersection (a b : Fin 16) : Fin 16 :=
  ((BitVec.ofFin a : BitVec 4) &&& (BitVec.ofFin b : BitVec 4)).toFin

set_option maxRecDepth 100000 in
theorem maskIntersection_bit : ∀ a b : Fin 16, ∀ i : Fin 4,
    maskBit (maskIntersection a b) i = (maskBit a i && maskBit b i) := by decide

variable {V : Type*} [Zero V]

theorem maskProjection_fixed_iff (a : Fin 16) (x : Fin 4 → V) :
    maskProjection a x = x ↔ ∀ i, maskBit a i ≠ true → x i = 0 := by
  constructor
  · intro h i hi
    have hh := congrFun h i
    simpa [maskProjection, hi] using hh.symm
  · intro h
    funext i
    by_cases hi : maskBit a i = true <;> simp [maskProjection, hi, h i]

theorem maskIntersection_fixed (a b : Fin 16) (x : Fin 4 → V) :
    maskProjection (maskIntersection a b) x = x ↔
      maskProjection a x = x ∧ maskProjection b x = x := by
  simp only [maskProjection_fixed_iff, maskIntersection_bit, ne_eq, Bool.and_eq_true, not_and]
  constructor
  · intro h
    constructor
    · intro i hi
      exact h i (fun ha => (hi ha).elim)
    · intro i hi
      exact h i (fun _ => hi)
  · rintro ⟨ha,hb⟩ i hi
    by_cases hai : maskBit a i = true
    · exact hb i (hi hai)
    · exact ha i hai

variable [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem activityColumn_product (a b : Fin 16) (x : Fin 4 → V) :
    activityColumn a x * activityColumn b x = activityColumn (maskIntersection a b) x := by
  unfold activityColumn
  simp only [maskIntersection_fixed]
  by_cases ha : maskProjection a x = x <;> by_cases hb : maskProjection b x = x <;> simp [ha,hb]

theorem activityColumn_sum (a : Fin 16) :
    (∑ x : Fin 4 → V, activityColumn a x) = (Fintype.card V : ℝ)^maskSize a := by
  simp_rw [activityColumn_as_sum]
  rw [Finset.sum_comm]
  simp [identityKernel, maskCoordinates_card]

theorem activity_gram (a b : Fin 16) :
    gram (fun x : Fin 4 → V => fun a => activityColumn a x) a b =
      (Fintype.card V : ℝ)^maskSize (maskIntersection a b) := by
  unfold gram
  simp_rw [activityColumn_product]
  exact activityColumn_sum _

theorem byte_activity_gram (a b : Fin 16) :
    gram (fun x : Fin 4 → BinaryWord 8 => fun a => activityColumn a x) a b =
      (256 : ℝ)^maskSize (maskIntersection a b) := by
  simpa only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] using
    activity_gram (V := BinaryWord 8) a b

end AESMixing
