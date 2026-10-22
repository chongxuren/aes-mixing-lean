import AESConcrete.SurvivorRelabel
import AESConcrete.MarkedMomentNumbers

/-!
# Exact unsigned survivor cube evaluations

These finite sums are evaluated after the actual physical-index transport.
All arithmetic is exact; no native decision procedure or oracle is used.
The signed degree-three estimate is a separate mathematical obligation.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.SurvivorCubeNumbers
open SurvivorRelabel

attribute [local instance] Classical.propDecidable
local instance (priority := 10000) (n : ℕ) : DecidableEq (Fin n) :=
  fun a b => Classical.propDecidable (a = b)
set_option maxRecDepth 100000
-- Local build overlay: the finite cube_two calculation exceeds 1.2M heartbeats.
-- Statements and proofs are unchanged; the worker enforces a wall-clock limit.
set_option maxHeartbeats 0

def consEquiv (n : ℕ) : (Fin (n+1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun s := (s 0, fun i => s i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv s := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := by
    rcases p with ⟨b,s⟩
    rfl

theorem sum_cube_succ {M : Type*} [AddCommMonoid M] (n : ℕ) [Fintype (Fin (n+1) → Bool)]
    (f : (Fin (n+1) → Bool) → M) :
    (∑ s, f s) = (∑ t : Fin n → Bool, f (Fin.cons false t)) +
      ∑ t : Fin n → Bool, f (Fin.cons true t) := by
  rw [← (consEquiv n).symm.sum_comp f, Fintype.sum_prod_type]
  simp [consEquiv, Fintype.sum_bool, add_comm]

theorem sum_cube_zero {M : Type*} [AddCommMonoid M]
    [Fintype (Fin 0 → Bool)] (f : (Fin 0 → Bool) → M) : (∑ s, f s) = f (fun i => Fin.elim0 i) := by
  rw [Fintype.sum_unique]
  congr 1

theorem falseCount_eq_sum {I : Type*} [Fintype I] (s : I → Bool) :
    falseCount s = ∑ i, if s i = false then 1 else 0 := by
  classical
  simp [falseCount, Fintype.card_subtype]

theorem falseCount_cons (n : ℕ) (b : Bool) (s : Fin n → Bool) :
    falseCount (Fin.cons b s) = (if b = false then 1 else 0) + falseCount s := by
  simp only [falseCount_eq_sum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem falseCount_zero (s : Fin 0 → Bool) : falseCount s = 0 := by
  simp [falseCount]

theorem frameInverse_cons (n : ℕ) (b c : Bool) (s t : Fin n → Bool) :
    ActivityFrame.frameInverse (Fin.cons b s) (Fin.cons c t) =
      ActivityFrame.byteInverse b c * ActivityFrame.frameInverse s t := by
  simp only [ActivityFrame.frameInverse, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem frameInverse_zero (s t : Fin 0 → Bool) : ActivityFrame.frameInverse s t = 1 := by
  simp [ActivityFrame.frameInverse]

theorem cube_eight : cubeBound (Fin 0) 8 = MarkedMomentNumbers.unsignedCap 8 := by
  norm_num [cubeBound, cubeSurvives, falseCount_cons, falseCount_zero, sum_cube_zero,
    frameInverse_cons, frameInverse_zero, MarkedMomentNumbers.unsignedCap,
    MarkedMomentNumbers.zeta, ActualMarkedContractionEnergy.zeta,
    MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta]

theorem cube_seven : cubeBound (Fin 1) 7 = MarkedMomentNumbers.unsignedCap 7 := by
  norm_num [cubeBound, cubeSurvives, falseCount_cons, falseCount_zero, sum_cube_succ 0, sum_cube_succ 1, sum_cube_succ 2, sum_cube_succ 3,
    sum_cube_succ 4, sum_cube_succ 5, sum_cube_zero,
    frameInverse_cons, frameInverse_zero, ActivityFrame.byteInverse, Fin.sum_univ_succ,
    Fin.prod_univ_succ, MarkedMomentNumbers.unsignedCap,
    MarkedMomentNumbers.zeta, ActualMarkedContractionEnergy.zeta,
    MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta]

theorem cube_six : cubeBound (Fin 2) 6 = MarkedMomentNumbers.unsignedCap 6 := by
  norm_num [cubeBound, cubeSurvives, falseCount_cons, falseCount_zero, sum_cube_succ 0, sum_cube_succ 1, sum_cube_succ 2, sum_cube_succ 3,
    sum_cube_succ 4, sum_cube_succ 5, sum_cube_zero,
    frameInverse_cons, frameInverse_zero, ActivityFrame.byteInverse, Fin.sum_univ_succ,
    Fin.prod_univ_succ, MarkedMomentNumbers.unsignedCap,
    MarkedMomentNumbers.zeta, ActualMarkedContractionEnergy.zeta,
    MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta]

theorem cube_five : cubeBound (Fin 3) 5 = MarkedMomentNumbers.unsignedCap 5 := by
  norm_num [cubeBound, cubeSurvives, falseCount_cons, falseCount_zero, sum_cube_succ 0, sum_cube_succ 1, sum_cube_succ 2, sum_cube_succ 3,
    sum_cube_succ 4, sum_cube_succ 5, sum_cube_zero,
    frameInverse_cons, frameInverse_zero, ActivityFrame.byteInverse, Fin.sum_univ_succ,
    Fin.prod_univ_succ, MarkedMomentNumbers.unsignedCap,
    MarkedMomentNumbers.zeta, ActualMarkedContractionEnergy.zeta,
    MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta]

theorem cube_four : cubeBound (Fin 4) 4 = MarkedMomentNumbers.unsignedCap 4 := by
  norm_num [cubeBound, cubeSurvives, falseCount_cons, falseCount_zero, sum_cube_succ 0, sum_cube_succ 1, sum_cube_succ 2, sum_cube_succ 3,
    sum_cube_succ 4, sum_cube_succ 5, sum_cube_zero,
    frameInverse_cons, frameInverse_zero, ActivityFrame.byteInverse, Fin.sum_univ_succ,
    Fin.prod_univ_succ, MarkedMomentNumbers.unsignedCap,
    MarkedMomentNumbers.zeta, ActualMarkedContractionEnergy.zeta,
    MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta]

theorem cube_two : cubeBound (Fin 6) 2 = MarkedMomentNumbers.unsignedCap 2 := by
  norm_num [cubeBound, cubeSurvives, falseCount_cons, falseCount_zero, sum_cube_succ 0, sum_cube_succ 1, sum_cube_succ 2, sum_cube_succ 3,
    sum_cube_succ 4, sum_cube_succ 5, sum_cube_zero,
    frameInverse_cons, frameInverse_zero, ActivityFrame.byteInverse, Fin.sum_univ_succ,
    Fin.prod_univ_succ, MarkedMomentNumbers.unsignedCap,
    MarkedMomentNumbers.zeta, ActualMarkedContractionEnergy.zeta,
    MixedCodeMoment.byteMoment, MixedCodeMoment.byteDelta]

theorem cubeBound_le_markedCap (ell : ℕ)
    (hpos : 0 < ell) (hle : ell ≤ 8) (hthree : ell ≠ 3) :
    cubeBound (Fin (8-ell)) ell ≤ WordMomentNumbers.markedCap ell := by
  interval_cases ell
  · norm_num [cubeBound_one_eq_zero, WordMomentNumbers.markedCap]
  · exact (cube_two.trans_le MarkedMomentNumbers.unsigned_two_lt.le)
  · exact (hthree rfl).elim
  · exact (cube_four.trans_le MarkedMomentNumbers.unsigned_four_lt.le)
  · exact (cube_five.trans_le MarkedMomentNumbers.unsigned_five_lt.le)
  · exact (cube_six.trans_le MarkedMomentNumbers.unsigned_six_lt.le)
  · exact (cube_seven.trans_le MarkedMomentNumbers.unsigned_seven_lt.le)
  · exact (cube_eight.trans_le MarkedMomentNumbers.unsigned_eight_lt.le)

end AESConcrete.SurvivorCubeNumbers
