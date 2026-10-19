import AESMixing.Markov

/-! Pointwise pair identity for a retained input/output-whitened permutation. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

def whitenedPairDifference (s : Equiv.Perm V) (x a y b : V) : ℝ :=
  ((∑ inputKey, ∑ outputKey,
    if s (x + inputKey) + outputKey = y ∧
      s (x + inputKey + a) + outputKey = y + b then (1 : ℝ) else 0) /
        Fintype.card V) / Fintype.card V

theorem whitened_pair_identity (s : Equiv.Perm V) (x a y b : V) :
    whitenedPairDifference s x a y b = differenceChannel s b a / Fintype.card V := by
  unfold whitenedPairDifference
  rw [Finset.sum_div]
  simp_rw [output_key_pair]
  rw [← Finset.sum_div, common_key_difference]

def pairCoordinates : (V × V) ≃ (V × V) where
  toFun y := (y.1, y.2 - y.1)
  invFun z := (z.1, z.1 + z.2)
  left_inv y := by simp
  right_inv z := by simp

def pairFromDifference (p : V → ℝ) (y : V × V) : ℝ :=
  p (y.2 - y.1) / Fintype.card V

omit [DecidableEq V] in
theorem tv_pairFromDifference (p q : V → ℝ) :
    tv (pairFromDifference p) (pairFromDifference q) = tv p q := by
  calc
    tv (pairFromDifference p) (pairFromDifference q) =
        tv (uniformFirst (κ := V) p ∘ pairCoordinates)
           (uniformFirst (κ := V) q ∘ pairCoordinates) := rfl
    _ = tv (uniformFirst (κ := V) p) (uniformFirst (κ := V) q) :=
      tv_relabel pairCoordinates _ _
    _ = tv p q := tv_uniformFirst p q

theorem whitened_fixed_pair_tv (s : Equiv.Perm V) (x a : V) :
    tv (fun y : V × V => whitenedPairDifference s x a y.1 (y.2 - y.1))
      (pairFromDifference (uniformExcept (0 : V))) =
        tv (fun b => differenceChannel s b a) (uniformExcept 0) := by
  simp_rw [whitened_pair_identity]
  exact tv_pairFromDifference (V := V) (fun b => differenceChannel s b a)
    (uniformExcept (0 : V))

end AESMixing
