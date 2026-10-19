import AESMixing.RectangularSchur
import AESMixing.ShortenedFibers

/-! An incidence kernel counts graph points with prescribed output and
input coordinates. Its row and column masses are the corresponding fiber
cardinalities. This supplies the Schur estimate without assuming that
different coordinate assignments are independent. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem real_indicator_sum_card {C : Type*} [Fintype C]
    (p : C → Prop) [DecidablePred p] :
    (∑ c, if p c then (1 : ℝ) else 0) = Fintype.card {c // p c} := by
  simp [Fintype.card_subtype]

def incidenceMultiplicity {C O I : Type*} [Fintype C] [DecidableEq O] [DecidableEq I]
    (o : C → O) (i : C → I) (y : O) (x : I) : ℝ :=
  ∑ c, if o c = y ∧ i c = x then 1 else 0

theorem incidenceMultiplicity_nonnegative {C O I : Type*}
    [Fintype C] [DecidableEq O] [DecidableEq I]
    (o : C → O) (i : C → I) (y : O) (x : I) :
    0 ≤ incidenceMultiplicity o i y x := by
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

theorem incidenceMultiplicity_pair_card {C O I : Type*}
    [Fintype C] [DecidableEq O] [DecidableEq I]
    (o : C → O) (i : C → I) (y : O) (x : I) :
    incidenceMultiplicity o i y x = Fintype.card {c // (o c,i c) = (y,x)} := by
  have e : {c // o c = y ∧ i c = x} ≃ {c // (o c,i c) = (y,x)} :=
    Equiv.subtypeEquivRight (fun c => by
      constructor
      · rintro ⟨ho,hi⟩
        exact Prod.ext ho hi
      · intro h
        exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩)
  exact (real_indicator_sum_card (fun c => o c = y ∧ i c = x)).trans
    (congrArg (fun n : ℕ => (n : ℝ)) (Fintype.card_congr e))

theorem constant_kernel_zero_sum {O I : Type*} [Fintype I]
    (A : O → I → ℝ) (c : ℝ) (hA : ∀ y x, A y x = c)
    (f : I → ℝ) (hf : (∑ x, f x) = 0) : action A f = 0 := by
  funext y
  simp only [action, hA, ← Finset.mul_sum, hf, mul_zero, Pi.zero_apply]

theorem incidenceMultiplicity_action {C O I : Type*}
    [Fintype C] [Fintype I] [DecidableEq O] [DecidableEq I]
    (o : C → O) (i : C → I) (f : I → ℝ) (y : O) :
    action (incidenceMultiplicity o i) f y =
      ∑ c, if o c = y then f (i c) else 0 := by
  unfold action incidenceMultiplicity
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases h : o c = y <;> simp [h]

theorem incidenceMultiplicity_bilinear {C O I : Type*}
    [Fintype C] [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (o : C → O) (i : C → I) (f : I → ℝ) (g : O → ℝ) :
    (∑ y, g y * action (incidenceMultiplicity o i) f y) =
      ∑ c, g (o c) * f (i c) := by
  simp_rw [incidenceMultiplicity_action, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp

theorem incidenceMultiplicity_row {C O I : Type*}
    [Fintype C] [Fintype I] [DecidableEq O] [DecidableEq I]
    (o : C → O) (i : C → I) (y : O) :
    (∑ x, incidenceMultiplicity o i y x) = Fintype.card {c // o c = y} := by
  unfold incidenceMultiplicity
  rw [Finset.sum_comm]
  have ht (c : C) : (∑ x : I, if o c = y ∧ i c = x then (1 : ℝ) else 0) =
      if o c = y then 1 else 0 := by
    by_cases h : o c = y <;> simp [h]
  simp_rw [ht]
  exact real_indicator_sum_card _

theorem incidenceMultiplicity_column {C O I : Type*}
    [Fintype C] [Fintype O] [DecidableEq O] [DecidableEq I]
    (o : C → O) (i : C → I) (x : I) :
    (∑ y, incidenceMultiplicity o i y x) = Fintype.card {c // i c = x} := by
  unfold incidenceMultiplicity
  rw [Finset.sum_comm]
  have ht (c : C) : (∑ y : O, if o c = y ∧ i c = x then (1 : ℝ) else 0) =
      if i c = x then 1 else 0 := by
    by_cases h : i c = x <;> simp [h]
  simp_rw [ht]
  exact real_indicator_sum_card _

theorem incidenceMultiplicity_schur {C O I : Type*}
    [Fintype C] [Fintype O] [Fintype I] [DecidableEq O] [DecidableEq I]
    (o : C → O) (i : C → I) (r c : ℕ)
    (hr : ∀ y, Fintype.card {v // o v = y} ≤ r)
    (hc : ∀ x, Fintype.card {v // i v = x} ≤ c) (f : I → ℝ) :
    (∑ y, action (incidenceMultiplicity o i) f y^2) ≤
      (r : ℝ) * c * ∑ x, f x^2 := by
  apply rectangular_schur_energy _ r c (by positivity)
    (incidenceMultiplicity_nonnegative o i) ?_ ?_ f
  · intro y
    rw [incidenceMultiplicity_row]
    exact_mod_cast hr y
  · intro x
    rw [incidenceMultiplicity_column]
    exact_mod_cast hc x

end AESMixing
