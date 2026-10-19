import AESPaper.TwoQueryProgram
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Perm

/-!
# Uniform full-permutation sampling and the lazy two-query law
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AESPaper.UniformPermutation
open AESMixing AESPaper.FiniteOutputLaw AESPaper.TwoQueryProgram

section UniformFiber
variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
  [Nonempty X] [Nonempty Y]

/-- Equal finite fibers, witnessed by actual reindexing equivalences, give a
uniform output law under uniform sampling of the finite input type. -/
theorem pushLaw_uniform_of_fiberSymmetry (f : X → Y)
    (hsym : ∀ y z : Y, ∃ e : X ≃ X, ∀ x, f (e x) = z ↔ f x = y) :
    pushLaw f (fun _ => (Fintype.card X : ℝ)⁻¹) =
      fun _ => (Fintype.card Y : ℝ)⁻¹ := by
  classical
  let p := pushLaw f (fun _ => (Fintype.card X : ℝ)⁻¹)
  have heq (y z : Y) : p y = p z := by
    obtain ⟨e, he⟩ := hsym y z
    unfold p pushLaw
    exact Fintype.sum_equiv e _ _ (fun x => by simp only [he x])
  have hx : (Fintype.card X : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card X))
  have hy : (Fintype.card Y : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card Y))
  have ht : (∑ y, p y) = 1 := by
    dsimp [p]
    rw [pushLaw_total]
    simp [hx]
  funext y
  change p y = (Fintype.card Y : ℝ)⁻¹
  have hm : (Fintype.card Y : ℝ) * p y = 1 := by
    calc
      (Fintype.card Y : ℝ) * p y = ∑ z : Y, p y := by simp
      _ = ∑ z : Y, p z := Finset.sum_congr rfl (fun z _ => heq y z)
      _ = 1 := ht
  have hd : p y = 1 / (Fintype.card Y : ℝ) := by
    apply (eq_div_iff hy).2
    simpa [mul_comm] using hm
  simpa only [one_div] using hd

end UniformFiber

section Evaluation
variable {V : Type*} [Fintype V] [DecidableEq V]

def permutationWeight (_ : Equiv.Perm V) : ℝ :=
  (Fintype.card (Equiv.Perm V) : ℝ)⁻¹

theorem permutationWeight_total : (∑ p : Equiv.Perm V, permutationWeight p) = 1 := by
  have h : (Fintype.card (Equiv.Perm V) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (Equiv.Perm V)))
  simp [permutationWeight, h]

theorem single_eval_law (x : V) :
    pushLaw (fun p : Equiv.Perm V => p x) permutationWeight =
      fun _ => (Fintype.card V : ℝ)⁻¹ := by
  letI : Nonempty V := ⟨x⟩
  apply pushLaw_uniform_of_fiberSymmetry
  intro y z
  let q := Equiv.swap y z
  refine ⟨Equiv.equivCongr (Equiv.refl V) q, ?_⟩
  intro p
  change q (p x) = z ↔ p x = y
  have hq : q y = z := by simp [q]
  rw [← hq]
  exact q.injective.eq_iff

def DistinctPair (V : Type*) := {y : V × V // y.1 ≠ y.2}

instance : Fintype (DistinctPair V) := inferInstanceAs (Fintype {y : V × V // y.1 ≠ y.2})
instance : DecidableEq (DistinctPair V) := inferInstanceAs (DecidableEq {y : V × V // y.1 ≠ y.2})

theorem card_distinctPair : Fintype.card (DistinctPair V) =
    Fintype.card V * (Fintype.card V - 1) := by
  change Fintype.card {y : V × V // y.1 ≠ y.2} = _
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype (fun a b : V => a ≠ b))]
  simp only [Fintype.card_sigma]
  have hc (a : V) : Fintype.card {b : V // a ≠ b} = Fintype.card V - 1 := by
    simpa using (Fintype.card_subtype_compl (fun b : V => a = b))
  simp [hc]

def pairEval (x x' : V) (hx : x ≠ x') (p : Equiv.Perm V) : DistinctPair V :=
  ⟨(p x, p x'), fun h => hx (p.injective h)⟩

omit [Fintype V] [DecidableEq V] in
theorem bool_pair_injective {a b : V} (hab : a ≠ b) :
    Function.Injective (fun i : Bool => if i then a else b) := by
  intro i j hij
  cases i <;> cases j <;> simp_all

theorem distinct_eval_law (x x' : V) (hx : x ≠ x') :
    pushLaw (pairEval x x' hx) permutationWeight =
      fun _ => (Fintype.card (DistinctPair V) : ℝ)⁻¹ := by
  letI : Nonempty (DistinctPair V) := ⟨⟨(x, x'), hx⟩⟩
  apply pushLaw_uniform_of_fiberSymmetry
  intro a b
  obtain ⟨q, hq⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Bool => if i then a.val.1 else a.val.2)
    (fun i : Bool => if i then b.val.1 else b.val.2)
    (bool_pair_injective a.property) (bool_pair_injective b.property)
  have hq₁ : q a.val.1 = b.val.1 := by simpa using hq true
  have hq₂ : q a.val.2 = b.val.2 := by simpa using hq false
  refine ⟨Equiv.equivCongr (Equiv.refl V) q, ?_⟩
  intro p
  change pairEval x x' hx ((Equiv.equivCongr (Equiv.refl V) q) p) = b ↔
    pairEval x x' hx p = a
  constructor
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · change p x = a.val.1
      apply q.injective
      exact (congrArg (fun c : DistinctPair V => c.val.1) h).trans hq₁.symm
    · change p x' = a.val.2
      apply q.injective
      exact (congrArg (fun c : DistinctPair V => c.val.2) h).trans hq₂.symm
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · change q (p x) = b.val.1
      exact (congrArg q (congrArg (fun c : DistinctPair V => c.val.1) h)).trans hq₁
    · change q (p x') = b.val.2
      exact (congrArg q (congrArg (fun c : DistinctPair V => c.val.2) h)).trans hq₂

/-- Inclusion of a finite subtype retains its point mass exactly. -/
theorem pushLaw_subtype_val {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Y → Prop) [DecidablePred P] (p : {y // P y} → ℝ) (y : Y) :
    pushLaw Subtype.val p y = if h : P y then p ⟨y, h⟩ else 0 := by
  classical
  by_cases hy : P y
  · rw [dif_pos hy]
    unfold pushLaw
    rw [Finset.sum_eq_single (⟨y, hy⟩ : {y // P y})]
    · simp
    · intro z _ hzy
      have hz : z.val ≠ y := fun h => hzy (Subtype.ext h)
      simp [hz]
    · simp
  · rw [dif_neg hy]
    apply Finset.sum_eq_zero
    intro z _
    have hz : z.val ≠ y := fun h => hy (h ▸ z.property)
    simp [hz]

theorem fixed_pair_law_distinct (x x' : V) (hx : x ≠ x') (y : V × V) :
    pushLaw (fun p : Equiv.Perm V => (p x, p x')) permutationWeight y =
      if y.1 ≠ y.2 then (Fintype.card (DistinctPair V) : ℝ)⁻¹ else 0 := by
  have hcomp : (fun p : Equiv.Perm V => (p x, p x')) =
      fun p => (pairEval x x' hx p).val := rfl
  rw [hcomp, ← pushLaw_comp, distinct_eval_law]
  exact pushLaw_subtype_val (fun y : V × V => y.1 ≠ y.2) _ y

end Evaluation

section Adaptive
variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

/-- Exact fixed-pair law of uniform sampling over the full permutation type. -/
theorem retainedPairLaw_eq_response (x x' : V) (y : V × V) :
    retainedPairLaw (fun p : Equiv.Perm V => (p : V → V)) permutationWeight x x' y =
      freshRepeat x x' y.1 y.2 / Fintype.card V := by
  have hp : retainedPairLaw (fun p : Equiv.Perm V => (p : V → V)) permutationWeight x x' =
      pushLaw (fun p : Equiv.Perm V => (p x, p x')) permutationWeight := by
    funext z
    rcases z with ⟨z₁, z₂⟩
    simp only [retainedPairLaw, pushLaw, Prod.mk.injEq, mul_ite, mul_one, mul_zero]
  rw [hp]
  by_cases hx : x' = x
  · subst x'
    have he : (fun p : Equiv.Perm V => (p x, p x)) =
        (fun p => (fun z : V => (z, z)) (p x)) := rfl
    rw [he, ← pushLaw_comp (fun p : Equiv.Perm V => p x)
      (fun z : V => (z, z)) permutationWeight, single_eval_law]
    by_cases hy : y.1 = y.2
    · rcases y with ⟨a, b⟩
      dsimp at hy
      subst b
      simp [pushLaw, freshRepeat, differencePoint]
    · have hz (z : V) : (z, z) ≠ y := by
        intro h
        exact hy ((congrArg Prod.fst h).symm.trans (congrArg Prod.snd h))
      simp [pushLaw, hz, freshRepeat, differencePoint, hy]
  · have hx' : x ≠ x' := Ne.symm hx
    rw [fixed_pair_law_distinct x x' hx', card_distinctPair]
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hsub : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card V), Nat.cast_one]
    by_cases hy : y.1 = y.2
    · simp [freshRepeat, hx, uniformExcept, hy]
    · simp [freshRepeat, hx, uniformExcept, hy, Ne.symm hy,
        Nat.cast_mul, hsub, div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- Sampling one full uniform permutation gives exactly the adaptive two-answer
view used by the accepted lazy stopped-program experiment. -/
theorem retainedAdaptiveLaw_eq_adaptiveDifferenceView (x : V) (choose : V → V) :
    retainedAdaptiveLaw (fun p : Equiv.Perm V => (p : V → V))
      (fun _ => (Fintype.card (Equiv.Perm V) : ℝ)⁻¹) x choose =
      adaptiveDifferenceView permutationDifference (fun y => choose y - x) := by
  apply retained_adaptive_difference_identity
  intro a b y
  change retainedPairLaw (fun p : Equiv.Perm V => (p : V → V)) permutationWeight a b y = _
  rw [retainedPairLaw_eq_response, permutationDifference_eq_response]

end Adaptive
end AESPaper.UniformPermutation
