import AESMixing.KeyedPairStep
import Mathlib.Data.Fin.Tuple.Basic

/-! Explicit finite key tuples, with the last key sampled independently.
The equivalences only reorganize the one retained tuple used in both calls. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [DecidableEq V] [AddCommGroup V]

def uniformKeyWeight (n : ℕ) (_ : Fin n → V) : ℝ := 1 / (Fintype.card V : ℝ)^n

omit [DecidableEq V] [AddCommGroup V] in
theorem uniformKeyWeight_succ (n : ℕ) (keys : Fin (n+1) → V) :
    uniformKeyWeight (n+1) keys =
      uniformKeyWeight n (Fin.init keys) / Fintype.card V := by
  simp only [uniformKeyWeight, pow_succ, div_mul_eq_div_div]

def appendKeyEquiv (n : ℕ) : ((Fin n → V) × V) ≃ (Fin (n+1) → V) where
  toFun k := Fin.snoc k.1 k.2
  invFun keys := (Fin.init keys, keys (Fin.last n))
  left_inv k := by simp
  right_inv keys := Fin.snoc_init_self keys

omit [Fintype V] [DecidableEq V] [AddCommGroup V] in
theorem appendKeyEquiv_apply (n : ℕ) (k : (Fin n → V) × V) :
    appendKeyEquiv n k = Fin.snoc k.1 k.2 := rfl

omit [Fintype V] [AddCommGroup V] in
theorem retainedPairLaw_reindex {K J : Type*} [Fintype K] [Fintype J]
    (e : J ≃ K) (E : K → V → V) (weight : K → ℝ) (x x' : V) :
    retainedPairLaw (fun k => E (e k)) (fun k => weight (e k)) x x' =
      retainedPairLaw E weight x x' := by
  funext y
  exact Equiv.sum_comp e
    (fun k => weight k * if E k x = y.1 ∧ E k x' = y.2 then (1 : ℝ) else 0)

theorem retained_tuple_step (n : ℕ) (E : (Fin n → V) → V → V)
    (s : Equiv.Perm V) (x x' : V) :
    retainedPairLaw (fun keys : Fin (n+1) → V => fun z =>
      s (E (Fin.init keys) z) + keys (Fin.last n)) (uniformKeyWeight (n+1)) x x' =
    action (keyedPairKernel s) (retainedPairLaw E (uniformKeyWeight n) x x') := by
  have h := retainedPairLaw_reindex (appendKeyEquiv (V := V) n)
    (fun keys : Fin (n+1) → V => fun z => s (E (Fin.init keys) z) + keys (Fin.last n))
    (uniformKeyWeight (n+1)) x x'
  simp only [appendKeyEquiv_apply, Fin.init_snoc, Fin.snoc_last,
    uniformKeyWeight_succ] at h
  rw [← h]
  exact retained_pair_fresh_key E (uniformKeyWeight n) s x x'

def singletonKeyEquiv : V ≃ (Fin 1 → V) where
  toFun k _ := k
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]

def differencePoint (a : V) (b : V) : ℝ := if a = b then 1 else 0

theorem retained_whitening (x x' : V) :
    retainedPairLaw (fun keys : Fin 1 → V => fun z => z + keys 0)
      (uniformKeyWeight 1) x x' = pairFromDifference (differencePoint (x'-x)) := by
  have h := retainedPairLaw_reindex (singletonKeyEquiv (V := V))
    (fun keys : Fin 1 → V => fun z => z + keys 0) (uniformKeyWeight 1) x x'
  rw [← h]
  funext y
  change (∑ key : V, (1 / (Fintype.card V : ℝ)^1) *
    if x + key = y.1 ∧ x' + key = y.2 then 1 else 0) = _
  simp only [pow_one, one_div_mul_eq_div]
  rw [← Finset.sum_div]
  have hy : y.1 + (y.2-y.1) = y.2 := by simp
  simpa only [hy, pairFromDifference, differencePoint] using
    output_key_pair x x' y.1 (y.2-y.1)

end AESMixing
