import AESConcrete.MarkedBlockVectorization

/-!
# Symmetric inverse-frame row-energy bounds

Exact contraction energies give pair bounds by Cauchy--Schwarz in its
two-squares form. Symmetric coefficient rows then give an absolute row-sum
bound. Vanishing contractions may be removed before taking row sums.
This generic absolute bound does not supply the sharper signed degree-three
overlap argument. Constructive mathematics only; no attacks or edits to
frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.InverseFrameEnergy
open AESMixing AESConcrete.ActivityFrame AESConcrete.MarkedBlockVectorization

attribute [local instance] Classical.propDecidable

section Generic
variable {S Y : Type*} [Fintype S] [Fintype Y]

def energy (f : Y → ℝ) : ℝ := ∑ y, f y ^ 2
def inner (f g : Y → ℝ) : ℝ := ∑ y, f y * g y

theorem inner_abs_le_average (f g : Y → ℝ) :
    |inner f g| ≤ (energy f + energy g) / 2 := by
  have hp (y : Y) : |f y * g y| ≤ (f y ^ 2 + g y ^ 2) / 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg (f y + g y)]
    · nlinarith [sq_nonneg (f y - g y)]
  calc
    _ ≤ ∑ y : Y, |f y * g y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y : Y, (f y ^ 2 + g y ^ 2) / 2 :=
      Finset.sum_le_sum (fun y _ => hp y)
    _ = _ := by rw [← Finset.sum_div, Finset.sum_add_distrib]; rfl

theorem scaled_inner_abs_le (q : ℝ) (hq : 0 ≤ q) (C : S → Y → ℝ)
    (zeta : S → ℝ) (hC : ∀ s, q * energy (C s) ≤ zeta s) (s t : S) :
    q * |inner (C s) (C t)| ≤ (zeta s + zeta t) / 2 := by
  calc
    _ ≤ q * ((energy (C s) + energy (C t)) / 2) :=
      mul_le_mul_of_nonneg_left (inner_abs_le_average (C s) (C t)) hq
    _ ≤ _ := by nlinarith [hC s, hC t]

/-- Symmetry combines the two endpoint energies into one row sum. -/
theorem symmetric_average_sum (a : S → S → ℝ) (ha : ∀ s t, a s t = a t s)
    (zeta : S → ℝ) :
    (∑ s : S, ∑ t : S, |a s t| * ((zeta s + zeta t) / 2)) =
      ∑ s : S, zeta s * ∑ t : S, |a s t| := by
  have hswap : (∑ s : S, ∑ t : S, |a s t| * zeta t) =
      ∑ s : S, ∑ t : S, |a s t| * zeta s := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [ha t s]
  have hexpand :
      (∑ s : S, ∑ t : S, |a s t| * ((zeta s + zeta t) / 2)) =
        ((∑ s : S, ∑ t : S, |a s t| * zeta s) +
          (∑ s : S, ∑ t : S, |a s t| * zeta t)) / 2 := by
    have hp (s t : S) : |a s t| * ((zeta s + zeta t) / 2) =
        (|a s t| * zeta s) / 2 + (|a s t| * zeta t) / 2 := by ring
    simp_rw [hp, Finset.sum_add_distrib, ← Finset.sum_div]
    ring
  rw [hexpand, hswap]
  have hfactor : (∑ s : S, ∑ t : S, |a s t| * zeta s) =
      ∑ s : S, zeta s * ∑ t : S, |a s t| := by
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  simp_rw [hfactor]
  ring

theorem quadratic_le_rows (q : ℝ) (hq : 0 ≤ q)
    (a : S → S → ℝ) (ha : ∀ s t, a s t = a t s)
    (C : S → Y → ℝ) (zeta : S → ℝ) (hC : ∀ s, q * energy (C s) ≤ zeta s) :
    q * (∑ s : S, ∑ t : S, a s t * inner (C s) (C t)) ≤
      ∑ s : S, zeta s * ∑ t : S, |a s t| := by
  have hp (s t : S) : a s t * (q * inner (C s) (C t)) ≤
      |a s t| * ((zeta s + zeta t) / 2) := by
    calc
      _ ≤ |a s t * (q * inner (C s) (C t))| := le_abs_self _
      _ = |a s t| * (q * |inner (C s) (C t)|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq]
      _ ≤ _ := mul_le_mul_of_nonneg_left (scaled_inner_abs_le q hq C zeta hC s t)
        (abs_nonneg _)
  calc
    _ = ∑ s : S, ∑ t : S, a s t * (q * inner (C s) (C t)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ s : S, ∑ t : S, |a s t| * ((zeta s + zeta t) / 2) :=
      Finset.sum_le_sum (fun s _ => Finset.sum_le_sum (fun t _ => hp s t))
    _ = _ := symmetric_average_sum a ha zeta

theorem sum_subtype_of_zero (P : S → Prop) (f : S → ℝ)
    (hf : ∀ s, ¬ P s → f s = 0) : (∑ s : S, f s) = ∑ s : {s // P s}, f s.val := by
  calc
    _ = ∑ s : S, if P s then f s else 0 := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : P s <;> simp [hs, hf s]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

theorem quadratic_restrict (a : S → S → ℝ) (C : S → Y → ℝ)
    (P : S → Prop) (hC : ∀ s, ¬ P s → ∀ y, C s y = 0) :
    (∑ s : S, ∑ t : S, a s t * inner (C s) (C t)) =
      ∑ s : {s // P s}, ∑ t : {t // P t}, a s.val t.val * inner (C s.val) (C t.val) := by
  rw [sum_subtype_of_zero P (fun s => ∑ t : S, a s t * inner (C s) (C t))
    (fun s hs => by simp only [inner, hC s hs, zero_mul, Finset.sum_const_zero, mul_zero])]
  apply Finset.sum_congr rfl
  intro s _
  exact sum_subtype_of_zero P (fun t => a s.val t * inner (C s.val) (C t))
    (fun t ht => by simp only [inner, hC t ht, mul_zero, Finset.sum_const_zero])

theorem quadratic_restricted_le_rows (q : ℝ) (hq : 0 ≤ q)
    (a : S → S → ℝ) (ha : ∀ s t, a s t = a t s)
    (C : S → Y → ℝ) (P : S → Prop)
    (hzero : ∀ s, ¬ P s → ∀ y, C s y = 0)
    (zeta : {s // P s} → ℝ)
    (hC : ∀ s : {s // P s}, q * energy (C s.val) ≤ zeta s) :
    q * (∑ s : S, ∑ t : S, a s t * inner (C s) (C t)) ≤
      ∑ s : {s // P s}, zeta s * ∑ t : {t // P t}, |a s.val t.val| := by
  rw [quadratic_restrict a C P hzero]
  exact quadratic_le_rows q hq (fun s t : {s // P s} => a s.val t.val)
    (fun s t => ha s.val t.val) (fun s : {s // P s} => C s.val) zeta hC

end Generic

theorem frameInverse_symmetric {I : Type*} [Fintype I]
    (s t : I → Bool) : frameInverse s t = frameInverse t s := by
  unfold frameInverse
  apply Finset.prod_congr rfl
  intro i _
  exact byteInverse_symmetric (s i) (t i)

section Activity
variable {I V X : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [Zero V] [DecidableEq V] [Fintype X]

/-- Every source correlation remains in the actual contracted responses.
Only surviving frame choices enter the absolute coefficient row sums. -/
theorem fullResponse_restricted_le_rows (hV : Fintype.card V = 256)
    (m : I → Bool) (T : Marked m → V → V → ℝ) (coord : X → I → V)
    (q : ℝ) (hq : 0 ≤ q) (P : (Activity m → Bool) → Prop)
    (hzero : ∀ s, ¬ P s → ∀ y : Marked m → V, contractedResponse m T coord s y = 0)
    (zeta : {s // P s} → ℝ)
    (hC : ∀ s : {s // P s},
      q * energy (contractedResponse m T coord s.val) ≤ zeta s) :
    q * (∑ v : I → V, fullResponse m T coord v ^ 2) ≤
      ∑ s : {s // P s}, zeta s *
        ∑ t : {t // P t}, |frameInverse s.val t.val| := by
  rw [fullResponse_energy hV]
  exact quadratic_restricted_le_rows q hq frameInverse frameInverse_symmetric
    (fun s => contractedResponse m T coord s) P hzero zeta hC

end Activity

end AESConcrete.InverseFrameEnergy
