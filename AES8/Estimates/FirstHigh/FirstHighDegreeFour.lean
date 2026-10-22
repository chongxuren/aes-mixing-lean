/- Module role: Selected first-high component estimates and their assembly.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Recurrence.TransferAssembly
import AESPaper.WordDamping
import AESMixing.DegreeProjectionBounds

/-!
# The actual first high remainder at degree-four output

The universal four-round initializer bounds the two degree-three support
components and the degree-four component. Their counting-norm triangle bound
is enough for output coordinate 13: the actual final `H Pi` damps its four
residual words by `nu^4`, with the inverse boundary transport retained.

The result is one unconditional coordinate of `PhysicalCaps.firstHigh`.
It does not establish the other output coordinates or the low/return fields.
No source atom estimate of 14/q, return-matrix cap, numerical premise, or
predecessor first-return estimate is used.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.FirstHighDegreeFour
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (error)
open AESPaper.GroupedRecurrence (step)
open AES8.SupportEvolution (highPart)

section CountingNorm

/-- Prove reindexing with an abstract finite alphabet before specializing to AES. -/
private theorem l2_equiv {I : Type*} [Fintype I] (e : Equiv.Perm I) (f : I → ℝ) :
    l2 (fun x => f (e x)) = l2 f := by
  apply (sq_eq_sq₀ (l2_nonneg _) (l2_nonneg _)).mp
  rw [l2_sq, l2_sq]
  exact Equiv.sum_comp e (fun x => f x ^ 2)

private theorem degree_l2_le {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    l2 (degreeComponent z j f) ≤ l2 f := by
  have he : (∑ x, degreeComponent z j f x ^ 2) ≤
      (1 : ℝ)^2 * ∑ x, f x ^ 2 := by
    simpa only [one_pow, _root_.one_mul] using degreeComponent_energy_le z hn j f
  have h := l2_le_of_energy (degreeComponent z j f) f 1 (by norm_num) he
  simpa only [_root_.one_mul] using h

/-- The exact forward law transport uses the inverse physical boundary. -/
theorem Pi_l2 (f : WordState → ℝ) :
    l2 (AESPaper.GroupedRecurrence.Pi f) = l2 f := by
  have hp : AESPaper.GroupedRecurrence.Pi f =
      fun x => f (AESPaper.GroupedRecurrence.boundary.toEquiv.symm x) := by
    funext x
    exact AESPaper.GroupedRecurrence.Pi_apply f x
  rw [hp]
  exact l2_equiv AESPaper.GroupedRecurrence.boundary.toEquiv.symm f

/-- Only output degree is used; the input can be an arbitrary correlated vector. -/
theorem degree_step_l2_le (j : Fin 5) (f : WordState → ℝ) :
    l2 (degreeComponent (0 : AES.Word) j (step f)) ≤
      AESPaper.WordDamping.nu ^ j.val * l2 f := by
  have h := l2_le_of_energy
    (action AES.parallelSuperboxKernel
      (degreeComponent (0 : AES.Word) j (AESPaper.GroupedRecurrence.Pi f)))
    (degreeComponent (0 : AES.Word) j (AESPaper.GroupedRecurrence.Pi f))
    (AESPaper.WordDamping.nu ^ j.val)
    (pow_nonneg AESPaper.WordDamping.nu_nonnegative j.val)
    (AESPaper.WordDamping.parallel_degree_energy j (AESPaper.GroupedRecurrence.Pi f))
  calc
    _ = l2 (action AES.parallelSuperboxKernel
        (degreeComponent (0 : AES.Word) j (AESPaper.GroupedRecurrence.Pi f))) := by
      rw [AESPaper.GroupedRecurrence.step, Function.comp_apply,
        AESPaper.GroupedRecurrence.H,
        ← AESConcrete.WordChannelCommutation.parallel_word_degree_commutes]
    _ ≤ AESPaper.WordDamping.nu ^ j.val *
        l2 (degreeComponent (0 : AES.Word) j (AESPaper.GroupedRecurrence.Pi f)) := h
    _ ≤ AESPaper.WordDamping.nu ^ j.val * l2 (AESPaper.GroupedRecurrence.Pi f) :=
      mul_le_mul_of_nonneg_left
        (degree_l2_le (0 : AES.Word) SupportProfile.word_card_gt_one j _)
        (pow_nonneg AESPaper.WordDamping.nu_nonnegative j.val)
    _ = AESPaper.WordDamping.nu ^ j.val * l2 f := by rw [Pi_l2]

/-- Coordinate 13 refines whole-word residual degree four. -/
theorem profile_step_thirteen_le (f : WordState → ℝ) :
    SupportProfile.profile (step f) (13 : Fin 14) ≤
      AESPaper.WordDamping.nu ^ (4 : ℕ) * l2 f := by
  have hd : SupportDegree.degree (13 : Fin 14) = (4 : Fin 5) := rfl
  have hr := SupportDegree.profile_le_degree (step f) (13 : Fin 14)
  rw [hd] at hr
  exact hr.trans (degree_step_l2_le (4 : Fin 5) f)

end CountingNorm

/-- The high part uses exactly the support coordinates with degrees 3, 3, 4.
The universal initializer has already discharged both actual source cases. -/
theorem highPart_actual_scaled_le (a : AES.State) (ha : a ≠ 0) :
    (2 : ℝ) ^ (80 : ℕ) * l2 (highPart (error 1 a)) ≤ 61 / 400 := by
  have htri : l2 (highPart (error 1 a)) ≤
      ∑ c : Fin 3, SupportProfile.profile (error 1 a) (Fin.natAdd 11 c) := by
    unfold highPart
    exact l2_finset_sum_le Finset.univ
      (fun c : Fin 3 => SupportProfile.component (error 1 a) (Fin.natAdd 11 c))
  have hb (c : Fin 3) :
      (2 : ℝ) ^ (80 : ℕ) *
          SupportProfile.profile (error 1 a) (Fin.natAdd 11 c) ≤
        AESPaper.initialProfile (SupportDegree.degree (Fin.natAdd 11 c)) := by
    have hr := mul_le_mul_of_nonneg_left
      (SupportDegree.profile_le_degree (error 1 a) (Fin.natAdd 11 c))
      (by positivity : 0 ≤ (2 : ℝ) ^ (80 : ℕ))
    exact (hr.trans_lt (Startup.scaled_degree_lt a ha
      (SupportDegree.degree (Fin.natAdd 11 c)))).le
  calc
    _ ≤ (2 : ℝ) ^ (80 : ℕ) *
        (∑ c : Fin 3, SupportProfile.profile (error 1 a) (Fin.natAdd 11 c)) :=
      mul_le_mul_of_nonneg_left htri (by positivity)
    _ = ∑ c : Fin 3, (2 : ℝ) ^ (80 : ℕ) *
        SupportProfile.profile (error 1 a) (Fin.natAdd 11 c) := Finset.mul_sum _ _ _
    _ ≤ ∑ c : Fin 3,
        AESPaper.initialProfile (SupportDegree.degree (Fin.natAdd 11 c)) :=
      Finset.sum_le_sum (fun c _ => hb c)
    _ = 61 / 400 := by
      norm_num [Fin.sum_univ_succ, SupportDegree.degree, SupportProfile.residualDegree,
        vec14_apply, AESPaper.initialProfile]

/-- Scalar slack for the fixed new diagonal and first-high allowance.
This calculation is separate from the actual-source and operator estimates. -/
theorem firstHigh_thirteen_scalar :
    (2 : ℝ) ^ (41 : ℕ) * AESPaper.WordDamping.nu ^ (4 : ℕ) * (61 / 400) ≤
      (1000 * g (13 : Fin 14)) * d (13 : Fin 14) := by
  norm_num [AESPaper.WordDamping.nu, g, d, vec14_apply]

/-- Unconditional coordinate 13 of the actual first high remainder.
The other coordinates of `PhysicalCaps.firstHigh` remain separate obligations. -/
theorem firstHigh_thirteen (a : AES.State) (ha : a ≠ 0) :
    SupportProfile.profile
        (TransferAssembly.centeredStep (highPart (error 1 a))) (13 : Fin 14) ≤
      (d (13 : Fin 14) / NormalizedProfile.factor 1) * (1000 * g (13 : Fin 14)) := by
  have hf : NormalizedProfile.factor 1 =
      (2 : ℝ) ^ (80 : ℕ) * (2 : ℝ) ^ (41 : ℕ) := by
    norm_num [NormalizedProfile.factor, omega41]
  have hh := highPart_actual_scaled_le a ha
  have hp := profile_step_thirteen_le (highPart (error 1 a))
  have hbound : NormalizedProfile.factor 1 *
      SupportProfile.profile
        (TransferAssembly.centeredStep (highPart (error 1 a))) (13 : Fin 14) ≤
      (1000 * g (13 : Fin 14)) * d (13 : Fin 14) := by
    rw [TransferAssembly.centeredStep_high_eq_step]
    calc
      _ ≤ NormalizedProfile.factor 1 *
          (AESPaper.WordDamping.nu ^ (4 : ℕ) * l2 (highPart (error 1 a))) :=
        mul_le_mul_of_nonneg_left hp (NormalizedProfile.factor_pos 1).le
      _ = (2 : ℝ) ^ (41 : ℕ) * AESPaper.WordDamping.nu ^ (4 : ℕ) *
          ((2 : ℝ) ^ (80 : ℕ) * l2 (highPart (error 1 a))) := by
        rw [hf]
        ring
      _ ≤ (2 : ℝ) ^ (41 : ℕ) * AESPaper.WordDamping.nu ^ (4 : ℕ) * (61 / 400) :=
        mul_le_mul_of_nonneg_left hh
          (mul_nonneg (by positivity) (pow_nonneg AESPaper.WordDamping.nu_nonnegative _))
      _ ≤ _ := firstHigh_thirteen_scalar
  calc
    _ ≤ ((1000 * g (13 : Fin 14)) * d (13 : Fin 14)) / NormalizedProfile.factor 1 := by
      apply (le_div_iff₀ (NormalizedProfile.factor_pos 1)).mpr
      calc
        _ = NormalizedProfile.factor 1 *
            SupportProfile.profile
              (TransferAssembly.centeredStep (highPart (error 1 a))) (13 : Fin 14) :=
          _root_.mul_comm _ _
        _ ≤ _ := hbound
    _ = _ := by ring

end AES8.FirstHighDegreeFour
