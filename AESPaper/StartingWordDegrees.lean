import AESPaper.StartingWord
import AESPaper.SourceNumbers
import AESConcrete.ActualPositiveColumnDegrees
import AESConcrete.ActualColumnActivity
import AESMixing.DegreeComposition

/-!
# Actual centered source byte-degree energies

`byteDegreeEnergy` counts residual bytes inside one 32-bit source word.
It is distinct from the five full-state residual-word components. The
source is the actual forward AES word column, centered at uniform nonzero
words. Positive byte degrees do not see that reference; degree zero loses
exactly `1/(q-1)` in squared energy.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.StartingWordDegrees
open AESMixing AESConcrete
open AESPaper.StartingWord (q wordLaw)
open AESPaper.SourceNumbers (sourceZ)
open AESConcrete.AllColumnBound (inputZeroMask inputZeroMask_bit)

abbrev Byte := BinaryWord 8

/-- Source word after its first complete forward superbox, with the actual
nonzero-word reference removed. -/
def centeredWordLaw (a : AES.Word) : AES.Word → ℝ :=
  wordLaw a - uniformExcept (0 : AES.Word)

/-- The five source energies are measured on the four-byte decomposition. -/
def byteDegreeEnergy (a : AES.Word) (j : Fin 5) : ℝ :=
  ∑ y, degreeComponent (0 : Byte) j (centeredWordLaw a) y ^ 2

/-- Actual byte weight, derived from the checked zero mask of the input. -/
def inputByteWeight (a : AES.Word) : ℕ := 4-AES.maskSize (inputZeroMask a)

theorem inputByteWeight_range (a : AES.Word) (ha : a ≠ 0) :
    1 ≤ inputByteWeight a ∧ inputByteWeight a ≤ 4 := by
  have h := AllColumnBound.inputZeroMask_size_lt_four a ha
  unfold inputByteWeight
  omega

theorem centeredWordLaw_zero (a : AES.Word) (ha : a ≠ 0) :
    centeredWordLaw a 0 = 0 := by
  simp only [centeredWordLaw, Pi.sub_apply, StartingWord.wordLaw_zero a ha,
    uniformExcept, if_true, sub_self]

theorem centeredWordLaw_sum (a : AES.Word) : (∑ y, centeredWordLaw a y) = 0 := by
  simp only [centeredWordLaw, Pi.sub_apply, Finset.sum_sub_distrib,
    StartingWord.wordLaw_total,
    GroupedLaw.uniform_total (0 : AES.Word) AESConcrete.AES.word_card_gt_one, sub_self]

/-- Stationarity of the uniform non-distinguished law is purely pointed
kernel algebra; it requires no contraction or nonnegativity estimate. -/
theorem pointed_uniformExcept {V : Type*} [Fintype V] [DecidableEq V]
    {D : V → V → ℝ} {z : V} (h : PointedBistochastic D z) :
    action D (uniformExcept z) = uniformExcept z := by
  funext y
  have hp (x : V) : D y x * uniformExcept z x =
      (D y x - if x=z then D y z else 0) / (Fintype.card V - 1 : ℝ) := by
    by_cases hx : x=z
    · subst x
      simp [uniformExcept]
    · simp [uniformExcept, hx, div_eq_mul_inv]
  unfold action
  simp_rw [hp]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, h.row_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, h.zero_column]
  by_cases hy : y=z <;> simp [uniformExcept, hy]

theorem uniform_byte_degree_zero :
    degreeComponent (0 : Byte) 0 (uniformExcept (0 : AES.Word)) = uniformExcept 0 := by
  rw [← degreeKernel_action]
  exact pointed_uniformExcept
    (degree_zero_pointed (0 : Byte) (by norm_num [BinaryWord.card]))

theorem uniform_positive_byte_degree (j : Fin 5) (hj : j ≠ 0) :
    degreeComponent (0 : Byte) j (uniformExcept (0 : AES.Word)) = 0 := by
  calc
    _ = degreeComponent (0 : Byte) j
        (degreeComponent (0 : Byte) 0 (uniformExcept (0 : AES.Word))) :=
      congrArg (degreeComponent (0 : Byte) j) uniform_byte_degree_zero.symm
    _ = 0 := by
      rw [degreeComponent_compose (0 : Byte) (by norm_num [BinaryWord.card]), if_neg hj]

theorem degreeComponent_sub (j : Fin 5) (f g : AES.Word → ℝ) :
    degreeComponent (0 : Byte) j (f-g) =
      degreeComponent (0 : Byte) j f-degreeComponent (0 : Byte) j g := by
  simp only [← degreeKernel_action, action_sub]

/-- Every positive source byte degree is unchanged by the word reference. -/
theorem centered_positive_degree (a : AES.Word) (j : Fin 5) (hj : j ≠ 0) :
    degreeComponent (0 : Byte) j (centeredWordLaw a) =
      degreeComponent (0 : Byte) j (wordLaw a) := by
  rw [centeredWordLaw, degreeComponent_sub, uniform_positive_byte_degree j hj, sub_zero]

/-- Exact degree-zero reference correction. The ordinary activity projection
preserves both the source's zero entry and its total mass. -/
theorem byteDegreeEnergy_zero (a : AES.Word) (ha : a ≠ 0) :
    byteDegreeEnergy a 0 =
      (∑ y, degreeComponent (0 : Byte) 0 (wordLaw a) y ^ 2) - 1/(q-1) := by
  have hp := degree_zero_pointed (0 : Byte) (by norm_num [BinaryWord.card])
  have hz : degreeComponent (0 : Byte) 0 (wordLaw a) (0 : AES.Word) = 0 := by
    rw [← degreeKernel_action]
    change action (degreeKernel (0 : Byte) 0) (wordLaw a) (fun _ : Fin 4 => (0 : Byte)) = 0
    rw [hp.action_zero]
    exact StartingWord.wordLaw_zero a ha
  have hs : (∑ y, degreeComponent (0 : Byte) 0 (wordLaw a) y) = 1 := by
    rw [← degreeKernel_action, hp.action_sum]
    exact StartingWord.wordLaw_total a
  have hc := centered_energy (degreeComponent (0 : Byte) 0 (wordLaw a))
    (0 : AES.Word) AESConcrete.AES.word_card_gt_one hz hs
  unfold byteDegreeEnergy
  rw [centeredWordLaw, degreeComponent_sub, uniform_byte_degree_zero]
  simpa only [energy, Pi.sub_apply, ← StartingWord.q_eq_word_card] using hc

/-- v9 source-energy formula for byte weights two through four. -/
def multiCap (t : ℕ) (j : Fin 5) : ℝ :=
  if j=0 then MultibyteColumnNumbers.activityFactor t / (255 : ℝ)^4 - 1/(q-1)
  else MultibyteColumnNumbers.degreeCap t j.val

theorem actual_activity_energy_le (a : AES.Word) (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4)
    (hw : inputByteWeight a = t) :
    (∑ y, degreeComponent (0 : Byte) 0 (wordLaw a) y ^ 2) ≤
      MultibyteColumnNumbers.activityFactor t / (255 : ℝ)^4 := by
  have hmask := AESMixing.maskSize_le_four (inputZeroMask a)
  have hcount : t + AES.maskSize (inputZeroMask a) = 4 := by
    unfold inputByteWeight at hw
    omega
  have h := ActualColumnActivity.actual_column_activity_energy_le .ordinary .ordinary false
    a (inputZeroMask a) t ht hcount (fun i => (inputZeroMask_bit a i).symm)
  rw [WordOrientationClosure.ordinary_word_kernel] at h
  have hcolumn : (fun v : AES.Word => AES.wordSuperboxKernel v a) =
      AESPaper.StartingWord.wordLaw a := rfl
  rw [hcolumn] at h
  exact h

theorem actual_positive_degree_energy_le (a : AES.Word) (ha : a ≠ 0)
    (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (hw : inputByteWeight a = t)
    (j : Fin 5) (hj : j ≠ 0) :
    byteDegreeEnergy a j ≤ MultibyteColumnNumbers.degreeCap t j.val := by
  have hmask := AESMixing.maskSize_le_four (inputZeroMask a)
  have hcount : t + AES.maskSize (inputZeroMask a) = 4 := by
    unfold inputByteWeight at hw
    omega
  have hjval : 1 ≤ j.val := by
    have hne : j.val ≠ 0 := fun h => hj (Fin.ext h)
    omega
  have h := ActualPositiveColumnDegrees.positive_degree_energy_le .ordinary .ordinary false
    a ha (inputZeroMask a) t ht hcount (fun i => (inputZeroMask_bit a i).symm) j hjval
  rw [WordOrientationClosure.ordinary_word_kernel] at h
  unfold byteDegreeEnergy
  rw [centered_positive_degree a j hj]
  have hcolumn : (fun v : AES.Word => AES.wordSuperboxKernel v a) =
      AESPaper.StartingWord.wordLaw a := rfl
  rw [hcolumn] at h
  exact h

theorem byteDegreeEnergy_le_multiCap (a : AES.Word) (ha : a ≠ 0)
    (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (hw : inputByteWeight a = t) (j : Fin 5) :
    byteDegreeEnergy a j ≤ multiCap t j := by
  by_cases hj : j=0
  · subst j
    rw [byteDegreeEnergy_zero a ha]
    exact sub_le_sub_right (actual_activity_energy_le a t ht hw) _
  · simpa only [multiCap, if_neg hj] using
      actual_positive_degree_energy_le a ha t ht hw j hj

/-- Exact rational rounding of the already identified multibyte source caps.
All source and support mathematics is outside this finite calculation. -/
theorem multiCap_scaled_lt (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (j : Fin 5) :
    q * multiCap t j < sourceZ t j ^ 2 := by
  obtain ⟨ht0,ht1⟩ := ht
  interval_cases t <;> fin_cases j <;>
    norm_num [multiCap, q, sourceZ, MultibyteColumnNumbers.activityFactor,
      MultibyteColumnNumbers.degreeCap, MultibyteColumnNumbers.zeroCap,
      MultibyteColumnNumbers.rho, MultibyteColumnNumbers.atom,
      MultibyteColumnNumbers.nu, MultibyteColumnNumbers.delta,
      Finset.sum_range_succ, Nat.choose]

/-- The actual centered source has the v9 strict `Z` row for every input
with two, three or four active bytes. No source-energy premise remains. -/
theorem source_degree_energy_lt_multi (a : AES.Word) (ha : a ≠ 0)
    (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (hw : inputByteWeight a = t) (j : Fin 5) :
    q * byteDegreeEnergy a j < sourceZ t j ^ 2 := by
  have hq : 0 ≤ q := by norm_num [q]
  exact (mul_le_mul_of_nonneg_left (byteDegreeEnergy_le_multiCap a ha t ht hw j) hq).trans_lt
    (multiCap_scaled_lt t ht j)

end AESPaper.StartingWordDegrees
