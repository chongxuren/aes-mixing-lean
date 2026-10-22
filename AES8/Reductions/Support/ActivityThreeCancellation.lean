/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.SupportOutput
import AESPaper.WordCells
import AESPaper.StartingWord

/-!
# All-active activity length from the three lower activity lengths

The all-active degree-zero component is constant on its exact support cell.
Its total signed mass cancels the other three activity masses. Exact support
cardinality converts its counting norm to that mass without charging another
factor two. This is a structural bridge, not a new AES moment estimate.

Constructive only; no attacks, proof bypasses or predecessor/manuscript edits.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.ActivityThreeCancellation
open AESMixing AESMixing.AES
open AESPaper.StartingWord (q)
open AESPaper.RareActivity (l1)
open AES8.SupportProfile (component profile)

section Generic
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Exact conversion on one constant support cell, retaining signed mass. -/
theorem constant_supported_length_mass (s : Finset X) (f : X → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hcard : (s.card : ℝ) = K ^ 2) (hne : s.Nonempty)
    (hs : ∀ x, x ∉ s → f x = 0)
    (hc : ∀ x ∈ s, ∀ y ∈ s, f x = f y) :
    K * l2 f = |∑ x, f x| := by
  obtain ⟨a, ha⟩ := hne
  have hsum : (∑ x, f x) = (s.card : ℝ) * f a := by
    calc
      _ = ∑ x ∈ s, f x := (Finset.sum_subset (Finset.subset_univ s)
        (fun x _ hx => hs x hx)).symm
      _ = ∑ _x ∈ s, f a := Finset.sum_congr rfl (fun x hx => hc x hx a ha)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hsq : (∑ x, f x ^ 2) = (s.card : ℝ) * f a ^ 2 := by
    calc
      _ = ∑ x ∈ s, f x ^ 2 := (Finset.sum_subset (Finset.subset_univ s)
        (fun x _ hx => by rw [hs x hx]; norm_num)).symm
      _ = ∑ _x ∈ s, f a ^ 2 := Finset.sum_congr rfl (fun x hx => congrArg (fun z : ℝ => z ^ 2) (hc x hx a ha))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  apply (sq_eq_sq₀ (mul_nonneg hK (l2_nonneg _)) (abs_nonneg _)).mp
  rw [mul_pow, l2_sq, hsq, hsum, sq_abs, hcard]
  ring

end Generic

/-- Only the support-four activity component survives on the all-active cell. -/
theorem component_three_eq_activity_allActive (f : WordState → ℝ) (hz : f 0 = 0)
    (x : WordState) (hx : ∀ i, x i ≠ 0) : component f 3 x = SupportProfile.activity f x := by
  have hx4 : SupportProfile.activeCount x = 4 := by simp [SupportProfile.activeCount, hx]
  have h0 : component f 0 x = 0 := SupportProfile.component_supported f 0 x (by rw [hx4]; decide)
  have h1 : component f 1 x = 0 := SupportProfile.component_supported f 1 x (by rw [hx4]; decide)
  have h2 : component f 2 x = 0 := SupportProfile.component_supported f 2 x (by rw [hx4]; decide)
  have hd := SupportProfile.activity_decomposition f hz x
  simp only [Fin.sum_univ_four] at hd
  have hi0 : Fin.castAdd 10 (0 : Fin 4) = (0 : Fin 14) := by decide
  have hi1 : Fin.castAdd 10 (1 : Fin 4) = (1 : Fin 14) := by decide
  have hi2 : Fin.castAdd 10 (2 : Fin 4) = (2 : Fin 14) := by decide
  have hi3 : Fin.castAdd 10 (3 : Fin 4) = (3 : Fin 14) := by decide
  simpa only [hi0, hi1, hi2, hi3, h0, h1, h2, zero_add] using hd.symm

/-- Exact all-active cell count supplies the squared denominator (q-1)^2. -/
theorem component_three_length_mass (f : WordState → ℝ) (hz : f 0 = 0) :
    (q - 1) ^ 2 * profile f 3 = |∑ x, component f 3 x| := by
  apply constant_supported_length_mass AESPaper.WordCells.allActive (component f 3) ((q - 1) ^ 2)
    (sq_nonneg _) ?_ ?_ ?_ ?_
  · rw [AESPaper.WordCells.allActive_card]
    norm_num [q]
  · apply Finset.card_pos.mp
    rw [AESPaper.WordCells.allActive_card]
    norm_num
  · intro x hx
    apply SupportProfile.component_supported f 3 x
    change SupportProfile.activeCount x ≠ 4
    intro he
    apply hx
    rw [AESPaper.WordCells.mem_allActive]
    exact SupportOutput.allActive_of_count_four x he
  · intro x hx y hy
    rw [AESPaper.WordCells.mem_allActive] at hx hy
    have hxa : ∀ i, x i ≠ 0 := hx
    have hya : ∀ i, y i ≠ 0 := hy
    rw [component_three_eq_activity_allActive f hz x hxa, component_three_eq_activity_allActive f hz y hya]
    exact SupportProfile.activity_allActive f x y hxa hya

/-- Zero total mass cancels the signed mass in the largest activity cell. -/
theorem component_three_mass_le (f : WordState → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    |∑ x, component f 3 x| ≤ l1 (component f 0) + (l1 (component f 1) + l1 (component f 2)) := by
  have hm : (∑ x, component f 0 x) + ((∑ x, component f 1 x) +
      ((∑ x, component f 2 x) + (∑ x, component f 3 x))) = 0 := by
    have ha := SupportProfile.activity_sum f hs
    simp_rw [SupportProfile.activity_decomposition f hz] at ha
    rw [Finset.sum_comm] at ha
    simp only [Fin.sum_univ_four] at ha
    have hi0 : Fin.castAdd 10 (0 : Fin 4) = (0 : Fin 14) := by decide
    have hi1 : Fin.castAdd 10 (1 : Fin 4) = (1 : Fin 14) := by decide
    have hi2 : Fin.castAdd 10 (2 : Fin 4) = (2 : Fin 14) := by decide
    have hi3 : Fin.castAdd 10 (3 : Fin 4) = (3 : Fin 14) := by decide
    simp only [hi0, hi1, hi2, hi3] at ha
    linarith only [ha]
  have heq : (∑ x, component f 3 x) = -((∑ x, component f 0 x) +
      ((∑ x, component f 1 x) + (∑ x, component f 2 x))) := by linarith
  rw [heq, abs_neg]
  calc
    _ ≤ |∑ x, component f 0 x| + |(∑ x, component f 1 x) + (∑ x, component f 2 x)| := abs_add_le _ _
    _ ≤ |∑ x, component f 0 x| + (|∑ x, component f 1 x| + |∑ x, component f 2 x|) :=
      add_le_add le_rfl (abs_add_le _ _)
    _ ≤ _ := add_le_add (Finset.abs_sum_le_sum_abs _ _)
      (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))

/-- A complete structural bridge using the existing relaxed support counts. -/
theorem profile_three_le (f : WordState → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (q - 1) ^ 2 * profile f 3 ≤
      (2 : ℝ) ^ 17 * profile f 0 +
        (5 * (2 : ℝ) ^ 31 * profile f 1 + (2 : ℝ) ^ 49 * profile f 2) := by
  rw [component_three_length_mass f hz]
  have h0 := SupportOutput.component_l1 f 0 (by decide)
  have h1 := SupportOutput.component_l1 f 1 (by decide)
  have h2 := SupportOutput.component_l1 f 2 (by decide)
  change l1 (component f 0) ≤ (2 : ℝ) ^ 17 * profile f 0 at h0
  change l1 (component f 1) ≤ 5 * (2 : ℝ) ^ 31 * profile f 1 at h1
  change l1 (component f 2) ≤ (2 : ℝ) ^ 49 * profile f 2 at h2
  exact (component_three_mass_le f hz hs).trans (add_le_add h0 (add_le_add h1 h2))

end AES8.ActivityThreeCancellation
