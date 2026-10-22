/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.FirstHigh.TwoZeroElevenMoment
import AES8.Reductions.Source.ActualTwoActiveMass

/-! Signed incoming-eleven masses use the literal affine zero pin. One
retained entry and two complete pinned-fiber column energies suffice. No
second-source averaging or independence is used.  Constructive only; no attacks. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.constructorNameAsVariable false
noncomputable section
open scoped BigOperators

namespace AES8.PinnedTwoZeroMass
open AESMixing AESMixing.AES
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.GroupedLaw (error)
open AES8.SupportProfile (component)
open AES8.ConditionalSourceResponse
open AES8.ElevenConditionalResponse
open AES8.TwoZeroElevenMoment (retained retained_ne prod_retained)
open AES8.OneSourceEventMoment (atomCap columnCap)
open AES8.TwoZeroThirteenMoment (entryCap)
open AES8.TwoActiveScalars (elevenExactMassCap)

section Generic
variable {G : Type*} [Fintype G]

/-- Entry-times-Cauchy for a signed triple product. -/
theorem triple_mass_le (F : Fin 3 → G → ℝ) (eta delta : ℝ)
    (he : 0 ≤ eta) (hd : 0 ≤ delta)
    (hentry : ∀ g, |F 0 g| ≤ eta)
    (h1 : (∑ g, F 1 g ^ 2) ≤ delta) (h2 : (∑ g, F 2 g ^ 2) ≤ delta) :
    |∑ g, ∏ i : Fin 3, F i g| ≤ eta * delta := by
  have hbc : (∑ g, |F 1 g| * |F 2 g|) ≤ delta := by
    apply (sq_le_sq₀ (Finset.sum_nonneg (fun g _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))) hd).mp
    calc
      _ ≤ (∑ g, |F 1 g| ^ 2) * (∑ g, |F 2 g| ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun g => |F 1 g|) (fun g => |F 2 g|)
      _ = (∑ g, F 1 g ^ 2) * (∑ g, F 2 g ^ 2) := by simp only [sq_abs]
      _ ≤ delta * delta := mul_le_mul h1 h2 (Finset.sum_nonneg (fun g _ => sq_nonneg _)) hd
      _ = delta ^ 2 := (pow_two delta).symm
  calc
    _ ≤ ∑ g, |∏ i : Fin 3, F i g| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ g, |F 0 g| * (|F 1 g| * |F 2 g|) := by
      simp only [Fin.prod_univ_three, abs_mul]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ ≤ ∑ g, eta * (|F 1 g| * |F 2 g|) := Finset.sum_le_sum
      (fun g _ => mul_le_mul_of_nonneg_right (hentry g) (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = eta * ∑ g, |F 1 g| * |F 2 g| := (Finset.mul_sum _ _ _).symm
    _ ≤ eta * delta := mul_le_mul_of_nonneg_left hbc he

end Generic

theorem pinned_pattern_mass_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0)
    (w : OtherAssignments k) (j : Fin 4) :
    |∑ g : WordMixTwoZeroFiber.G r, pinnedPattern b k w j g.val| ≤
      atomCap * entryCap * columnCap := by
  let a := zeroPin k w j
  let mu := wordLaw (sourceInput b k) a
  let R := residualMatrix AES.wordSuperboxKernel (0 : AES.Word)
  let F (i : Fin 3) (h : WordMixTwoZeroPinnedFiber.H r j) : ℝ :=
    R (h.val.val (retained j i)) (affineEquiv k w (retained j i) a)
  have hcol (i : Fin 3) : (∑ h : WordMixTwoZeroPinnedFiber.H r j, F i h ^ 2) ≤ columnCap := by
    change (∑ h : WordMixTwoZeroPinnedFiber.H r j,
      R (h.val.val (retained j i)) (affineEquiv k w (retained j i) a) ^ 2) ≤ columnCap
    rw [WordMixTwoZeroPinnedFiber.sum_coordinate r hr j (retained j i) (retained_ne j i)
      (fun x => R x (affineEquiv k w (retained j i) a) ^ 2)]
    exact OneSourceEventMoment.residual_column_le _
  have htriple : |∑ h : WordMixTwoZeroPinnedFiber.H r j, ∏ i : Fin 3, F i h| ≤
      entryCap * columnCap :=
    triple_mass_le F entryCap columnCap (by norm_num [entryCap, q]) (by norm_num [columnCap, q])
      (fun h => TwoZeroThirteenMoment.residual_entry_le _ _) (hcol 1) (hcol 2)
  have heq : (∑ g : WordMixTwoZeroFiber.G r, pinnedPattern b k w j g.val) =
      mu * ∑ h : WordMixTwoZeroPinnedFiber.H r j, ∏ i : Fin 3, F i h := by
    change (∑ g : WordMixTwoZeroFiber.G r,
      if g.val j = 0 then mu * ∏ i : OtherCoordinates j,
        R (g.val i.val) (affineEquiv k w i.val a) else 0) = _
    rw [WordMixTwoZeroPinnedFiber.sum_input_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [prod_retained]
    rfl
  rw [heq, abs_mul]
  calc
    _ ≤ atomCap * (entryCap * columnCap) :=
      mul_le_mul (AESPaper.StartingWord.wordLaw_abs_point_lt (sourceInput b k) a hk).le htriple
        (abs_nonneg _) (by norm_num [atomCap, q])
    _ = _ := by ring

theorem actual_eleven_full_mass_le (r : Fin 16) (hr : maskSize r = 2)
    (b : AES.State) (hb : b ≠ 0) :
    |∑ g : WordMixTwoZeroFiber.G r, component (error 1 b) 11 g.val| ≤ elevenExactMassCap := by
  obtain ⟨k, hk, _⟩ := exists_nonzero_source_probability_mixture b hb
  rw [actual_component_eleven_eq_probability_mixture b k, Finset.sum_comm]
  simp only [← Finset.mul_sum]
  apply ActualZeroMoment.abs_probability_sum_le (conditionWeight b k) _ elevenExactMassCap
    (conditionWeight_nonnegative b k) (conditionWeight_total b k)
  intro w
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : Fin 4, |∑ g : WordMixTwoZeroFiber.G r, pinnedPattern b k w j g.val| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, atomCap * entryCap * columnCap := Finset.sum_le_sum
      (fun j _ => pinned_pattern_mass_le r hr b k hk w j)
    _ = elevenExactMassCap := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_ofNat, elevenExactMassCap]
      ring

/-- Three prescribed output zeros plus any input zero force the zero vector. -/
theorem three_zero_input_zero (r : Fin 16) (hr : maskSize r = 3)
    (g : WordMixThreeZeroFiber.G r) (j : Fin 4) (hj : g.val j = 0) : g.val = 0 := by
  let g0 : WordMixThreeZeroFiber.G r := ⟨0, by
    constructor
    · intro i _
      exact congrFun (map_zero WordMixThreeZeroFiber.L) i
    · intro i _
      rfl⟩
  have hh : g = g0 := (WordMixThreeZeroFiber.coordinateEquiv r hr j).injective (by exact hj)
  exact congrArg Subtype.val hh

/-- Incoming eleven has exact input support three, absent on these lower fibers. -/
theorem component_eleven_three_zero (f : WordState → ℝ) (r : Fin 16)
    (hr : maskSize r = 3) (g : WordMixThreeZeroFiber.G r) : component f 11 g.val = 0 := by
  by_cases hs : SupportProfile.activeCount g.val = 3
  · obtain ⟨j, hj⟩ := OneSourceEventMoment.activeCount_three_has_zero g.val hs
    rw [three_zero_input_zero r hr g j hj]
    exact SupportProfile.component_at_zero f 11
  · exact SupportProfile.component_supported f 11 g.val (by exact hs)

theorem component_eleven_three_zero_mass (f : WordState → ℝ) (r : Fin 16)
    (hr : maskSize r = 3) : (∑ g : WordMixThreeZeroFiber.G r, component f 11 g.val) = 0 := by
  exact Finset.sum_eq_zero (fun g _ => component_eleven_three_zero f r hr g)

end AES8.PinnedTwoZeroMass
