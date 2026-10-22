import AES8.Reductions.Support.SupportOutput
import AES8.Reductions.Support.PaperRoundedOutput

/-!
# Current quadrature output on the physical fourteen-coordinate profile

The paper and the historical route share the fourteen physical projections.
Their output functionals differ. This leaf supplies the exact current formula
without altering historical consumers or assuming a profile-distance bridge.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperPhysicalOutput
open AESMixing AESMixing.AES AESPaper.RareActivity

/-- The literal four-word functional in the current coordinate order. -/
def psi (v : Profile) : ℝ :=
  2 * (v 0 / 2 ^ (47 : ℕ) + 5 * v 1 / 2 ^ (33 : ℕ) + v 2 / 2 ^ (15 : ℕ)) +
    Real.sqrt (v 4 ^ 2) / 2 ^ (47 : ℕ) +
    5 * Real.sqrt (v 5 ^ 2 + v 8 ^ 2) / 2 ^ (33 : ℕ) +
    Real.sqrt (v 6 ^ 2 + v 9 ^ 2 + v 11 ^ 2) / 2 ^ (15 : ℕ) +
    Real.sqrt (v 7 ^ 2 + v 10 ^ 2 + v 12 ^ 2 + v 13 ^ 2)

/-- Any injectively selected family in one support cell is summed before
applying Cauchy--Schwarz. No sign condition is imposed on the error. -/
theorem support_sum_l1 {J : Type*} [Fintype J] (idx : J → Fin 14)
    (hinj : Function.Injective idx) (t : ℕ)
    (ht : ∀ j, SupportProfile.supportSize (idx j) = t)
    (hcard : ((SupportOutput.activeCell t).card : ℝ) ≤ SupportOutput.supportFactor t ^ 2)
    (f : WordState → ℝ) :
    l1 (fun x => ∑ j, SupportProfile.component f (idx j) x) ≤
      SupportOutput.supportFactor t * Real.sqrt (∑ j, SupportProfile.profile f (idx j) ^ 2) := by
  have hs : ∀ x, x ∉ SupportOutput.activeCell t →
      (∑ j, SupportProfile.component f (idx j) x) = 0 := by
    intro x hx
    have hx' : SupportProfile.activeCount x ≠ t := by
      simpa only [SupportOutput.mem_activeCell] using hx
    apply Finset.sum_eq_zero
    intro j _
    exact SupportProfile.component_supported f (idx j) x (by simpa only [ht j] using hx')
  have horth (i j : J) (hij : i ≠ j) :
      (∑ x, SupportProfile.component f (idx i) x * SupportProfile.component f (idx j) x) = 0 :=
    SupportProfile.component_orthogonal f f _ _ (fun he => hij (hinj he))
  have h := SupportOutput.l1_le_of_supported_card (SupportOutput.activeCell t)
    (fun x => ∑ j, SupportProfile.component f (idx j) x) (SupportOutput.supportFactor t)
    (SupportOutput.supportFactor_nonneg t) hs hcard
  rw [SupportOutput.orthogonal_sum_l2 _ horth] at h
  exact h

def pairIndex : Fin 2 → Fin 14 := ![5,8]
def tripleIndex : Fin 3 → Fin 14 := ![6,9,11]

theorem pairIndex_injective : Function.Injective pairIndex := by decide
theorem tripleIndex_injective : Function.Injective tripleIndex := by decide

theorem support_sensitive_tv (f : WordState → ℝ) (hz : f 0 = 0)
    (hsum : (∑ x, f x) = 0) :
    l1 f / 2 ≤ (2 : ℝ) ^ (63 : ℕ) * psi (SupportProfile.profile f) := by
  have ha := SupportOutput.activity_l1 f hz hsum
  have h0 := SupportOutput.component_l1 f 0 (by decide)
  have h1 := SupportOutput.component_l1 f 1 (by decide)
  have h2 := SupportOutput.component_l1 f 2 (by decide)
  have h4 := SupportOutput.component_l1 f 4 (by decide)
  have hp := support_sum_l1 pairIndex pairIndex_injective 2
    (by intro i; fin_cases i <;> rfl) SupportOutput.activeCell_card_two f
  have ht := support_sum_l1 tripleIndex tripleIndex_injective 3
    (by intro i; fin_cases i <;> rfl) SupportOutput.activeCell_card_three f
  have hr := SupportOutput.residual_l1 f
  have htri : l1 f ≤ l1 (SupportProfile.activity f) + l1 (SupportProfile.component f 4) +
      l1 (fun x => ∑ i : Fin 2, SupportProfile.component f (pairIndex i) x) +
      l1 (fun x => ∑ i : Fin 3, SupportProfile.component f (tripleIndex i) x) +
      l1 (fun x => ∑ i : Fin 4, SupportProfile.component f (SupportOutput.residualIndex i) x) := by
    have hd (x : WordState) : f x = SupportProfile.activity f x + SupportProfile.component f 4 x +
        (∑ i : Fin 2, SupportProfile.component f (pairIndex i) x) +
        (∑ i : Fin 3, SupportProfile.component f (tripleIndex i) x) +
        (∑ i : Fin 4, SupportProfile.component f (SupportOutput.residualIndex i) x) := by
      rw [← SupportProfile.component_decomposition f hz x,
        SupportProfile.activity_decomposition f hz x]
      simp [Fin.sum_univ_succ, pairIndex, tripleIndex, SupportOutput.residualIndex]
      ring
    unfold l1
    calc
      _ ≤ ∑ x, (|SupportProfile.activity f x| + |SupportProfile.component f 4 x| +
          |∑ i : Fin 2, SupportProfile.component f (pairIndex i) x| +
          |∑ i : Fin 3, SupportProfile.component f (tripleIndex i) x| +
          |∑ i : Fin 4, SupportProfile.component f (SupportOutput.residualIndex i) x|) := by
        apply Finset.sum_le_sum
        intro x _
        rw [hd]
        exact (abs_add_le _ _).trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add
            ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)
      _ = _ := by simp only [Finset.sum_add_distrib]
  change l1 (SupportProfile.component f 0) ≤ (2 : ℝ) ^ (17 : ℕ) * SupportProfile.profile f 0 at h0
  change l1 (SupportProfile.component f 1) ≤ (5 * (2 : ℝ) ^ (31 : ℕ)) * SupportProfile.profile f 1 at h1
  change l1 (SupportProfile.component f 2) ≤ (2 : ℝ) ^ (49 : ℕ) * SupportProfile.profile f 2 at h2
  change l1 (SupportProfile.component f 4) ≤ (2 : ℝ) ^ (17 : ℕ) * SupportProfile.profile f 4 at h4
  simp only [Fin.sum_univ_two, pairIndex, Matrix.cons_val_zero, Matrix.cons_val_one] at hp
  simp only [Fin.sum_univ_succ, tripleIndex, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero] at ht
  change _ ≤ (5 * (2 : ℝ) ^ (31 : ℕ)) * _ at hp
  change _ ≤ (2 : ℝ) ^ (49 : ℕ) * _ at ht
  simp only [Fin.sum_univ_two, pairIndex, Matrix.cons_val_zero, Matrix.cons_val_one] at htri
  simp only [Fin.sum_univ_succ, tripleIndex, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.sum_univ_zero, add_zero] at htri
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc] at hr
  unfold psi
  rw [Real.sqrt_sq (SupportProfile.profile_nonneg f 4)]
  simp only [add_assoc]
  linarith only [htri, ha, h0, h1, h2, h4, hp, ht, hr]


/-- The historical functional is an upper bound, with its inequality direction
explicit. This permits reuse of conservative envelope-output arithmetic. -/
theorem psi_le_legacy (v : Profile) (hv : ∀ i, 0 ≤ v i) :
    psi v ≤ SupportOutput.psi v := by
  have h2 : Real.sqrt (v 5 ^ 2 + v 8 ^ 2) ≤ v 5 + v 8 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact add_nonneg (hv 5) (hv 8)
    · nlinarith [mul_nonneg (hv 5) (hv 8)]
  have h3 : Real.sqrt (v 6 ^ 2 + v 9 ^ 2 + v 11 ^ 2) ≤ v 6 + v 9 + v 11 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact add_nonneg (add_nonneg (hv 6) (hv 9)) (hv 11)
    · nlinarith [mul_nonneg (hv 6) (hv 9), mul_nonneg (hv 6) (hv 11),
        mul_nonneg (hv 9) (hv 11)]
  unfold psi SupportOutput.psi
  rw [Real.sqrt_sq (hv 4)]
  linarith only [h2, h3]

/-- Literal diagonal-scaled current functional. -/
def Phi (z : Profile) : ℝ := psi (physical z)

theorem Phi_le_legacy (z : Profile) (hz : ∀ i, 0 ≤ z i) : Phi z ≤ AES8.Phi z := by
  exact (psi_le_legacy (physical z) (physical_nonneg hz)).trans_eq (SupportOutput.psi_physical z)

end AES8.PaperPhysicalOutput
