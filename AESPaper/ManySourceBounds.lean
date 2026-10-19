import AESPaper.ManySourceLaw
import AESPaper.FourSourceConvolution
import AESPaper.SingleResidualJ

/-!
# Actual several-source marginal and J-only residual bounds
-/
set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace AESPaper.ManySourceBounds
open AESMixing AESConcrete
open AESPaper.StartingWord (q sourceInput)
open AESPaper.ManySourceLaw

def activeSourceMask (b : AES.State) (i : Fin 4) : Bool := decide (sourceInput b i ≠ 0)

/-- This is the number of source words, not the output residual degree. -/
def activeSourceCount (b : AES.State) : ℕ := residualDegree (activeSourceMask b)

theorem activeSourceMask_iff (b : AES.State) (i : Fin 4) :
    activeSourceMask b i = true ↔ sourceInput b i ≠ 0 := by
  simp [activeSourceMask]

theorem marginal_centered_energy_le (b : AES.State)
    (hb : 2 ≤ activeSourceCount b) (c : Fin 4) :
    CenteredConvolution.centeredEnergy
      (wordMarginal (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) c) ≤ 1/(25*q) := by
  rw [boundary_marginal]
  have he (i : Fin 4) (hi : activeSourceMask b i = true) :
      CenteredConvolution.centeredEnergy (transportedSource b c i) ≤
        1/(5*(Fintype.card AES.Word : ℝ)) := by
    rw [← StartingWord.q_eq_word_card]
    exact transportedSource_centered_energy_le b c i ((activeSourceMask_iff b i).mp hi)
  have h := FourSourceConvolution.fourfold_fifth_bound
    (transportedSource b c) (activeSourceMask b)
    (transportedSource_nonnegative b c) (transportedSource_mass b c) he hb
  simpa only [FourSourceConvolution.fourfold, ← StartingWord.q_eq_word_card] using h

theorem marginal_energy_le (b : AES.State)
    (hb : 2 ≤ activeSourceCount b) (c : Fin 4) :
    (∑ v, (wordMarginal (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) c v-1/q)^2) ≤
      1/(25*q) := by
  simpa only [CenteredConvolution.centeredEnergy, CenteredConvolution.centered,
    CenteredConvolution.uniform, ← StartingWord.q_eq_word_card]
    using marginal_centered_energy_le b hb c

/-- The actual residual response in each observed word has no analytic premise. -/
theorem marginal_response_energy_le (b : AES.State)
    (hb : 2 ≤ activeSourceCount b) (c : Fin 4) :
    (∑ v, action ResidualMarginal.R
      (wordMarginal (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) c) v ^ 2) ≤
        441/(100*q^2) :=
  ResidualMarginal.response_energy_le _ (marginal_energy_le b hb c)

/-- Physical boundary law, with all output correlations retained. -/
theorem one_R_three_J_total_lt (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ c : Fin 4, ∑ y, action (SingleResidualJ.kernel c)
      (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) y ^ 2) < 92/5 := by
  exact SingleResidualJ.total_scaled_energy_lt _ (fun c => marginal_energy_le b hb c)

end AESPaper.ManySourceBounds
