import AESPaper.TernaryDegree
import AESPaper.SingleBias

/-!
# Actual four-round J/Z/R terms and the single-bias budget

The input to the final parallel superbox is the actual transported grouped
index-zero law. Grouped index one is four physical rounds. Its literal ternary
terms give an exact orthogonal decomposition, and grouping by the number of
R labels recovers the existing residual-word degrees. Bias labels do not
contribute to that count.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.BiasStartup
open AESMixing AESConcrete
open AESPaper.StartingWord (q)
open AESPaper.ManySourceBounds (activeSourceCount)

/-- Actual joint boundary law; no independence of its current words is assumed. -/
def inputLaw (b : AES.State) : AES.WordState → ℝ :=
  GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)

/-- A literal ternary channel term for the actual forward word channel. -/
def channel (a : Fin 4 → Fin 3) : AES.WordState → AES.WordState → ℝ :=
  TernaryTensor.tensorChannel (fun _ : Fin 4 => AES.wordSuperboxKernel) (0 : AES.Word) a

def term (b : AES.State) (a : Fin 4 → Fin 3) : AES.WordState → ℝ :=
  action (channel a) (inputLaw b)

/-- The recurrence uses the final word channel after the actual boundary. -/
theorem grouped_one (b : AES.State) :
    GroupedLaw.groupedLaw 1 b =
      action (coordinateKernel (fun _ : Fin 4 => AES.wordSuperboxKernel)) (inputLaw b) := by
  rw [show (1 : ℕ) = 0+1 by rfl, GroupedRecurrence.groupedLaw_succ]
  rfl

theorem term_projection (b : AES.State) (a : Fin 4 → Fin 3) :
    action (TernaryTensor.tensorProjection (0 : AES.Word) a)
      (GroupedLaw.groupedLaw 1 b) = term b a := by
  rw [grouped_one]
  exact TernaryTensor.project_channel _ (0 : AES.Word)
    (fun _ => AES.word_superbox_pointed) a (inputLaw b)

/-- All eighty-one literal terms sum to the actual grouped four-round law. -/
theorem decomposition (b : AES.State) :
    (fun y => ∑ a : Fin 4 → Fin 3, term b a y) = GroupedLaw.groupedLaw 1 b := by
  rw [grouped_one]
  exact TernaryTensor.channel_decomposition _ (0 : AES.Word)
    (fun _ => AES.word_superbox_pointed) (inputLaw b)

theorem orthogonal (b : AES.State) (a d : Fin 4 → Fin 3) (had : a ≠ d) :
    (∑ y, term b a y * term b d y) = 0 := by
  exact TernaryTensor.channel_orthogonal _ (0 : AES.Word) AES.word_card_gt_one
    (fun _ => AES.word_superbox_pointed) a d had (inputLaw b) (inputLaw b)

theorem energy (b : AES.State) :
    (∑ y, GroupedLaw.groupedLaw 1 b y ^ 2) =
      ∑ a : Fin 4 → Fin 3, ∑ y, term b a y ^ 2 := by
  rw [grouped_one]
  exact TernaryTensor.channel_pythagoras _ (0 : AES.Word) AES.word_card_gt_one
    (fun _ => AES.word_superbox_pointed) (inputLaw b)

/-- These are the original five residual-word components, grouped by R count. -/
theorem degree (b : AES.State) (j : Fin 5) :
    degreeComponent (0 : AES.Word) j (GroupedLaw.groupedLaw 1 b) =
      groupedFamily TernaryDegree.residualIndex (term b) j := by
  rw [grouped_one]
  exact TernaryDegree.degree_channel _ (0 : AES.Word)
    (fun _ => AES.word_superbox_pointed) j (inputLaw b)

theorem degree_energy (b : AES.State) (j : Fin 5) :
    (∑ y, degreeComponent (0 : AES.Word) j (GroupedLaw.groupedLaw 1 b) y ^ 2) =
      ∑ a : Fin 4 → Fin 3, if TernaryDegree.residualIndex a=j then
        (∑ y, term b a y ^ 2) else 0 := by
  rw [grouped_one]
  exact TernaryDegree.degree_channel_energy _ (0 : AES.Word) AES.word_card_gt_one
    (fun _ => AES.word_superbox_pointed) j (inputLaw b)

/-- One bias position, with full-uniform labels at the other three positions. -/
def singleZ (c : Fin 4) : Fin 4 → Fin 3 := fun i => if i=c then 1 else 0

/-- One residual position, with full-uniform labels at the other three positions. -/
def singleR (c : Fin 4) : Fin 4 → Fin 3 := fun i => if i=c then 2 else 0

theorem singleZ_injective : Function.Injective singleZ := by
  intro c d h
  by_contra hne
  have hc := congrFun h c
  simp [singleZ, hne] at hc

theorem singleR_injective : Function.Injective singleR := by
  intro c d h
  by_contra hne
  have hc := congrFun h c
  simp [singleR, hne] at hc

theorem singleZ_residualIndex (c : Fin 4) : TernaryDegree.residualIndex (singleZ c) = 0 := by
  fin_cases c <;> decide

theorem singleR_residualIndex (c : Fin 4) : TernaryDegree.residualIndex (singleR c) = 1 := by
  fin_cases c <;> decide

theorem singleZ_channel (c : Fin 4) : channel (singleZ c) = SingleBias.kernel c := by
  funext y x
  change (∏ i, UniformBias.channelPiece AES.wordSuperboxKernel (0 : AES.Word)
    (singleZ c i) (y i) (x i)) =
      ∏ i, if i=c then SingleBias.Z (y i) (x i) else 1/q
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i=c <;>
    simp [singleZ, hi, UniformBias.channelPiece, UniformBias.uniformKernel,
      SingleBias.Z] <;> norm_num [BinaryWord.card, q]

theorem singleR_channel (c : Fin 4) : channel (singleR c) = SingleResidualJ.kernel c := by
  funext y x
  change (∏ i, UniformBias.channelPiece AES.wordSuperboxKernel (0 : AES.Word)
    (singleR c i) (y i) (x i)) =
      ∏ i, if i=c then ResidualMarginal.R (y i) (x i) else 1/q
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i=c <;>
    simp [singleR, hi, UniformBias.channelPiece, UniformBias.uniformKernel,
      ResidualMarginal.R] <;> norm_num [BinaryWord.card, q]

theorem singleZ_term (b : AES.State) (c : Fin 4) :
    term b (singleZ c) = action (SingleBias.kernel c) (inputLaw b) := by
  unfold term
  rw [singleZ_channel]

theorem singleR_term (b : AES.State) (c : Fin 4) :
    term b (singleR c) = action (SingleResidualJ.kernel c) (inputLaw b) := by
  unfold term
  rw [singleR_channel]

/-- The four single-Z terms in the actual ternary expansion obey the checked
budget. Multiple-Z patterns are not part of this sum. -/
theorem singleZ_total_scaled_energy_lt (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ c : Fin 4, ∑ y, term b (singleZ c) y ^ 2) < 1000001/250000 := by
  simpa only [term, singleZ_channel, inputLaw] using
    SingleBias.actual_total_scaled_energy_lt b hb

/-- The four literal degree-one J-only terms are linked to their actual budget. -/
theorem singleR_total_scaled_energy_lt (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ c : Fin 4, ∑ y, term b (singleR c) y ^ 2) < 92/5 := by
  simpa only [term, singleR_channel, inputLaw] using
    ManySourceBounds.one_R_three_J_total_lt b hb

/-- Injectivity selects four distinct orthogonal single-bias patterns. -/
theorem singleZ_sum_energy (b : AES.State) :
    (∑ y, (∑ c : Fin 4, term b (singleZ c) y) ^ 2) =
      ∑ c : Fin 4, ∑ y, term b (singleZ c) y ^ 2 := by
  exact orthogonal_family_energy _
    (fun c d hcd => orthogonal b _ _ (fun h => hcd (singleZ_injective h)))

theorem singleR_sum_energy (b : AES.State) :
    (∑ y, (∑ c : Fin 4, term b (singleR c) y) ^ 2) =
      ∑ c : Fin 4, ∑ y, term b (singleR c) y ^ 2 := by
  exact orthogonal_family_energy _
    (fun c d hcd => orthogonal b _ _ (fun h => hcd (singleR_injective h)))

/-- The bound concerns the actual sum vector, using its established orthogonality. -/
theorem singleZ_sum_scaled_energy_lt (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ y, (∑ c : Fin 4, term b (singleZ c) y) ^ 2) < 1000001/250000 := by
  rw [singleZ_sum_energy]
  exact singleZ_total_scaled_energy_lt b hb

theorem singleR_sum_scaled_energy_lt (b : AES.State) (hb : 2 ≤ activeSourceCount b) :
    q^5 * (∑ y, (∑ c : Fin 4, term b (singleR c) y) ^ 2) < 92/5 := by
  rw [singleR_sum_energy]
  exact singleR_total_scaled_energy_lt b hb

end AESPaper.BiasStartup
