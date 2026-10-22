import AES8.Reductions.Source.PaperAESSourceMDS
import AES8.Reductions.Source.PaperAESSourceOrientations
import AES8.Estimates.Word.PaperWordEntryBounds
import AES8.Math.PaperRestrictedDiffusionMass
import AESPaper.StartingWord
import AESPaper.BoundaryZeros

/-!
# Actual word-source adapter for the four-round startup

The source includes initial ShiftRows and retains the four actual channel
columns. Inactive inputs are fixed at zero. The original-law identification,
the checked word-diffusion MDS interface, and further-event probabilities
are separate from the startup's numerical allowances. Constructive only;
no attacks or assumed startup bound. The word-entry resource is an explicit
interface, derived from the cited result in its separate adapter.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperAESStartupSource
open AESMixing PaperRestrictedDiffusion
open AESPaper.StartingWord (sourceInput)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000

def active (a : AES.State) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => sourceInput a i ≠ 0)

@[simp] theorem mem_active (a : AES.State) (i : Fin 4) :
    i ∈ active a ↔ sourceInput a i ≠ 0 := by simp [active]

def law (a : AES.State) (i : Fin 4) (x : AES.Word) : ℝ :=
  AES.wordSuperboxKernel x (sourceInput a i)

def diffusion : AES.WordState →+ AES.WordState := wordMixAddEquiv.toAddMonoidHom

theorem diffusion_graph_isMDS :
    PaperMDSGram.IsMDS (graph diffusion) 4 :=
  PaperAESSource.graph_isMDS_of_zeroMDS diffusion wordMixAddEquiv_zeroMDS

theorem law_nonneg (a : AES.State) (i : Fin 4) (x : AES.Word) :
    0 ≤ law a i x := AES.word_superbox_pointed.nonnegative _ _

theorem law_mass_one (a : AES.State) (i : Fin 4) :
    (∑ x, law a i x) = 1 := AES.word_superbox_pointed.column_sum _

theorem law_zero (a : AES.State) (i : Fin 4) (hi : i ∈ active a) :
    law a i 0 = 0 :=
  (AES.word_superbox_pointed.zero_row _).trans (if_neg ((mem_active a i).mp hi))

theorem law_point_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (i : Fin 4) (hi : i ∈ active a) (x : AES.Word) :
    law a i x ≤ (14 / 4294967296 : ℝ) := by
  have h := (raw (sourceInput a i) x ((mem_active a i).mp hi)).le
  simpa only [law, show (2 : ℝ)^32 = 4294967296 by norm_num] using h

theorem law_collision_le (a : AES.State) (i : Fin 4) (hi : i ∈ active a) :
    (∑ x, law a i x ^ 2) ≤ (17 / (15 * 4294967296) : ℝ) :=
  (PaperAESSource.all_nonzero_column_energy_lt_current .ordinary .ordinary false
    (sourceInput a i) ((mem_active a i).mp hi)).le

theorem active_nonempty (a : AES.State) (ha : a ≠ 0) : (active a).Nonempty := by
  by_contra h
  have hs : sourceInput a = 0 := by
    funext i
    by_contra hi
    exact h ⟨i, (mem_active a i).mpr hi⟩
  have hshift : AES.shiftRows a = 0 :=
    (map_eq_zero_iff AES.transposeState.symm AES.transposeState.symm.injective).mp hs
  apply ha
  exact (map_eq_zero_iff AES.shiftRowsEquiv AES.shiftRowsEquiv.injective).mp hshift

/-- Removing inactive delta factors leaves exactly the actual two-round law. -/
theorem originalLaw_eq_grouped_initial (a : AES.State) (x : AES.WordState) :
    originalLaw (active a) (law a) x = AESPaper.GroupedLaw.groupedLaw 0 a x := by
  rw [AESPaper.StartingWord.grouped_initial_product]
  change originalLaw (active a) (law a) x = ∏ i, law a i (x i)
  by_cases hs : ∀ i ∉ active a, x i = 0
  · rw [originalLaw, if_pos hs, productWeight]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro i _ hi
    have hai : sourceInput a i = 0 := by simpa only [mem_active, not_not] using hi
    rw [law, hai, AES.word_superbox_pointed.zero_column, if_pos (hs i hi)]
  · rw [originalLaw, if_neg hs]
    push Not at hs
    obtain ⟨i, hi, hxi⟩ := hs
    have hai : sourceInput a i = 0 := by simpa only [mem_active, not_not] using hi
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [law, hai, AES.word_superbox_pointed.zero_column, if_neg hxi]

theorem eventMass_eq_grouped_initial (a : AES.State) (zeros : Finset (Fin 4))
    (event : AES.WordState → Prop) :
    eventMass diffusion (active a) zeros (law a) event =
      ∑ x : AES.WordState, if (∀ i ∈ zeros, diffusion x i = 0) ∧ event x
        then AESPaper.GroupedLaw.groupedLaw 0 a x else 0 := by
  rw [eventMass_eq_originalLaw]
  simp_rw [originalLaw_eq_grouped_initial]

theorem jointMarginal_eq_grouped_initial (a : AES.State)
    (zeros observed : Finset (Fin 4)) (event : AES.WordState → Prop)
    (y : observed → AES.Word) :
    paperJointMarginal diffusion (active a) zeros observed (law a) event y =
      ∑ x : AES.WordState, if (∀ i ∈ zeros, diffusion x i = 0) ∧ event x ∧
        (fun i : observed => diffusion x i.val) = y
        then AESPaper.GroupedLaw.groupedLaw 0 a x else 0 := by
  rw [paperJointMarginal_eq_originalLaw]
  simp_rw [originalLaw_eq_grouped_initial]

/-- The impossible branch uses actual off-zero source support. -/
theorem eventMass_zero (a : AES.State) (ha : a ≠ 0) (zeros : Finset (Fin 4))
    (hz : (active a).card ≤ zeros.card) (event : AES.WordState → Prop) :
    eventMass diffusion (active a) zeros (law a) event = 0 := by
  obtain ⟨i, hi⟩ := active_nonempty a ha
  exact actual_event_mass_eq_zero diffusion diffusion_graph_isMDS (active a) zeros
    hz (law a) ⟨i, hi, law_zero a i hi⟩ event

theorem specified_zero_mass_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (zeros : Finset (Fin 4))
    (event : AES.WordState → Prop) :
    eventMass diffusion (active a) zeros (law a) event ≤
      zeroEventBound (active a).card zeros.card (14 / 4294967296)
        (17 / (15 * 4294967296)) :=
  paper_zero_event_mass_bound diffusion diffusion_graph_isMDS (active a) zeros
    (active_nonempty a ha) (law a) event _ _ (by norm_num) (by norm_num)
    (fun i _ x => law_nonneg a i x) (fun i _ => law_mass_one a i)
    (fun i hi x => law_point_le raw a i hi x) (fun i hi => law_collision_le a i hi)
    (fun i hi => law_zero a i hi)

/-- Execution correspondence: this is the actual four-round law. -/
theorem grouped_four_round_response (a : AES.State) :
    AESPaper.GroupedLaw.groupedLaw 1 a =
      AESConcrete.WordColumnGram.tensorResponse (fun _ : Fin 4 => AES.wordSuperboxKernel)
        diffusion (AESPaper.GroupedLaw.groupedLaw 0 a) := by
  rw [AESPaper.GroupedRecurrence.groupedLaw_succ,
    AESPaper.BoundaryZeros.H_Pi_eq_wordStep]
  rfl

end AES8.PaperAESStartupSource
