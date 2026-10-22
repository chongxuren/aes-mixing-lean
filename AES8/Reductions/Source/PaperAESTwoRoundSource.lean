import AES8.Reductions.Source.PaperProductSource
import AES8.Reductions.Source.PaperAESSourceOrientations
import AESPaper.StartingWord

/-! The paper's two-round source lengths on the actual fixed input support.
The source coordinate includes the initial ShiftRows. The source is uncentered,
including its degree-zero term. This lemma does not itself bound a return. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESTwoRoundSource
open AESMixing PaperSupportProjection PaperFixedSupportBlockLift
open AESPaper.StartingWord (sourceInput)
set_option autoImplicit false

def sourceMask (a : AES.State) (k : Fin 4) : Bool := decide (sourceInput a k = 0)

def energyBound (j w : ℕ) : ℝ :=
  (Nat.choose w j : ℝ) * (2 / (15 * 4294967296) : ℝ)^j *
    (1 / 4294967295 : ℝ)^(w-j)

theorem grouped_source (a : AES.State) :
    AESPaper.GroupedLaw.groupedLaw 0 a =
      PaperProductSource.source AES.wordSuperboxKernel (sourceInput a) := by
  funext x
  exact AESPaper.StartingWord.grouped_initial_product a x

theorem fixed_energy_le (a : AES.State) (j : Fin 5) :
    (∑ x, fixedComponent (0 : AES.Word) (AESPaper.GroupedLaw.groupedLaw 0 a)
      j.val (sourceMask a) x ^ 2) ≤ energyBound j.val (supportCount (sourceMask a)) := by
  rw [grouped_source]
  have h := PaperProductSource.fixed_source_energy_le (0 : AES.Word)
    AESConcrete.AES.word_card_gt_one AES.wordSuperboxKernel AES.word_superbox_pointed
    (sourceInput a) j.val (sourceMask a) (by intro k; simp [sourceMask])
    (2 / (15 * 4294967296)) (by norm_num)
    (fun b _ => (PaperAESSource.all_residual_column_energy_lt_current
      .ordinary .ordinary false b).le)
  simpa only [PaperFixedSupportBlockLift.four_word_count,
    AESConcrete.AES.word_card_exact, Nat.cast_ofNat, show (4294967296 : ℝ) - 1 =
      4294967295 by norm_num, energyBound] using h

theorem fixed_norm_le (a : AES.State) (j : Fin 5) :
    l2 (fixedComponent (0 : AES.Word) (AESPaper.GroupedLaw.groupedLaw 0 a)
      j.val (sourceMask a)) ≤ Real.sqrt (energyBound j.val (supportCount (sourceMask a))) :=
  Real.sqrt_le_sqrt (fixed_energy_le a j)

/-- The factor 2^80 is exactly Q^(5/2) for Q=2^32. -/
theorem scaled_fixed_norm_le (a : AES.State) (j : Fin 5) :
    (2 : ℝ)^80 * l2 (fixedComponent (0 : AES.Word)
      (AESPaper.GroupedLaw.groupedLaw 0 a) j.val (sourceMask a)) ≤
      (2 : ℝ)^80 * Real.sqrt (energyBound j.val (supportCount (sourceMask a))) :=
  mul_le_mul_of_nonneg_left (fixed_norm_le a j) (by positivity)

end AES8.PaperAESTwoRoundSource
