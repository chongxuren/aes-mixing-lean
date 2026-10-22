import AESConcrete.WordOrientationClosure

/-! Entry interfaces used by the paper's reductions. These statements describe
actual channels; the cited-result adapter and any finite verification have
separate ownership. No external theorem is declared as an axiom here. -/
noncomputable section
namespace AES8.PaperWordEntryBounds
open AESMixing

/-- The ordinary nonzero-source point bound used by the four-round initializer. -/
def OrdinaryBound : Prop :=
  ∀ a b : AES.Word, a ≠ 0 → AES.wordSuperboxKernel b a < (14 / 2^32 : ℝ)

end AES8.PaperWordEntryBounds
