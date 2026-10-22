import AES8.Reductions.Support.PaperAESSupportReturnBound

/-! The first return retains the fixed input support. This removes the
number of possible input supports from the support-lifting coefficient.
The equal-Fourier finite entry premise is explicit, as in the grouped return. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperFixedSupportReturn
open AESMixing PaperSupportProjection PaperFixedSupportBlockLift
open PaperExactSupportLift PaperAESSupportReturnBound
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem norm_le (i t j : Fin 5) (mask : Fin 4 → Bool)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry)
    (f : AES.WordState → ℝ) :
    l2 (component (0 : AES.Word)
      (action ReturnCentering.physicalReturnKernel (fixedComponent 0 f j.val mask))
      i.val t.val) ≤
      (fixedBound AES.Word i.val t.val j.val (supportCount mask) (graphCap i.val j.val) *
        Real.sqrt (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
          Nat.choose (supportCount mask) j.val)) *
        l2 (fixedComponent (0 : AES.Word) f j.val mask) := by
  apply PaperExactSupportLift.fixed_input_norm_le 0
    (by norm_num [AES.word_card, BinaryWord.card]) ReturnCentering.physicalReturnKernel
    i t j mask (graphCap i.val j.val) (graphCap_nonneg i.val j.val)
  intro p q s r
  exact frame_norm_le p.val (q.val,mask) s r p.property.2.1 q.property.2 hentry

end AES8.PaperFixedSupportReturn
