import AES8.Reductions.Support.PaperAESExactSupportStep
import AES8.Reductions.Support.PaperExactSupportLift
import AES8.Math.PaperKernelLinear

/-!
# One-step bounds on literal AES support blocks

The physical zero/full graph estimate discharges every frame hypothesis of
the generic support lift. The scale is the full word cardinality 2^32;
the constant-nonzero support normalizations remain inside the lift.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESSupportStepBound
open AESMixing PaperSupportProjection PaperSupportCoordinates PaperSupportOutside
open PaperSupportFrameJoin PaperAESExactSupportStep PaperKernelBounds
open PaperAESActivityIdentification PaperSupportBlockLift PaperExactSupportLift
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem frame_scaled_norm_le {i j : ℕ} (p q : Label 4)
    (s : Finset (Active p)) (t : Finset (Active q))
    (eo : residualSet p ≃ Fin i) (ei : residualSet q ≃ Fin j)
    (hn : 0 < i+j) (adjoint : Bool) :
    (4294967296 : ℝ) *
      ‖kernelOperator (frameKernel (0 : AES.Word) (actualStep adjoint) p q s t)‖ ≤
      (PaperComparison.stepGraph i s.card j t.card : ℝ) := by
  rw [frameKernel_norm_eq p q s t eo ei adjoint]
  have h := PaperAESActivityStepBound.contracted_stepGraph_norm
    (residualSet p) (residualSet q) (fullSet p s) (fullSet q t) eo ei hn adjoint
  have hreal := PaperKernelReindex.real_kernel_norm_le_complex
    (fun y x => (4294967296 : ℝ) *
      contracted (residualSet p) (residualSet q) (fullSet p s) (fullSet q t) eo ei adjoint y x)
  have hs : fullSet p s \ residualSet p = fullSet p s :=
    Finset.sdiff_eq_self_iff_disjoint.mpr (full_disjoint p s)
  have ht : fullSet q t \ residualSet q = fullSet q t :=
    Finset.sdiff_eq_self_iff_disjoint.mpr (full_disjoint q t)
  rw [hs, ht, full_card, full_card] at h
  have he := hreal.trans h
  rw [PaperKernelLinear.operator_smul, norm_smul] at he
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4294967296)] at he
  exact he

def graphCap (i j a b : ℕ) : ℝ :=
  (PaperComparison.stepGraph i a j b : ℝ) / 4294967296

theorem graphCap_nonneg (i j a b : ℕ) : 0 ≤ graphCap i j a b := by
  unfold graphCap PaperComparison.stepGraph
  dsimp only
  split_ifs
  · unfold PaperComparison.C PaperComparison.E PaperComparison.qp PaperComparison.sqrtQ
    positivity
  · norm_num

theorem frame_norm_le {i j : ℕ} (p q : Label 4)
    (s : Finset (Active p)) (t : Finset (Active q))
    (hp : residualCount p.1 = i) (hq : residualCount q.1 = j)
    (hn : 0 < i+j) (adjoint : Bool) :
    ‖kernelOperator (frameKernel (0 : AES.Word) (actualStep adjoint) p q s t)‖ ≤
      graphCap i j s.card t.card := by
  let eo : residualSet p ≃ Fin i := Finset.equivFinOfCardEq hp
  let ei : residualSet q ≃ Fin j := Finset.equivFinOfCardEq hq
  have h := frame_scaled_norm_le p q s t eo ei hn adjoint
  exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 4294967296)).mpr (by
    simpa only [mul_comm] using h)

/-- All input and output supports, acting on arbitrary already-projected data. -/
theorem grouped_norm_le (i t j u : Fin 5) (hn : 0 < i.val+j.val)
    (adjoint : Bool) (f : AES.WordState → ℝ) :
    l2 (component (0 : AES.Word)
      (action (actualStep adjoint) (component 0 f j.val u.val)) i.val t.val) ≤
      (fixedBound AES.Word i.val t.val j.val u.val (graphCap i.val j.val) *
        Real.sqrt (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
          (Nat.choose 4 u.val * Nat.choose u.val j.val))) *
        l2 (component (0 : AES.Word) f j.val u.val) := by
  apply PaperExactSupportLift.grouped_norm_le 0
    (by norm_num [AES.word_card, BinaryWord.card]) (actualStep adjoint) i t j u
    (graphCap i.val j.val) (graphCap_nonneg i.val j.val)
  intro p q s r
  exact frame_norm_le p.val q.val s r p.property.2.1 q.property.2.1 hn adjoint

/-- Fixed input support, with only residual-position multiplicity on that side. -/
theorem fixed_input_norm_le (i t j : Fin 5) (mask : Fin 4 → Bool)
    (hn : 0 < i.val+j.val) (adjoint : Bool) (f : AES.WordState → ℝ) :
    l2 (component (0 : AES.Word)
      (action (actualStep adjoint) (PaperFixedSupportBlockLift.fixedComponent 0 f j.val mask))
      i.val t.val) ≤
      (fixedBound AES.Word i.val t.val j.val (supportCount mask) (graphCap i.val j.val) *
        Real.sqrt (((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
          Nat.choose (supportCount mask) j.val)) *
        l2 (PaperFixedSupportBlockLift.fixedComponent (0 : AES.Word) f j.val mask) := by
  apply PaperExactSupportLift.fixed_input_norm_le 0
    (by norm_num [AES.word_card, BinaryWord.card]) (actualStep adjoint) i t j mask
    (graphCap i.val j.val) (graphCap_nonneg i.val j.val)
  intro p q s r
  exact frame_norm_le p.val (q.val,mask) s r p.property.2.1 q.property.2 hn adjoint

end AES8.PaperAESSupportStepBound
