import AES8.Reductions.Return.PaperAESReturnFrameBound
import AES8.Reductions.Support.PaperAESExactSupportStep
import AES8.Recurrence.PaperComparisonReal
import AES8.Recurrence.PaperReturnGraphOrder
import AES8.Reductions.Support.PaperSupportProfileJoin

/-! Actual AES high-return estimates on every exact-support block. The
fixed-position return graph and literal support expansion are composed here;
only the finite equal-Fourier entry resource remains. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESSupportReturnBound
open AESMixing PaperSupportProjection PaperSupportCoordinates PaperSupportOutside
open PaperSupportFrameJoin PaperSupportContraction PaperAESExactSupportStep
open PaperKernelBounds PaperSupportBlockLift PaperExactSupportLift
open PaperAESReturnIdentification PaperSupportProfileJoin
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem frameKernel_eq_outside {i j : ℕ} (p q : Label 4)
    (s : Finset (Active p)) (t : Finset (Active q))
    (eo : residualSet p ≃ Fin i) (ei : residualSet q ≃ Fin j)
    (K : AES.WordState → AES.WordState → ℝ)
    (y : Residual p → AES.Word) (x : Residual q → AES.Word) :
    frameKernel (0 : AES.Word) K p q s t y x =
      outsideContract (residualSet p) (residualSet q) (fullSet p s) (fullSet q t)
        eo ei K (valuesEquiv p eo y) (valuesEquiv q ei x) := by
  rw [frameKernel_eq]
  unfold outsideContract kernelCompose
  simp only [PaperActivityMinorTransport.synthesis,
    maskedAnalysis_eq_enum p s eo, maskedAnalysis_eq_enum q t ei]

theorem frameKernel_norm_eq {i j : ℕ} (p q : Label 4)
    (s : Finset (Active p)) (t : Finset (Active q))
    (eo : residualSet p ≃ Fin i) (ei : residualSet q ≃ Fin j)
    (K : AES.WordState → AES.WordState → ℝ) :
    ‖kernelOperator (frameKernel (0 : AES.Word) K p q s t)‖ =
      ‖kernelOperator (outsideContract (residualSet p) (residualSet q)
        (fullSet p s) (fullSet q t) eo ei K)‖ := by
  have he := funext (fun y => funext (fun x => frameKernel_eq_outside p q s t eo ei K y x))
  rw [he]
  exact PaperKernelReindex.kernelOperator_reindex (valuesEquiv q ei) (valuesEquiv p eo) _

theorem frame_scaled_norm_le {i j : ℕ} (p q : Label 4)
    (s : Finset (Active p)) (t : Finset (Active q))
    (eo : residualSet p ≃ Fin i) (ei : residualSet q ≃ Fin j)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    (PaperComparison.q : ℝ)^3 *
      ‖kernelOperator (frameKernel (0 : AES.Word) ReturnCentering.physicalReturnKernel p q s t)‖ ≤
      (PaperComparison.returnGraph i s.card j t.card : ℝ) := by
  rw [frameKernel_norm_eq p q s t eo ei]
  have h := PaperAESReturnFrameBound.high_scaled_norm
    (residualSet p) (residualSet q) (fullSet p s) (fullSet q t) eo ei hentry
  have hs : fullSet p s \ residualSet p = fullSet p s :=
    Finset.sdiff_eq_self_iff_disjoint.mpr (full_disjoint p s)
  have ht : fullSet q t \ residualSet q = fullSet q t :=
    Finset.sdiff_eq_self_iff_disjoint.mpr (full_disjoint q t)
  simpa only [hs, ht, full_card] using h


def graphCap (i j a b : ℕ) : ℝ :=
  (PaperComparison.returnGraph i a j b : ℝ) / (PaperComparison.q : ℝ)^3

theorem graphCap_nonneg (i j a b : ℕ) : 0 ≤ graphCap i j a b := by
  apply div_nonneg _ (by norm_num [PaperComparison.q])
  exact_mod_cast PaperComparison.returnGraph_nonneg i a j b

theorem frame_norm_le {i j : ℕ} (p q : Label 4)
    (s : Finset (Active p)) (t : Finset (Active q))
    (hp : residualCount p.1 = i) (hq : residualCount q.1 = j)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry) :
    ‖kernelOperator (frameKernel (0 : AES.Word) ReturnCentering.physicalReturnKernel p q s t)‖ ≤
      graphCap i j s.card t.card := by
  let eo : residualSet p ≃ Fin i := Finset.equivFinOfCardEq hp
  let ei : residualSet q ≃ Fin j := Finset.equivFinOfCardEq hq
  have h := frame_scaled_norm_le p q s t eo ei hentry
  exact (le_div_iff₀ (by norm_num [PaperComparison.q] : (0 : ℝ) < (PaperComparison.q : ℝ)^3)).mpr
    (by simpa only [mul_comm] using h)

theorem grouped_norm_le (i t j u : Fin 5) (hju : j.val ≤ u.val)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry)
    (f : AES.WordState → ℝ) :
    l2 (component (0 : AES.Word)
      (action ReturnCentering.physicalReturnKernel (component 0 f j.val u.val)) i.val t.val) ≤
      ((PaperComparison.support i.val t.val j.val u.val PaperComparison.returnGraph : ℝ) /
        (PaperComparison.q : ℝ)^3) * l2 (component (0 : AES.Word) f j.val u.val) := by
  have h := PaperExactSupportLift.grouped_norm_le 0
    (by norm_num [AES.word_card, BinaryWord.card]) ReturnCentering.physicalReturnKernel i t j u
    (graphCap i.val j.val) (graphCap_nonneg i.val j.val)
    (fun p q s r => frame_norm_le p.val q.val s r p.property.2.1 q.property.2.1 hentry) f
  exact h.trans (mul_le_mul_of_nonneg_right
    (PaperRationalSupportLift.coefficient_le i t j u hju PaperComparison.returnGraph
      (fun a b => PaperComparison.returnGraph_nonneg i.val a j.val b) ((PaperComparison.q : ℝ)^3)
      (by norm_num [PaperComparison.q])) (l2_nonneg _))

theorem profile_norm_le (a b : Fin 14)
    (hentry : ∀ bit y x,
      |PaperWordMixedGram.mixed false bit bit y x| ≤ PaperAESOverlapResources.entry)
    (f : AES.WordState → ℝ) :
    SupportProfile.profile (TransferAssembly.highReturn (SupportProfile.component f b)) a ≤
      ((PaperComparison.support (SupportProfile.residualDegree a) (SupportProfile.supportSize a)
        (SupportProfile.residualDegree b) (SupportProfile.supportSize b)
        PaperComparison.returnGraph : ℝ) / (PaperComparison.q : ℝ)^3) * SupportProfile.profile f b := by
  rw [ReturnCentering.highReturn_eq_physical_action]
  unfold SupportProfile.profile
  simp only [component_eq]
  exact grouped_norm_le (degreeIndex a) (supportIndex a) (degreeIndex b) (supportIndex b)
    (degree_le_support b) hentry f

end AES8.PaperAESSupportReturnBound
