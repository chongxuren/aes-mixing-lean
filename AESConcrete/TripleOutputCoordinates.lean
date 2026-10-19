import AESConcrete.ActivityWordKernel
import AESConcrete.ShortenedLineGeometry

/-!
# Exact separation of three marked outputs and one activity output

The coordinate equivalence preserves all four physical byte labels. It
splits products and counting-measure sums without a scale factor. This
connects the actual projected word kernel to the previously checked graph
response in its original output space. Constructive mathematics only.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TripleOutputCoordinates
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ActivityFrame
open AESConcrete.ActivityWordKernel
open AESConcrete.ActivityGraphContraction
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.WordOrientationClosure (wordKernel)

set_option maxRecDepth 65536

private theorem unique_unmarked : ∀ (out : Fin 16) (r k : Fin 4),
    maskSize out = 3 → maskBit out r ≠ true → maskBit out k ≠ true → k = r := by decide

def splitIndex {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) : Fin 3 ⊕ Unit ≃ Fin 4 :=
  Equiv.ofBijective (Sum.elim (fun i => (e i).val) (fun _ => r))
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨by
      intro x y h
      cases x with
      | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (e.injective (Subtype.ext h))
        | inr u =>
          have hh : (e i).val = r := h
          exact (hr (hh ▸ (e i).property)).elim
      | inr u =>
        cases y with
        | inl j =>
          have hh : r = (e j).val := h
          exact (hr (hh.symm ▸ (e j).property)).elim
        | inr v => cases u; cases v; rfl,
      by simp⟩)

theorem splitIndex_inl {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (i : Fin 3) :
    splitIndex e r hr (Sum.inl i) = (e i).val := rfl

theorem splitIndex_inr {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (u : Unit) :
    splitIndex e r hr (Sum.inr u) = r := rfl

theorem product_split {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (f : Fin 4 → ℝ) :
    (∏ k, f k) = (∏ i : Fin 3, f (e i).val) * f r := by
  have h := (splitIndex e r hr).prod_comp f
  simpa only [Fintype.prod_sum_type, splitIndex_inl, splitIndex_inr,
    Fintype.prod_unique] using h.symm

def outputEquiv {V : Type*} (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true) :
    (Fin 4 → V) ≃ ((Fin 3 → V) × V) where
  toFun y := (fun i => y (e i).val, y r)
  invFun p k := if h : maskBit out k = true then p.1 (e.symm ⟨k,h⟩) else p.2
  left_inv y := by
    funext k
    by_cases hk : maskBit out k = true
    · simp only [hk, dite_true]
      exact congrArg y (congrArg Subtype.val (e.apply_symm_apply ⟨k,hk⟩))
    · simp only [hk, dite_false]
      exact congrArg y (unique_unmarked out r k hout hr hk).symm
  right_inv p := by
    apply Prod.ext
    · funext i
      dsimp only
      rw [dif_pos (e i).property]
      change p.1 (e.symm (e i)) = p.1 i
      rw [Equiv.symm_apply_apply]
    · dsimp only
      rw [dif_neg hr]

theorem sum_split {V : Type*} [Fintype V] (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (r : Fin 4) (hr : maskBit out r ≠ true)
    (f : (Fin 3 → V) → V → ℝ) :
    (∑ y : Fin 4 → V, f (fun i => y (e i).val) (y r)) =
      ∑ z : Fin 3 → V, ∑ v : V, f z v := by
  have h := (outputEquiv out hout e r hr).sum_comp (fun p => f p.1 p.2)
  simpa only [outputEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type] using h

/-- Physical three-residual word response is exactly the graph response. -/
theorem actual_word_graph_response (left right : Orientation) (inverse : Bool)
    (out : Fin 16) (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (a : Fin 16) (y : Fin 4 → Byte) :
    action (productProjection 0 (maskBit out))
      (action (wordKernel left right inverse) (frameColumn (maskBit a))) y =
      graphResponse (byteDiffusionHom inverse) a r (markedPositions e)
        (fun _ => leg left false) (fun i => y (e i).val) (y r) := by
  rw [actual_projected_word_frame]
  unfold graphResponse
  apply Finset.sum_congr rfl
  intro x _
  rw [product_split e r hr]
  have hmarked (i : Fin 3) :
      bytePiece (channel left) (maskBit out (e i).val) (y (e i).val)
        (byteDiffusionHom inverse x (e i).val) =
      leg left false (y (e i).val)
        (graphCoordinate (byteDiffusionHom inverse) x (markedPositions e i)) := by
    simp only [(e i).property, bytePiece, if_true]
    rfl
  simp_rw [hmarked]
  have hrfalse : maskBit out r = false := Bool.eq_false_iff.mpr hr
  simp only [hrfalse, bytePiece, Bool.false_eq_true, if_false]

theorem actual_centered_word_graph_response (left right : Orientation) (inverse : Bool)
    (out : Fin 16) (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (a : Fin 16) (y : Fin 4 → Byte) :
    action (productProjection 0 (maskBit out))
      (action (residualMatrix (wordKernel left right inverse) 0) (frameColumn (maskBit a))) y =
      graphResponse (byteDiffusionHom inverse) a r (markedPositions e)
        (fun _ => leg left false) (fun i => y (e i).val) (y r) := by
  rw [centered_pattern_action (by norm_num [BinaryWord.card]) _ _ (e 0).val (e 0).property]
  exact actual_word_graph_response left right inverse out e r hr a y

/-- Exact fixed-triple Gram identity for the actual centered word kernel. -/
theorem actual_centered_word_triple_inner (left right : Orientation) (inverse : Bool)
    (out : Fin 16) (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (r : Fin 4) (hr : maskBit out r ≠ true) (a a' : Fin 16) :
    (∑ y : Fin 4 → Byte,
      action (productProjection 0 (maskBit out))
        (action (residualMatrix (wordKernel left right inverse) 0) (frameColumn (maskBit a))) y *
      action (productProjection 0 (maskBit out))
        (action (residualMatrix (wordKernel left right inverse) 0) (frameColumn (maskBit a'))) y) =
    ∑ b : Bool, ∑ c : Bool, byteInverse b c * ∑ z : Fin 3 → Byte,
      ActivityFrameContraction.contraction
        (graphResponse (byteDiffusionHom inverse) a r (markedPositions e)
          (fun _ => leg left false) z) b *
      ActivityFrameContraction.contraction
        (graphResponse (byteDiffusionHom inverse) a' r (markedPositions e)
          (fun _ => leg left false) z) c := by
  simp_rw [actual_centered_word_graph_response left right inverse out e r hr]
  rw [sum_split out hout e r hr (fun z v =>
    graphResponse (byteDiffusionHom inverse) a r (markedPositions e)
      (fun _ => leg left false) z v *
    graphResponse (byteDiffusionHom inverse) a' r (markedPositions e)
      (fun _ => leg left false) z v)]
  have h := graphResponse_inner (by norm_num [BinaryWord.card])
    (byteDiffusionHom inverse) a a' r (markedPositions e) (fun _ => leg left false)
  simp_rw [ActivityGraphContraction.graphResponse_contraction
    (V := Byte) (by norm_num [BinaryWord.card])]
  exact h

end AESConcrete.TripleOutputCoordinates
