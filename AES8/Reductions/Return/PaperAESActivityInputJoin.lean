import AES8.Reductions.Return.PaperAESActivityInputResponse

/-! The literal one-sided frame response as a shortened actual AES graph.
The physical retained coordinates and both frame assignments remain explicit.
No scalar response norm or activity-input norm is assumed. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputJoin
open AESMixing PaperWordGraphCode PaperAESActivityInputResponse
open PaperAESActivityIdentification
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

/-- Summing the actual marked tuple first retains the genuine graph weight. -/
theorem response_graph (M U : Finset Position) (adjoint : Bool) (y : M → AES.Word) :
    response M U adjoint y = ∑ c : wordGraph,
      (∏ p : M, AESConcrete.WordFourierVariants.baseResidual adjoint (y p) (c.val p.val)) *
        graphWeight M U c := by
  unfold response action graphContraction
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  have he (z : M → AES.Word) :
      coordinateKernel (fun _ : M => AESConcrete.WordFourierVariants.baseResidual adjoint) y z *
      (((if (fun p : M => c.val p.val) = z then 1 else 0) *
      (∏ p : U, WordActivityFrame.wordFrame 0 true (c.val p.val))) *
      ∏ p : zeroPositions M U, WordActivityFrame.wordFrame 0 false (c.val p.val)) =
      if (fun p : M => c.val p.val) = z then
        coordinateKernel (fun _ : M => AESConcrete.WordFourierVariants.baseResidual adjoint) y z *
          graphWeight M U c else 0 := by
    split_ifs <;> simp [graphWeight]
  simp_rw [he]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, coordinateKernel]

def outputMarked (O : Finset (Fin 4)) : Finset Position := marked O ∅

def outputEquiv (O : Finset (Fin 4)) : outputMarked O ≃ O where
  toFun p := match hp : p.val with
    | Sum.inl k => False.elim (by have h := p.property; simp [outputMarked,marked,hp] at h)
    | Sum.inr k => ⟨k,by simpa [outputMarked,marked,hp] using p.property⟩
  invFun p := ⟨Sum.inr p.val,by simpa [outputMarked,marked] using p.property⟩
  left_inv p := by
    rcases p with ⟨p,hp⟩
    cases p with
    | inl k => exact False.elim (by simp [outputMarked,marked] at hp)
    | inr k => rfl
  right_inv p := rfl

def frameResponse (O A B : Finset (Fin 4)) (adjoint : Bool) (y : O → AES.Word) : ℝ :=
  ∑ x : AES.WordState,
    ((∏ p : O, AESConcrete.WordFourierVariants.baseResidual adjoint
      (y p) (AESConcrete.WordCrossZero.wordMixAddEquiv x p.val)) *
      (∏ k : Fin 4, if k ∈ O then 1 else
        WordActivityFrame.wordFrame 0 (decide (k ∈ A))
          (AESConcrete.WordCrossZero.wordMixAddEquiv x k))) *
      ∏ k : Fin 4, WordActivityFrame.wordFrame 0 (decide (k ∈ B)) (x k)

/-- The graph reindexing contributes counting coefficient one. -/
theorem frameResponse_eq (O A B : Finset (Fin 4)) (adjoint : Bool) (y : O → AES.Word) :
    frameResponse O A B adjoint y =
      response (outputMarked O) (uniform O ∅ A B) adjoint
        (fun p => y (outputEquiv O p)) := by
  rw [response_graph]
  rw [← (PaperRestrictedDiffusion.graphEquiv
      AESConcrete.WordCrossZero.wordMixAddEquiv.toAddMonoidHom).sum_comp]
  unfold frameResponse
  apply Finset.sum_congr rfl
  intro x _
  have hW := graphWeight_physical O ∅ A B
    ((PaperRestrictedDiffusion.graphEquiv AESConcrete.WordCrossZero.wordMixAddEquiv.toAddMonoidHom) x)
  change graphWeight (outputMarked O) (uniform O ∅ A B) _ = _ at hW
  rw [hW]
  have hp : (∏ p : outputMarked O,
      AESConcrete.WordFourierVariants.baseResidual adjoint
        (y (outputEquiv O p))
        ((PaperRestrictedDiffusion.graphEquiv AESConcrete.WordCrossZero.wordMixAddEquiv.toAddMonoidHom x).val p.val)) =
      ∏ p : O, AESConcrete.WordFourierVariants.baseResidual adjoint
        (y p) (AESConcrete.WordCrossZero.wordMixAddEquiv x p.val) := by
    rw [← (outputEquiv O).prod_comp]
    apply Finset.prod_congr rfl
    intro p _
    rcases p with ⟨p,hp⟩
    cases p with
    | inl k => exact False.elim (by simp [outputMarked,marked] at hp)
    | inr k => rfl
  rw [hp]
  simp only [graphEquiv_input,graphEquiv_output]
  simp
  ring

def tupleEquiv (O : Finset (Fin 4)) :
    (outputMarked O → AES.Word) ≃ (O → AES.Word) where
  toFun y p := y ((outputEquiv O).symm p)
  invFun y p := y (outputEquiv O p)
  left_inv y := by funext p; simp
  right_inv y := by funext p; simp

theorem frameResponse_energy (O A B : Finset (Fin 4)) (d : ℕ)
    (hdim : (zeroPositions (outputMarked O) (uniform O ∅ A B)).card+d=4)
    (hd0 : 0 < d) (hdn : d < O.card) (adjoint : Bool) :
    (∑ y : O → AES.Word, frameResponse O A B adjoint y ^ 2) ≤
      responseMoment O.card d / wordQ ^ (4-O.card) := by
  have hc : (outputMarked O).card = O.card := by simp [outputMarked,marked]
  have h := response_energy (outputMarked O) (uniform O ∅ A B)
    (marked_uniform_disjoint O ∅ A B) d hdim hd0 (by omega)
    (by have ho := Finset.card_le_card (Finset.subset_univ O); simp only [Finset.card_univ,Fintype.card_fin] at ho; omega) adjoint
  rw [← (tupleEquiv O).symm.sum_comp
    (fun y => response (outputMarked O) (uniform O ∅ A B) adjoint y ^ 2)] at h
  simpa only [hc,frameResponse_eq,tupleEquiv,Equiv.coe_fn_symm_mk] using h

end AES8.PaperAESActivityInputJoin
