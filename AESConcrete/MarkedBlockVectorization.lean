import AESConcrete.ActivityTensorContraction
import AESConcrete.ActivityWordKernel
import AESConcrete.WordColumnGram

/-!
# Two-sided marked word blocks and their exact vectorization

The eight physical coordinates are output positions followed by input
positions. An input residual is transposed when a matrix is vectorized;
output residuals retain their usual orientation. Activity contractions use
the actual normalized nonorthogonal frame and its inverse metric. These
are exact identities, with no block-energy premise. Constructive scope
only; no attacks, manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MarkedBlockVectorization
open AESMixing AESMixing.AES
open AESConcrete.ActivityFrame
open AESConcrete.ShortenedLineResponse
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordOrientationClosure (wordKernel)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

section Partition
variable {I V X : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [Zero V] [DecidableEq V] [Fintype X]

abbrev Marked (m : I → Bool) := {i : I // m i = true}
abbrev Activity (m : I → Bool) := {i : I // m i ≠ true}

def join (m : I → Bool) (y : Marked m → V) (v : Activity m → V) (i : I) : V :=
  if h : m i = true then y ⟨i,h⟩ else v ⟨i,h⟩

def partitionEquiv (m : I → Bool) :
    (I → V) ≃ (Marked m → V) × (Activity m → V) where
  toFun x := (fun i => x i.val, fun i => x i.val)
  invFun x := join m x.1 x.2
  left_inv x := by
    funext i
    by_cases h : m i = true <;> simp [join, h]
  right_inv x := by
    apply Prod.ext
    · funext i
      simp [join, i.property]
    · funext i
      simp [join, i.property]

def splitResponse (m : I → Bool) (T : Marked m → V → V → ℝ)
    (coord : X → I → V) (y : Marked m → V) (v : Activity m → V) : ℝ :=
  ∑ x : X, (∏ i : Marked m, T i (y i) (coord x i.val)) *
    (∏ i : Activity m, activityMatrix 0 (v i) (coord x i.val))

def fullResponse (m : I → Bool) (T : Marked m → V → V → ℝ)
    (coord : X → I → V) (v : I → V) : ℝ :=
  ∑ x : X, ∏ i : I,
    if h : m i = true then T ⟨i,h⟩ (v i) (coord x i)
    else activityMatrix 0 (v i) (coord x i)

theorem fullResponse_join (m : I → Bool) (T : Marked m → V → V → ℝ)
    (coord : X → I → V) (y : Marked m → V) (v : Activity m → V) :
    fullResponse m T coord (join m y v) = splitResponse m T coord y v := by
  unfold fullResponse splitResponse
  apply Finset.sum_congr rfl
  intro x _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : I => m i = true)]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [join, i.property]
  · apply Finset.prod_congr rfl
    intro i _
    simp [join, i.property]

theorem splitResponse_activity (hV : Fintype.card V = 256)
    (m : I → Bool) (T : Marked m → V → V → ℝ) (coord : X → I → V)
    (y : Marked m → V) :
    action (coordinateKernel (fun _ : Activity m => activityMatrix (0 : V)))
      (splitResponse m T coord y) = splitResponse m T coord y := by
  funext v
  unfold action splitResponse
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have he :
      (∑ w : Activity m → V,
        coordinateKernel (fun _ : Activity m => activityMatrix (0 : V)) v w *
          ((∏ i : Marked m, T i (y i) (coord x i.val)) *
           ∏ i : Activity m, activityMatrix 0 (w i) (coord x i.val))) =
        (∏ i : Marked m, T i (y i) (coord x i.val)) *
          ∏ i : Activity m, activityMatrix 0 (v i) (coord x i.val) := by
    calc
      _ = (∏ i : Marked m, T i (y i) (coord x i.val)) *
          ∑ w : Activity m → V, ∏ i : Activity m,
            activityMatrix 0 (v i) (w i) * activityMatrix 0 (w i) (coord x i.val) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        simp only [coordinateKernel, Finset.prod_mul_distrib]
        ring
      _ = _ := by
        apply congrArg ((∏ i : Marked m, T i (y i) (coord x i.val)) * ·)
        rw [← Fintype.prod_sum (fun (i : Activity m) (w : V) =>
          activityMatrix 0 (v i) w * activityMatrix 0 w (coord x i.val))]
        apply Finset.prod_congr rfl
        intro i _
        exact congrFun (congrFun (activityMatrix_idempotent (0 : V) (by omega))
          (v i)) (coord x i.val)
  exact he

def contractedResponse (m : I → Bool) (T : Marked m → V → V → ℝ)
    (coord : X → I → V) (s : Activity m → Bool) (y : Marked m → V) : ℝ :=
  ActivityTensorContraction.tensorContraction (splitResponse m T coord y) s

/-- The activity contraction retains the same graph/source point on all legs. -/
theorem contractedResponse_formula (hV : Fintype.card V = 256)
    (m : I → Bool) (T : Marked m → V → V → ℝ) (coord : X → I → V)
    (s : Activity m → Bool) (y : Marked m → V) :
    contractedResponse m T coord s y =
      ∑ x : X, (∏ i : Marked m, T i (y i) (coord x i.val)) *
        ∏ i : Activity m, byteFrame (s i) (coord x i.val) := by
  unfold contractedResponse ActivityTensorContraction.tensorContraction splitResponse
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = (∏ i : Marked m, T i (y i) (coord x i.val)) *
        ∑ v : Activity m → V, ∏ i : Activity m,
          byteFrame (s i) (v i) * activityMatrix 0 (v i) (coord x i.val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      simp only [frameColumn, Finset.prod_mul_distrib]
      ring
    _ = _ := by
      apply congrArg ((∏ i : Marked m, T i (y i) (coord x i.val)) * ·)
      rw [← Fintype.prod_sum (fun (i : Activity m) (v : V) =>
        byteFrame (s i) v * activityMatrix 0 v (coord x i.val))]
      apply Finset.prod_congr rfl
      intro i _
      have hf := congrFun
        (ActivityWordKernel.pointed_byteFrame_fixed
          (activityMatrix_pointed (0 : V) (by omega)) (s i)) (coord x i.val)
      change (∑ v : V, activityMatrix 0 (coord x i.val) v * byteFrame (s i) v) =
        byteFrame (s i) (coord x i.val) at hf
      calc
        _ = ∑ v : V, activityMatrix 0 (coord x i.val) v * byteFrame (s i) v := by
          apply Finset.sum_congr rfl
          intro v _
          rw [activityMatrix_symmetric (0 : V) v (coord x i.val)]
          ring
        _ = _ := hf

theorem splitResponse_energy (hV : Fintype.card V = 256)
    (m : I → Bool) (T : Marked m → V → V → ℝ) (coord : X → I → V) :
    (∑ y : Marked m → V, ∑ v : Activity m → V, splitResponse m T coord y v ^ 2) =
      ∑ s : Activity m → Bool, ∑ t : Activity m → Bool,
        frameInverse s t * ∑ y : Marked m → V,
          contractedResponse m T coord s y * contractedResponse m T coord t y := by
  simpa only [pow_two, contractedResponse] using
    ActivityTensorContraction.fixed_family_inner hV
      (splitResponse m T coord) (splitResponse m T coord)
      (splitResponse_activity hV m T coord) (splitResponse_activity hV m T coord)

theorem fullResponse_energy (hV : Fintype.card V = 256)
    (m : I → Bool) (T : Marked m → V → V → ℝ) (coord : X → I → V) :
    (∑ v : I → V, fullResponse m T coord v ^ 2) =
      ∑ s : Activity m → Bool, ∑ t : Activity m → Bool,
        frameInverse s t * ∑ y : Marked m → V,
          contractedResponse m T coord s y * contractedResponse m T coord t y := by
  rw [← (partitionEquiv (V := V) m).symm.sum_comp
    (fun v => fullResponse m T coord v ^ 2), Fintype.sum_prod_type]
  change (∑ y : Marked m → V, ∑ v : Activity m → V,
    fullResponse m T coord (join m y v) ^ 2) = _
  simp_rw [fullResponse_join]
  exact splitResponse_energy hV m T coord

end Partition

section ActualMatrix
abbrev Byte := BinaryWord 8
abbrev Word := Fin 4 → Byte

/-- The block is an actual two-sided product projection of the word kernel. -/
def markedBlock (D E : Byte → Byte → ℝ) (L : Equiv.Perm Word)
    (out inp : Fin 4 → Bool) : Word → Word → ℝ :=
  kernelCompose (productProjection 0 out)
    (kernelCompose (twoSubstitutionKernel D E L) (productProjection 0 inp))

private theorem compose_assoc {A B C D : Type*} [Fintype B] [Fintype C]
    [Fintype D] [DecidableEq D]
    (K : A → B → ℝ) (L : B → C → ℝ) (M : C → D → ℝ) :
    kernelCompose K (kernelCompose L M) = kernelCompose (kernelCompose K L) M := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action]

theorem markedBlock_piece_kernel {D E : Byte → Byte → ℝ}
    (hD : ByteResources D) (hE : ByteResources E) (L : Equiv.Perm Word)
    (out inp : Fin 4 → Bool) :
    markedBlock D E L out inp =
      kernelCompose (coordinateKernel (fun i => bytePiece D (out i)))
        (fun y x => coordinateKernel (fun i => bytePiece E (inp i)) (L.symm y) x) := by
  rw [markedBlock, twoSubstitutionKernel, compose_assoc, compose_assoc,
    substitution_pattern_left hD, ← compose_assoc]
  change kernelCompose (coordinateKernel (fun i => bytePiece D (out i)))
    (fun y x => kernelCompose (substitutionKernel E) (productProjection 0 inp)
      (L.symm y) x) = _
  rw [substitution_pattern_right hE]

theorem markedBlock_graph_formula {D E : Byte → Byte → ℝ}
    (hD : ByteResources D) (hE : ByteResources E) (L : Equiv.Perm Word)
    (out inp : Fin 4 → Bool) (y a : Word) :
    markedBlock D E L out inp y a =
      ∑ x : Word, (∏ i : Fin 4, bytePiece D (out i) (y i) (L x i)) *
        ∏ i : Fin 4, bytePiece E (inp i) (x i) (a i) := by
  rw [markedBlock_piece_kernel hD hE]
  change (∑ z : Word, coordinateKernel (fun i => bytePiece D (out i)) y z *
    coordinateKernel (fun i => bytePiece E (inp i)) (L.symm z) a) = _
  simpa only [Equiv.symm_apply_apply, coordinateKernel] using
    (Equiv.sum_comp L (fun z => coordinateKernel (fun i => bytePiece D (out i)) y z *
      coordinateKernel (fun i => bytePiece E (inp i)) (L.symm z) a)).symm

/-- Vectorization puts the input residual in its adjoint orientation. -/
def residualLeg (D E : Byte → Byte → ℝ) : GraphPosition → Byte → Byte → ℝ :=
  Sum.elim (fun _ y x => residualMatrix D 0 y x)
    (fun _ a x => residualMatrix E 0 x a)

def markedLeg (D E : Byte → Byte → ℝ) (m : GraphPosition → Bool) :
    Marked m → Byte → Byte → ℝ := fun p => residualLeg D E p.val

def vectorizedBlock (D E : Byte → Byte → ℝ)
    (L : Word →+ Word) (m : GraphPosition → Bool) : (GraphPosition → Byte) → ℝ :=
  fullResponse m (markedLeg D E m) (graphCoordinate L)

theorem vectorizedBlock_matrix {D E : Byte → Byte → ℝ}
    (hD : ByteResources D) (hE : ByteResources E)
    (L : Word ≃+ Word) (m : GraphPosition → Bool) (y a : Word) :
    vectorizedBlock D E L.toAddMonoidHom m (Sum.elim y a) =
      markedBlock D E L.toEquiv (fun i => m (Sum.inl i))
        (fun i => m (Sum.inr i)) y a := by
  rw [markedBlock_graph_formula hD hE]
  unfold vectorizedBlock fullResponse
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_sum_type]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    by_cases hm : m (Sum.inl i) = true <;>
      simp [markedLeg, residualLeg, bytePiece, graphCoordinate, hm]
  · apply Finset.prod_congr rfl
    intro i _
    by_cases hm : m (Sum.inr i) = true <;>
      simp [markedLeg, residualLeg, bytePiece, graphCoordinate, hm,
        activityMatrix_symmetric]

theorem markedBlock_hilbertSchmidt_square {D E : Byte → Byte → ℝ}
    (hD : ByteResources D) (hE : ByteResources E)
    (L : Word ≃+ Word) (m : GraphPosition → Bool) :
    (∑ y : Word, ∑ a : Word,
      markedBlock D E L.toEquiv (fun i => m (Sum.inl i))
        (fun i => m (Sum.inr i)) y a ^ 2) =
      ∑ v : GraphPosition → Byte, vectorizedBlock D E L.toAddMonoidHom m v ^ 2 := by
  rw [← (Equiv.sumArrowEquivProdArrow (Fin 4) (Fin 4) Byte).symm.sum_comp
    (fun v => vectorizedBlock D E L.toAddMonoidHom m v ^ 2), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun z : ℝ => z ^ 2) (vectorizedBlock_matrix hD hE L m y a).symm

def actualDiffusionEquiv (inverse : Bool) : Word ≃+ Word :=
  if inverse then byteDiffusionAddEquiv.symm else byteDiffusionAddEquiv

theorem actualDiffusionEquiv_hom (inverse : Bool) :
    (actualDiffusionEquiv inverse).toAddMonoidHom = byteDiffusionHom inverse := by
  cases inverse <;> rfl

theorem actualDiffusionEquiv_perm (inverse : Bool) :
    (actualDiffusionEquiv inverse).toEquiv = byteDiffusionOrientation inverse := by
  cases inverse <;> rfl

/-- All explicit byte orientations and both actual diffusion directions. -/
theorem actual_vectorizedBlock_matrix (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (y a : Word) :
    vectorizedBlock (channel left) (channel right) (byteDiffusionHom inverse) m
      (Sum.elim y a) =
      kernelCompose (productProjection 0 (fun i => m (Sum.inl i)))
        (kernelCompose (wordKernel left right inverse)
          (productProjection 0 (fun i => m (Sum.inr i)))) y a := by
  have h := vectorizedBlock_matrix (channel_resources left) (channel_resources right)
    (actualDiffusionEquiv inverse) m y a
  simpa only [actualDiffusionEquiv_hom, actualDiffusionEquiv_perm, markedBlock,
    wordKernel] using h

/-- Exact inverse-frame expression for every two-sided marked matrix block. -/
theorem actual_markedBlock_energy (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) :
    (∑ y : Word, ∑ a : Word,
      kernelCompose (productProjection 0 (fun i => m (Sum.inl i)))
        (kernelCompose (wordKernel left right inverse)
          (productProjection 0 (fun i => m (Sum.inr i)))) y a ^ 2) =
      ∑ s : Activity m → Bool, ∑ t : Activity m → Bool, frameInverse s t *
        ∑ y : Marked m → Byte,
          contractedResponse m (markedLeg (channel left) (channel right) m)
            (graphCoordinate (byteDiffusionHom inverse)) s y *
          contractedResponse m (markedLeg (channel left) (channel right) m)
            (graphCoordinate (byteDiffusionHom inverse)) t y := by
  have h := markedBlock_hilbertSchmidt_square (channel_resources left)
    (channel_resources right) (actualDiffusionEquiv inverse) m
  simp only [actualDiffusionEquiv_hom, actualDiffusionEquiv_perm, markedBlock,
    wordKernel] at h
  simp only [wordKernel]
  rw [h]
  exact fullResponse_energy (by norm_num [BinaryWord.card]) m
    (markedLeg (channel left) (channel right) m) (graphCoordinate (byteDiffusionHom inverse))

end ActualMatrix

end AESConcrete.MarkedBlockVectorization
