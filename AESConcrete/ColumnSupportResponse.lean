import AESConcrete.RestrictedSourcePushforward
import AESConcrete.ByteGramDiagonal
import AESMixing.SupportRepresentation

/-!
# Exact support components of actual AES word columns

Projecting a byte channel onto a marked coordinate gives its residual;
on an unmarked coordinate the zero and constant-nonzero projections are
preserved. Their physical coordinate products identify an actual word
column's support component with an explicitly normalized support embedding
of the restricted residual response. The unmarked constants supply the
exact counting-measure energy factor. No support energy bound is assumed.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ColumnSupportResponse
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordColumnGram (Byte Word inputColumn tensorResponse actual_word_column_response)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.RestrictedSourcePushforward (outputZeros fullWordSource fullOutputCoordinates)

/-- The zero part of a pointed byte channel is unchanged. -/
theorem zeroPart_channel (left : Orientation) (f : Byte → ℝ) :
    zeroPart 0 (action (channel left) f) = zeroPart 0 f := by
  funext y
  simp only [zeroPart, (channel_resources left).pointed.action_zero]

theorem zeroMatrix_channel (left : Orientation) :
    kernelCompose (zeroMatrix (0 : Byte)) (channel left) = zeroMatrix 0 := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action, zeroMatrix_action, zeroPart_channel]

theorem constantMatrix_channel (left : Orientation) :
    kernelCompose (constantMatrix (0 : Byte)) (channel left) = constantMatrix 0 := by
  apply kernel_action_ext
  intro f
  simp only [kernelCompose_action, constantMatrix_action,
    (channel_resources left).pointed.average_action, zeroPart_channel]

theorem unmarked_support_channel (left : Orientation) (b : Bool) :
    kernelCompose (supportPiece (0 : Byte) false b) (channel left) =
      supportPiece 0 false b := by
  cases b
  · simpa only [supportPiece, Bool.false_eq_true, if_false] using constantMatrix_channel left
  · simpa only [supportPiece, Bool.false_eq_true, if_false, if_true] using zeroMatrix_channel left

/-- The marked residual column, retaining each physical output position. -/
def markedColumn (left : Orientation) (out : Fin 16)
    (y : MaskCoordinates out → Byte) (v : Word) : ℝ :=
  ∏ i : MaskCoordinates out, residualMatrix (channel left) 0 (y i) (v i.val)

def unmarkedConstant (r out : Fin 16) (y : Word) : ℝ :=
  ∏ i : {i : Fin 4 // maskBit out i ≠ true}, supportConstant (maskBit r i.val) (y i.val)

def unmarkedDual (r out : Fin 16) (v : Word) : ℝ :=
  ∏ i : {i : Fin 4 // maskBit out i ≠ true}, supportDualConstant (maskBit r i.val) (v i.val)

/-- Exact one-column factorization after the actual left byte channel. -/
theorem projected_substitution_factor (left : Orientation) (r out : Fin 16)
    (hr : MaskDisjoint r out) (y v : Word) :
    kernelCompose (supportProduct (0 : Byte) (maskBit out) (maskBit r))
      (substitutionKernel (channel left)) y v =
      markedColumn left out (fun i => y i.val) v * unmarkedConstant r out y *
        unmarkedDual r out v := by
  change kernelCompose
    (coordinateKernel (fun i : Fin 4 => supportPiece (0 : Byte) (maskBit out i) (maskBit r i)))
    (coordinateKernel (fun _ : Fin 4 => channel left)) y v = _
  rw [coordinateKernel_compose]
  change (∏ i : Fin 4,
    kernelCompose (supportPiece (0 : Byte) (maskBit out i) (maskBit r i)) (channel left)
      (y i) (v i)) = _
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : Fin 4 => maskBit out i = true)]
  have hm (i : MaskCoordinates out) :
      kernelCompose (supportPiece (0 : Byte) (maskBit out i.val) (maskBit r i.val))
        (channel left) (y i.val) (v i.val) =
        residualMatrix (channel left) 0 (y i.val) (v i.val) := by
    have hi : maskBit r i.val = false :=
      Bool.eq_false_iff.mpr (fun h => hr i.val h i.property)
    rw [i.property, hi]
    simpa only [supportPiece, if_true, Bool.false_eq_true, if_false, degreePiece, bytePiece] using
      congrFun (congrFun (byte_degree_left (channel_resources left) true) (y i.val)) (v i.val)
  have hu (i : {i : Fin 4 // maskBit out i ≠ true}) :
      kernelCompose (supportPiece (0 : Byte) (maskBit out i.val) (maskBit r i.val))
        (channel left) (y i.val) (v i.val) =
        supportConstant (maskBit r i.val) (y i.val) *
          supportDualConstant (maskBit r i.val) (v i.val) := by
    have hi : maskBit out i.val = false := Bool.eq_false_iff.mpr i.property
    rw [hi, unmarked_support_channel]
    exact supportPiece_unmarked (maskBit r i.val) (y i.val) (v i.val)
  simp_rw [hm, hu]
  rw [Finset.prod_mul_distrib]
  change _ * (_ * _) = _ * _ * _
  exact (mul_assoc _ _ _).symm

/-- Exactly r is zero, including all unmarked and marked physical positions. -/
def exactZeroPattern (r : Fin 16) (v : Word) : Prop :=
  ∀ i : Fin 4, v i = 0 ↔ maskBit r i = true

instance (r : Fin 16) : DecidablePred (exactZeroPattern r) := by
  intro v
  unfold exactZeroPattern
  infer_instance

/-- Product of the dual constants on its exact support. -/
theorem unmarkedDual_on_pattern (r out : Fin 16) (hr : MaskDisjoint r out) (v : Word)
    (hv : exactZeroPattern r v) :
    unmarkedDual r out v = ((1 : ℝ)/255) ^ (4-(maskSize r+maskSize out)) := by
  unfold unmarkedDual
  calc
    _ = ∏ i : {i : Fin 4 // maskBit out i ≠ true},
        if maskBit r i.val = true then (1 : ℝ) else (1 : ℝ)/255 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : maskBit r i.val = true
      · have hzero : v i.val = 0 := (hv i.val).mpr hi
        norm_num [supportDualConstant, supportConstant, identityKernel, hi, hzero, BinaryWord.card]
      · have hnonzero : v i.val ≠ 0 := fun hzero => hi ((hv i.val).mp hzero)
        norm_num [supportDualConstant, supportConstant, identityKernel, hi, hnonzero, BinaryWord.card]
    _ = _ := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const_one, Finset.prod_const, one_mul]
      rw [unmarked_coordinate_count r out hr]

/-- Outside the exact support, a dual or marked residual factor vanishes. -/
theorem markedColumn_mul_dual_zero (left : Orientation) (r out : Fin 16)
    (hr : MaskDisjoint r out) (y : MaskCoordinates out → Byte) (v : Word)
    (hv : ¬ exactZeroPattern r v) :
    markedColumn left out y v * unmarkedDual r out v = 0 := by
  classical
  obtain ⟨i, hi⟩ := not_forall.mp hv
  by_cases hri : maskBit r i = true
  · have hvi : v i ≠ 0 := by
      intro hzero
      exact hi ⟨fun _ => hri, fun _ => hzero⟩
    have hoi : maskBit out i ≠ true := hr i hri
    have hd : unmarkedDual r out v = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hoi⟩ : {j : Fin 4 // maskBit out j ≠ true}))
      simp [supportDualConstant, supportConstant, identityKernel, hri, hvi]
    rw [hd, mul_zero]
  · have hvi : v i = 0 := by
      by_contra hnonzero
      exact hi ⟨fun hzero => (hnonzero hzero).elim, fun hr => (hri hr).elim⟩
    by_cases hoi : maskBit out i = true
    · have hm : markedColumn left out y v = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hoi⟩ : MaskCoordinates out))
        change residualMatrix (channel left) 0 (y ⟨i,hoi⟩) (v i) = 0
        rw [hvi]
        exact ByteGramDiagonal.residual_zero_column (channel_resources left) _
      rw [hm, zero_mul]
    · have hd : unmarkedDual r out v = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hoi⟩ : {j : Fin 4 // maskBit out j ≠ true}))
        simp [supportDualConstant, supportConstant, identityKernel, hri, hvi]
      rw [hd, mul_zero]

theorem markedColumn_mul_dual (left : Orientation) (r out : Fin 16)
    (hr : MaskDisjoint r out) (y : MaskCoordinates out → Byte) (v : Word) :
    markedColumn left out y v * unmarkedDual r out v =
      ((1 : ℝ)/255) ^ (4-(maskSize r+maskSize out)) *
        (if exactZeroPattern r v then markedColumn left out y v else 0) := by
  by_cases hv : exactZeroPattern r v
  · rw [if_pos hv, unmarkedDual_on_pattern r out hr v hv]
    exact mul_comm _ _
  · rw [if_neg hv, mul_zero]
    exact markedColumn_mul_dual_zero left r out hr y v hv

theorem projected_substitution_entry (left : Orientation) (r out : Fin 16)
    (hr : MaskDisjoint r out) (y v : Word) :
    kernelCompose (supportProduct (0 : Byte) (maskBit out) (maskBit r))
      (substitutionKernel (channel left)) y v =
      (((1 : ℝ)/255) ^ (4-(maskSize r+maskSize out)) *
        (if exactZeroPattern r v then markedColumn left out (fun i => y i.val) v else 0)) *
          unmarkedConstant r out y := by
  rw [projected_substitution_factor left r out hr]
  calc
    _ = (markedColumn left out (fun i => y i.val) v * unmarkedDual r out v) *
        unmarkedConstant r out y := by ring
    _ = _ := by rw [markedColumn_mul_dual left r out hr]

/-- The full-word event fixes every output position outside r to be nonzero. -/
def nonzeroOutside (inverse : Bool) (r : Fin 16) (x : Word) : Prop :=
  ∀ i : Fin 4, maskBit r i ≠ true → byteDiffusionOrientation inverse x i ≠ 0

instance (inverse : Bool) (r : Fin 16) : DecidablePred (nonzeroOutside inverse r) := by
  intro x
  unfold nonzeroOutside
  infer_instance

theorem exactZeroPattern_diffusion (inverse : Bool) (r : Fin 16) (x : Word) :
    exactZeroPattern r (byteDiffusionOrientation inverse x) ↔
      outputZeros inverse r x ∧ nonzeroOutside inverse r x := by
  constructor
  · intro h
    constructor
    · intro i hi
      exact (h i).mpr hi
    · intro i hi hzero
      exact hi ((h i).mp hzero)
  · rintro ⟨hz, hn⟩ i
    constructor
    · intro hzero
      by_contra hi
      exact hn i hi hzero
    · exact hz i

/-- Projection of a tensor response is composition of its output kernel. -/
theorem project_tensorResponse {X : Type*} [Fintype X]
    (K : Word → Word → ℝ) (D : Byte → Byte → ℝ)
    (coord : X → Word) (mu : X → ℝ) (y : Word) :
    action K (tensorResponse (fun _ : Fin 4 => D) coord mu) y =
      ∑ x : X, kernelCompose K (substitutionKernel D) y (coord x) * mu x := by
  simp only [action, WordColumnGram.tensorResponse, WordColumnGram.tensorColumn,
    substitutionKernel, coordinateKernel, kernelCompose, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Actual column support component, with its exact unmarked normalization. -/
theorem column_support_response (left right : Orientation) (inverse : Bool) (a : Word)
    (r out : Fin 16) (hr : MaskDisjoint r out) :
    action (supportProduct (0 : Byte) (maskBit out) (maskBit r))
      (fun y => wordKernel left right inverse y a) =
      fun y => ((1 : ℝ)/255) ^ (4-(maskSize r+maskSize out)) *
        supportEmbedding r out
          (tensorResponse (fun _ : MaskCoordinates out => residualMatrix (channel left) 0)
            (fullOutputCoordinates inverse out)
            (fullWordSource right inverse a r (nonzeroOutside inverse r))) y := by
  funext y
  rw [actual_word_column_response]
  rw [project_tensorResponse]
  change (∑ x : Word,
    kernelCompose (supportProduct (0 : Byte) (maskBit out) (maskBit r))
      (substitutionKernel (channel left)) y (byteDiffusionOrientation inverse x) *
        inputColumn right a x) =
    ((1 : ℝ)/255) ^ (4-(maskSize r+maskSize out)) *
      ((∑ x : Word, markedColumn left out (fun i => y i.val)
          (byteDiffusionOrientation inverse x) *
            fullWordSource right inverse a r (nonzeroOutside inverse r) x) *
        unmarkedConstant r out y)
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [projected_substitution_entry left r out hr]
  by_cases hp : exactZeroPattern r (byteDiffusionOrientation inverse x)
  · have hs := (exactZeroPattern_diffusion inverse r x).mp hp
    simp only [if_pos hp, fullWordSource, if_pos hs]
    ring
  · have hs : ¬ (outputZeros inverse r x ∧ nonzeroOutside inverse r x) :=
      fun h => hp ((exactZeroPattern_diffusion inverse r x).mpr h)
    simp only [if_neg hp, fullWordSource, if_neg hs, mul_zero, zero_mul]

/-- The unmarked nonzero directions contribute exactly one inverse power
of 255 per physical coordinate after taking counting-measure energy. -/
theorem column_support_energy (left right : Orientation) (inverse : Bool) (a : Word)
    (r out : Fin 16) (hr : MaskDisjoint r out) :
    (∑ y : Word, action (supportProduct (0 : Byte) (maskBit out) (maskBit r))
      (fun v => wordKernel left right inverse v a) y ^ 2) =
      (∑ u : MaskCoordinates out → Byte,
        tensorResponse (fun _ : MaskCoordinates out => residualMatrix (channel left) 0)
          (fullOutputCoordinates inverse out)
          (fullWordSource right inverse a r (nonzeroOutside inverse r)) u ^ 2) /
            (255 : ℝ) ^ (4-(maskSize r+maskSize out)) := by
  simp_rw [congrFun (column_support_response left right inverse a r out hr), mul_pow]
  rw [← Finset.mul_sum, supportEmbedding_energy r out hr]
  norm_num only [BinaryWord.card, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] 
  have hp : (255 : ℝ) ^ (4-(maskSize r+maskSize out)) ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [div_pow, one_pow]
  field_simp [hp] <;> ring

end AESConcrete.ColumnSupportResponse
