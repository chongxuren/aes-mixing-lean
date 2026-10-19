import AESPaper.WordMarkedCode
import AESPaper.WordMarkedResponse
import AESConcrete.ActualMarkedUniform

/-!
# Exact uniform marked images of the actual shortened word graph

Only `fiber_card_eq_kernel` and `sum_comp_uniform` are reused from the
additive-fiber section of ActualMarkedUniform. Its markedPositions,
enlargedOutputZeros, enlargedInputZeros and enlarged_zero_count concern only
the eight physical positions and masks, with no alphabet or diffusion map.
All concrete graph, cardinality, pushforward and residual results here are
rebuilt on AES.Word and GroupedRecurrence.boundary.

The exact pushforward uses equal fibers of the actual marked homomorphism;
surjectivity alone is not used as an independence premise. A retained marked
coordinate witness is necessary for cancellation. The actual input residual
is transposed, so its required row sum is the ordinary residual's column sum.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordMarkedUniform
open AESMixing AESConcrete
open AESMixing.AES (maskSize)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros sourceCoordinates rawResponse)
open AESConcrete.ActualMarkedUniform
  (markedPositions enlargedOutputZeros enlargedInputZeros enlarged_zero_count)
open AESPaper.WordMarkedCode (graphSubgroup markedHom sourceSubtypeEquiv)
open AESPaper.WordMarkedMoment (Source)
open AESPaper.WordMarkedResponse (wordMarkedLeg boundaryContractedResponse)
attribute [local instance] Classical.propDecidable

/-- The kernel imposes the marked physical coordinates as further zeros on
the same source word, rather than introducing abstract independent labels. -/
def kernelShorteningEquiv (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (markedHom m s).ker ≃
      ShortenedGraph GroupedRecurrence.boundary.toAddMonoidHom
        (enlargedOutputZeros m s) (enlargedInputZeros m s) where
  toFun c := by
    refine ⟨c.val.val, (graphZeroConditions_union_positions
      GroupedRecurrence.boundary.toAddMonoidHom (outputZeros m s) (inputZeros m s)
      (markedPositions m) c.val.val).mpr ⟨c.val.property, ?_⟩⟩
    intro p hp
    have hm : m p = true := (Finset.mem_filter.mp hp).2
    have hc : markedHom m s c.val = 0 := c.property
    exact congrFun hc (⟨p, hm⟩ : Marked m)
  invFun c := by
    have hc := (graphZeroConditions_union_positions
      GroupedRecurrence.boundary.toAddMonoidHom (outputZeros m s) (inputZeros m s)
      (markedPositions m) c.val).mp c.property
    refine ⟨⟨c.val, hc.1⟩, ?_⟩
    change markedHom m s ⟨c.val, hc.1⟩ = 0
    funext p
    exact hc.2 p.val (by simp [markedPositions, p.property])
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv c := Subtype.ext rfl

/-- Exact actual-word kernel count. Natural subtraction remains explicit;
no unproved surviving dimension is silently substituted. -/
theorem markedHom_kernel_card (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Nat.card (markedHom m s).ker =
      (2^32 : ℕ) ^ (4 - (maskSize (outputZeros m s) + maskSize (inputZeros m s) +
        Fintype.card (Marked m))) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (kernelShorteningEquiv m s),
    mds_graph_zero_count GroupedRecurrence.boundary.toAddMonoidHom
      ActivityKernel.aesBoundary_zeroMDS, enlarged_zero_count, AES.word_card]

/-- The actual marked map is onto all word tuples when the selected positions
fit in the dimension remaining after the prescribed physical zeros. -/
theorem markedHom_surjective (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m) ≤ 4) :
    Function.Surjective (markedHom m s) := by
  have hsource : Nat.card (graphSubgroup (outputZeros m s) (inputZeros m s)) =
      (2^32 : ℕ) ^ (4 - (maskSize (outputZeros m s) + maskSize (inputZeros m s))) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr (sourceSubtypeEquiv m s)]
    exact WordMarkedResponse.boundary_source_card m s
  have htarget : Nat.card (Marked m → AES.Word) =
      (2^32 : ℕ) ^ Fintype.card (Marked m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, AES.word_card]
  apply AddMonoidHom.surjective_of_card_ker_le_div
  rw [markedHom_kernel_card, hsource, htarget]
  apply (Nat.le_div_iff_mul_le
    (by positivity : 0 < (2^32 : ℕ) ^ Fintype.card (Marked m))).mpr
  have he :
      (4 - (maskSize (outputZeros m s) + maskSize (inputZeros m s) +
        Fintype.card (Marked m))) + Fintype.card (Marked m) =
      4 - (maskSize (outputZeros m s) + maskSize (inputZeros m s)) := by omega
  simpa only [← pow_add, he] using
    (le_rfl : (2^32 : ℕ) ^ (4 - (maskSize (outputZeros m s) + maskSize (inputZeros m s))) ≤
      (2^32 : ℕ) ^ (4 - (maskSize (outputZeros m s) + maskSize (inputZeros m s))))

/-- Every actual marked fiber has exactly the computed kernel size. -/
theorem markedHom_fiber_card (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m) ≤ 4) (v : Marked m → AES.Word) :
    Fintype.card {c : graphSubgroup (outputZeros m s) (inputZeros m s) //
      markedHom m s c = v} =
      (2^32 : ℕ) ^ (4 - (maskSize (outputZeros m s) + maskSize (inputZeros m s) +
        Fintype.card (Marked m))) := by
  rw [ActualMarkedUniform.fiber_card_eq_kernel (markedHom m s)
    (markedHom_surjective m s hlow) v]
  simpa only [Nat.card_eq_fintype_card] using markedHom_kernel_card m s

/-- Fiber identity on the original shortened-source subtype. Its equivalence
with the additive subgroup preserves the actual underlying source word. -/
theorem sourceCoordinates_fiber_card (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m) ≤ 4) (v : Marked m → AES.Word) :
    Fintype.card {c : Source m s //
      sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c = v} =
      (2^32 : ℕ) ^ (4 - (maskSize (outputZeros m s) + maskSize (inputZeros m s) +
        Fintype.card (Marked m))) := by
  let e : {c : Source m s //
        sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c = v} ≃
      {c : graphSubgroup (outputZeros m s) (inputZeros m s) // markedHom m s c = v} :=
    { toFun := fun c => ⟨sourceSubtypeEquiv m s c.val, c.property⟩
      invFun := fun c => ⟨(sourceSubtypeEquiv m s).symm c.val, c.property⟩
      left_inv := fun c => by
        apply Subtype.ext
        exact (sourceSubtypeEquiv m s).left_inv c.val
      right_inv := fun c => by
        apply Subtype.ext
        exact (sourceSubtypeEquiv m s).right_inv c.val }
  rw [Fintype.card_congr e]
  exact markedHom_fiber_card m s hlow v

/-- Exact counting-measure pushforward of arbitrary signed functions under
the actual marked projection, with the common source preserved. -/
theorem sourceCoordinates_sum_uniform (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m) ≤ 4) (F : (Marked m → AES.Word) → ℝ) :
    (∑ c : Source m s,
      F (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c)) =
      (Fintype.card (markedHom m s).ker : ℝ) * ∑ v : Marked m → AES.Word, F v := by
  have he := (sourceSubtypeEquiv m s).sum_comp
    (fun c : graphSubgroup (outputZeros m s) (inputZeros m s) => F (markedHom m s c))
  have hcoord (c : Source m s) :
      markedHom m s (sourceSubtypeEquiv m s c) =
        sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c := rfl
  calc
    _ = ∑ c : graphSubgroup (outputZeros m s) (inputZeros m s), F (markedHom m s c) := by
      simpa only [hcoord] using he
    _ = _ := ActualMarkedUniform.sum_comp_uniform (markedHom m s)
      (markedHom_surjective m s hlow) F

/-- The equal-fiber source-size factor used to turn counting pushforward into
the exact uniform probability law. -/
theorem source_card_factorization (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m) ≤ 4) :
    (Fintype.card (Source m s) : ℝ) =
      (Fintype.card (markedHom m s).ker : ℝ) * Fintype.card (Marked m → AES.Word) := by
  have h := sourceCoordinates_sum_uniform m s hlow (fun _ => (1 : ℝ))
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using h

/-- Exact normalized uniform pushforward for every signed test function. -/
theorem sourceCoordinates_average_uniform (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m) ≤ 4) (F : (Marked m → AES.Word) → ℝ) :
    (∑ c : Source m s,
      F (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c)) /
        Fintype.card (Source m s) =
      (∑ v : Marked m → AES.Word, F v) / Fintype.card (Marked m → AES.Word) := by
  have hk : (Fintype.card (markedHom m s).ker : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (markedHom m s).ker ≠ 0)
  rw [sourceCoordinates_sum_uniform m s hlow F, source_card_factorization m s hlow]
  exact mul_div_mul_left _ _ hk

/-- One explicitly retained marked leg with zero row sums cancels the exact
raw response under the proved uniform marked image. -/
theorem rawResponse_zero_of_uniform_image (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m) ≤ 4)
    (T : Marked m → AES.Word → AES.Word → ℝ) (k : Marked m)
    (hT : ∀ y, (∑ v : AES.Word, T k y v) = 0) (y : Marked m → AES.Word) :
    rawResponse GroupedRecurrence.boundary.toAddMonoidHom m s T y = 0 := by
  have hs := sourceCoordinates_sum_uniform m s hlow
    (fun v : Marked m → AES.Word => ∏ p : Marked m, T p (y p) (v p))
  change (∑ c : Source m s,
    ∏ p : Marked m,
      T p (y p) (sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s c p)) = 0
  rw [hs, ← Fintype.prod_sum]
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (hT (y k)), mul_zero]

/-- Output orientation: sum over the ordinary word residual's source index. -/
theorem wordResidual_row_sum (y : AES.Word) :
    (∑ v : AES.Word, residualMatrix AES.wordSuperboxKernel 0 y v) = 0 := by
  unfold residualMatrix
  rw [Finset.sum_sub_distrib, AES.word_superbox_pointed.row_sum,
    (activityMatrix_pointed (0 : AES.Word) AES.word_card_gt_one).row_sum]
  norm_num

/-- Input orientation: the source index is the ordinary residual's output
index, so the transposed leg requires the ordinary column sum. -/
theorem wordResidual_column_sum (y : AES.Word) :
    (∑ v : AES.Word, residualMatrix AES.wordSuperboxKernel 0 v y) = 0 := by
  unfold residualMatrix
  rw [Finset.sum_sub_distrib, AES.word_superbox_pointed.column_sum,
    (activityMatrix_pointed (0 : AES.Word) AES.word_card_gt_one).column_sum]
  norm_num

/-- Actual residual-leg cancellation includes the physically transposed
input kernel R(x,y), as fixed in WordGraphKernel. -/
theorem wordMarkedLeg_row_sum (m : GraphPosition → Bool) (p : Marked m) (y : AES.Word) :
    (∑ v : AES.Word, wordMarkedLeg m p y v) = 0 := by
  rcases p with ⟨p, hp⟩
  cases p with
  | inl i =>
      change (∑ v : AES.Word, residualMatrix AES.wordSuperboxKernel 0 y v) = 0
      exact wordResidual_row_sum y
  | inr i =>
      change (∑ v : AES.Word, residualMatrix AES.wordSuperboxKernel 0 v y) = 0
      exact wordResidual_column_sum y

/-- The actual activity contraction vanishes at the uniform-image endpoint.
The marking witness prevents applying a zero-product argument to an empty
marked family. This is a per-choice identity, not a full operator bound. -/
theorem boundaryContractedResponse_zero_of_uniform_image
    (m : GraphPosition → Bool) (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) +
      Fintype.card (Marked m) ≤ 4) (y : Marked m → AES.Word) :
    boundaryContractedResponse m s y = 0 := by
  obtain ⟨p, hp⟩ := hm
  rw [WordMarkedResponse.boundaryContractedResponse_shortened]
  rw [rawResponse_zero_of_uniform_image m s hlow (wordMarkedLeg m)
    (⟨p, hp⟩ : Marked m) (wordMarkedLeg_row_sum m ⟨p, hp⟩) y, zero_div]

end AESPaper.WordMarkedUniform
