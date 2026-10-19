import AESConcrete.ActualMarkedCodeDual
import Mathlib.GroupTheory.Index

/-!
# Uniform marked-coordinate endpoint of the actual shortened graph

The kernel of the actual marked projection is a further shortened graph.
Exact MDS counts imply surjectivity when marked coordinates fit within the
remaining dimension. Equal additive-map fibers then give an exact uniform
pushforward. A nonempty residual marking cancels its tensor response.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualMarkedUniform
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.MarkedBlockVectorization (Marked Activity markedLeg contractedResponse)
open AESConcrete.MarkedBlockShortening (sourceCoordinates outputZeros inputZeros rawResponse)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.ActualMarkedCodeMoment (Byte marked_remaining markedOrientation actual_markedLeg)
open AESConcrete.ActualMarkedCodeDual (markedHom)
attribute [local instance] Classical.propDecidable

-- Actual byte/source coercions require deeper reduction in the source
-- cardinality and finite-fiber normalization bridges.
set_option maxRecDepth 100000

/-- Identity on actual source words, with subtype finite enumerations kept separate. -/
def sourceSubtypeEquiv (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool) :
    ShortenedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s) ≃
      ShortenedPlane.graphSubgroup inverse (outputZeros m s) (inputZeros m s) where
  toFun c := ⟨c.val,c.property⟩
  invFun c := ⟨c.val,c.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def markedPositions (m : GraphPosition → Bool) : Finset GraphPosition :=
  Finset.univ.filter (fun p => m p = true)

def enlargedOutputZeros (m : GraphPosition → Bool) (s : Activity m → Bool) : Fin 16 :=
  maskUnion (outputZeros m s) (outputPositionMask (markedPositions m))

def enlargedInputZeros (m : GraphPosition → Bool) (s : Activity m → Bool) : Fin 16 :=
  maskUnion (inputZeros m s) (inputPositionMask (markedPositions m))

theorem enlarged_zero_count (m : GraphPosition → Bool) (s : Activity m → Bool) :
    maskSize (enlargedOutputZeros m s) + maskSize (enlargedInputZeros m s) =
      maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m) := by
  have hr : MaskDisjoint (outputZeros m s) (outputPositionMask (markedPositions m)) := by
    intro i hi hm
    have hp : m (Sum.inl i) = true :=
      (Finset.mem_filter.mp ((outputPositionMask_bit (markedPositions m) i).mp hm)).2
    have hf := marked_remaining m s (⟨Sum.inl i,hp⟩ : Marked m)
    exact hf hi
  have hz : MaskDisjoint (inputZeros m s) (inputPositionMask (markedPositions m)) := by
    intro i hi hm
    have hp : m (Sum.inr i) = true :=
      (Finset.mem_filter.mp ((inputPositionMask_bit (markedPositions m) i).mp hm)).2
    have hf := marked_remaining m s (⟨Sum.inr i,hp⟩ : Marked m)
    exact hf hi
  have hc : maskSize (outputPositionMask (markedPositions m)) +
      maskSize (inputPositionMask (markedPositions m)) = Fintype.card (Marked m) := by
    rw [selected_position_count]
    exact (Fintype.card_subtype (fun p : GraphPosition => m p = true)).symm
  rw [enlargedOutputZeros, enlargedInputZeros, maskUnion_size _ _ hr, maskUnion_size _ _ hz]
  omega

def kernelShorteningEquiv (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (markedHom inverse m s).ker ≃
      ShortenedGraph (byteDiffusionHom inverse) (enlargedOutputZeros m s) (enlargedInputZeros m s) where
  toFun c := by
    refine ⟨c.val.val, (graphZeroConditions_union_positions (byteDiffusionHom inverse)
      (outputZeros m s) (inputZeros m s) (markedPositions m) c.val.val).mpr ⟨c.val.property, ?_⟩⟩
    intro p hp
    have hm : m p = true := (Finset.mem_filter.mp hp).2
    have h := congrFun c.property (⟨p,hm⟩ : Marked m)
    exact h
  invFun c := by
    have hc := (graphZeroConditions_union_positions (byteDiffusionHom inverse)
      (outputZeros m s) (inputZeros m s) (markedPositions m) c.val).mp c.property
    refine ⟨⟨c.val,hc.1⟩, ?_⟩
    change markedHom inverse m s ⟨c.val,hc.1⟩ = 0
    funext p
    exact hc.2 p.val (by simp [markedPositions, p.property])
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv c := Subtype.ext rfl

theorem markedHom_kernel_card (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Nat.card (markedHom inverse m s).ker =
      256 ^ (4-(maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m))) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (kernelShorteningEquiv inverse m s),
    mds_graph_zero_count (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse),
    enlarged_zero_count]
  norm_num only [BinaryWord.card, Nat.reducePow]

/-- The actual map is onto all marked tuples, not merely a same-size abstract code. -/
theorem markedHom_surjective (inverse : Bool) (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m) ≤ 4) :
    Function.Surjective (markedHom inverse m s) := by
  have hsource : Nat.card (ShortenedPlane.graphSubgroup inverse (outputZeros m s) (inputZeros m s)) =
      256 ^ (4-(maskSize (outputZeros m s) + maskSize (inputZeros m s))) := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_congr (sourceSubtypeEquiv inverse m s)]
    rw [mds_graph_zero_count (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)]
    norm_num only [BinaryWord.card, Nat.reducePow]
  have htarget : Nat.card (Marked m → Byte) = 256 ^ Fintype.card (Marked m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun]
    norm_num only [BinaryWord.card, Nat.reducePow]
  apply AddMonoidHom.surjective_of_card_ker_le_div
  rw [markedHom_kernel_card, hsource, htarget]
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 256 ^ Fintype.card (Marked m))).mpr
  have he :
      (4-(maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m))) +
        Fintype.card (Marked m) = 4-(maskSize (outputZeros m s) + maskSize (inputZeros m s)) := by omega
  simpa only [← pow_add, he] using
    (le_rfl : 256 ^ (4-(maskSize (outputZeros m s) + maskSize (inputZeros m s))) ≤
      256 ^ (4-(maskSize (outputZeros m s) + maskSize (inputZeros m s))))

section Fibers
variable {X Y : Type*} [AddCommGroup X] [Fintype X] [AddCommGroup Y] [Fintype Y] [DecidableEq Y]

theorem fiber_card_eq_kernel (f : X →+ Y) (hf : Function.Surjective f) (y : Y) :
    Fintype.card {x : X // f x = y} = Fintype.card f.ker := by
  have hk : Fintype.card f.ker = Fintype.card {x : X // f x = 0} :=
    Fintype.card_congr (Equiv.subtypeEquivRight
      (fun x : X => show x ∈ f.ker ↔ f x = 0 from Iff.rfl))
  rw [hk]
  simp only [Fintype.card_subtype]
  exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) ⟨0,f.map_zero⟩

/-- Exact counting-measure pushforward along a surjective additive map. -/
theorem sum_comp_uniform (f : X →+ Y) (hf : Function.Surjective f) (F : Y → ℝ) :
    (∑ x : X, F (f x)) = (Fintype.card f.ker : ℝ) * ∑ y : Y, F y := by
  rw [← Fintype.sum_fiberwise' f F]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [fiber_card_eq_kernel f hf]
  exact (Finset.mul_sum _ _ _).symm

end Fibers

theorem rawResponse_zero_of_uniform_image (inverse : Bool) (m : GraphPosition → Bool)
    (s : Activity m → Bool)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m) ≤ 4)
    (T : Marked m → Byte → Byte → ℝ) (k : Marked m)
    (hT : ∀ y, (∑ v : Byte, T k y v) = 0) (y : Marked m → Byte) :
    rawResponse (byteDiffusionHom inverse) m s T y = 0 := by
  have hs := sum_comp_uniform (markedHom inverse m s) (markedHom_surjective inverse m s hlow)
    (fun v : Marked m → Byte => ∏ p : Marked m, T p (y p) (v p))
  have hr : rawResponse (byteDiffusionHom inverse) m s T y =
      ∑ c : ShortenedPlane.graphSubgroup inverse (outputZeros m s) (inputZeros m s),
        ∏ p : Marked m, T p (y p) (markedHom inverse m s c p) := by
    have he := (sourceSubtypeEquiv inverse m s).sum_comp
      (fun c : ShortenedPlane.graphSubgroup inverse (outputZeros m s) (inputZeros m s) =>
        ∏ p : Marked m, T p (y p) (markedHom inverse m s c p))
    have hcoord
        (c : ShortenedGraph (byteDiffusionHom inverse) (outputZeros m s) (inputZeros m s))
        (p : Marked m) :
        markedHom inverse m s (sourceSubtypeEquiv inverse m s c) p =
          sourceCoordinates (byteDiffusionHom inverse) m s c p := rfl
    simpa only [hcoord, rawResponse] using he
  rw [hr, hs, ← Fintype.prod_sum]
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (hT (y k)), mul_zero]

theorem actual_markedLeg_row_sum (left right : Orientation) (m : GraphPosition → Bool)
    (p : Marked m) (y : Byte) : (∑ v : Byte, markedLeg (channel left) (channel right) m p y v) = 0 := by
  rw [actual_markedLeg]
  exact ByteGramDiagonal.residual_row_sum (channel_resources (markedOrientation left right m p)) y

/-- The d>=ell endpoint vanishes for every actual nonempty residual marking. -/
theorem actual_contractedResponse_zero_of_uniform_image (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hlow : maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card (Marked m) ≤ 4)
    (y : Marked m → Byte) :
    contractedResponse m (markedLeg (channel left) (channel right) m)
      (graphCoordinate (byteDiffusionHom inverse)) s y = 0 := by
  obtain ⟨p,hp⟩ := hm
  rw [MarkedBlockShortening.actual_contractedResponse_shortened]
  rw [rawResponse_zero_of_uniform_image inverse m s hlow _ (⟨p,hp⟩ : Marked m)
    (actual_markedLeg_row_sum left right m ⟨p,hp⟩) y, zero_div]

end AESConcrete.ActualMarkedUniform
