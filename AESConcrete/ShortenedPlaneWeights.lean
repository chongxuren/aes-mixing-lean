import AESConcrete.ShortenedMixedGeometry
import AESConcrete.ActivityHighWeightVanishing
import AESConcrete.PlaneWeightEnumerator

/-!
# Actual plane zero fibers and exact spike enumerator

The raw two-zero shortened AES graph has 65536 points. A single additional
marked zero leaves exactly 256 points, and two distinct marked zeros force
the zero graph. These geometric facts instantiate the generic enumerator;
no empirical point enumeration or extra plane hypothesis is used.
Constructive scope only; full word-operator identification remains separate.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ShortenedPlaneWeights
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions)
open AESConcrete.ShortenedMixedGeometry (markedGraph_zero)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 65536

theorem raw_plane_card (inverse : Bool) {out : Fin 16} (p : ShorteningChoice out 2) :
    Fintype.card (ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2) = 65536 := by
  rw [plane_choice_cardinality (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) out p]
  norm_num [BinaryWord.card]

theorem marked_zero_fiber_card (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) (i : Fin 3) :
    Fintype.card {x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 //
      markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e) x i = 0} = 256 := by
  have hdisj : MaskDisjoint p.val.1 (singletonMask (e i).val) := by
    intro k hk hs
    have he : k = (e i).val := (singletonMask_bit _ _).mp hs
    subst k
    exact p.property.1 _ hk (e i).property
  have hsize : maskSize p.val.1 + maskSize p.val.2 + maskSize (singletonMask (e i).val) = 3 := by
    rw [p.property.2, singletonMask_size]
  have he (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2) :
      markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e) x i = 0 ↔
      shortenedOutput (byteDiffusionHom inverse) p.val.1 p.val.2 (singletonMask (e i).val) x = 0 := by
    constructor
    · intro hx
      funext k
      have hk : k.val = (e i).val := (singletonMask_bit _ _).mp k.property
      change byteDiffusionHom inverse x.val k.val = 0
      change byteDiffusionHom inverse x.val (e i).val = 0 at hx
      simpa only [hk] using hx
    · intro hx
      have hk : maskBit (singletonMask (e i).val) (e i).val = true :=
        (singletonMask_bit _ _).mpr rfl
      exact congrFun hx ⟨(e i).val, hk⟩
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  have hf := ActivityHighWeightVanishing.shortened_output_fiber_uniform
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    p.val.1 p.val.2 (singletonMask (e i).val) hdisj (by omega) 0
  norm_num only [hsize, BinaryWord.card, Nat.reduceSub, pow_one, Nat.reducePow] at hf
  exact hf

private theorem three_index_cover : ∀ i j : Fin 3, i ≠ j →
    ∃ k : Fin 3, ∀ u : Fin 3, u ≠ k → u = i ∨ u = j := by decide

theorem two_marked_zeros_force_zero (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2)
    (x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2)
    (i j : Fin 3) (hij : i ≠ j)
    (hi : markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e) x i = 0)
    (hj : markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e) x j = 0) :
    x = zeroGraph (byteDiffusionHom inverse) p.val.1 p.val.2 := by
  obtain ⟨k, hk⟩ := three_index_cover i j hij
  apply (ShortenedPlane.graph_pair_restriction_bijective inverse out hout e p k).1
  funext u
  change byteDiffusionHom inverse x.val (e u.val).val =
    byteDiffusionHom inverse (0 : Fin 4 → Byte) (e u.val).val
  have hval : byteDiffusionHom inverse x.val (e u.val).val = 0 := by
    change byteDiffusionHom inverse x.val (e i).val = 0 at hi
    change byteDiffusionHom inverse x.val (e j).val = 0 at hj
    rcases hk u.val u.property with hu | hu
    · simpa only [hu] using hi
    · simpa only [hu] using hj
  exact hval.trans (congrFun (map_zero (byteDiffusionHom inverse)) (e u.val).val).symm

theorem actual_plane_nonzero_spike_sum (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 2) (d g : ℝ) :
    (∑ x : {x : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 //
        x ≠ zeroGraph (byteDiffusionHom inverse) p.val.1 p.val.2},
      PlaneWeightEnumerator.spikeProduct d g
        (markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e)) x.val) =
      3*255*d*g^2 + 255*254*g^3 := by
  classical
  convert PlaneWeightEnumerator.plane_nonzero_spike_sum d g
    (markedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 (markedPositions e))
    (zeroGraph (byteDiffusionHom inverse) p.val.1 p.val.2)
    (markedGraph_zero _ _ _ _) (raw_plane_card inverse p)
    (marked_zero_fiber_card inverse e p) (two_marked_zeros_force_zero inverse out hout e p) using 1
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

end AESConcrete.ShortenedPlaneWeights
