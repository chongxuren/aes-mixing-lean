import AESConcrete.ActivityGraphContraction
import AESConcrete.ShortenedLineGeometry
import AESMixing.MarkedPrescriptions

/-!
# High-activity contractions vanish by exact MDS fibers

At activity weight at least four, at most one graph zero is prescribed.
The three marked physical output coordinates then have a uniform full
projection.  Its fibers have size |V| when no zero is imposed and size one
when one zero is imposed.  Keeping that multiplicity explicitly, the
shortened response factors into the three leg row sums and vanishes.

This concerns the checked graph-response kernel and ordinary actual residual
legs.  Full centered-word identification and operator assembly remain separate.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActivityHighWeightVanishing
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ActivityFrameContraction
open AESConcrete.ActivityGraphContraction
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedLineGeometry (markedPositions)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.ByteLineBounds (leg)

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The output-only fiber is the existing arbitrary-prescription fiber with
an empty marked-input mask.  This theorem preserves its full multiplicity. -/
theorem shortened_output_fiber_uniform
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out : Fin 16) (hr : MaskDisjoint r out)
    (hle : maskSize r + maskSize z + maskSize out ≤ 4)
    (v : MaskCoordinates out → V) :
    Fintype.card {x : ShortenedGraph L r z // shortenedOutput L r z out x = v} =
      Fintype.card V ^ (4 - (maskSize r + maskSize z + maskSize out)) := by
  classical
  have he (x : ShortenedGraph L r z) : shortenedOutput L r z out x = v ↔
      shortenedProjection L r z out 0 x = (v, fun _ => (0 : V)) := by
    constructor
    · intro h
      exact Prod.ext h (funext (fun i => (empty_mask_coordinate i).elim))
    · intro h
      exact congrArg Prod.fst h
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  have h := shortened_projection_fiber_uniform L hL r z out 0 hr (mask_disjoint_empty z)
    (by simpa only [show maskSize (0 : Fin 16) = 0 by decide, Nat.add_zero] using hle)
    v (fun _ => (0 : V))
  simpa only [show maskSize (0 : Fin 16) = 0 by decide, Nat.add_zero] using h

private def coordinateValuesEquiv {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out) :
    (MaskCoordinates out → V) ≃ (Fin 3 → V) where
  toFun f := fun i => f (e i)
  invFun f := fun i => f (e.symm i)
  left_inv f := by
    funext i
    exact congrArg f (e.apply_symm_apply i)
  right_inv f := by
    funext i
    exact congrArg f (e.symm_apply_apply i)

/-- With zero or one constraint outside the physical output triple, every
marked triple occurs exactly |V|^(1-k) times.  No graph-to-triple bijection
is asserted at k=0, where the multiplicity is |V| rather than one. -/
theorem shortened_response_low_zeros_factorization
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (hr : MaskDisjoint r out)
    (hlow : maskSize r + maskSize z ≤ 1)
    (T : Fin 3 → V → V → ℝ) (y : Fin 3 → V) :
    shortenedResponse L r z (markedPositions e) T y =
      (Fintype.card V : ℝ) ^ (1 - (maskSize r + maskSize z)) *
        ∏ i : Fin 3, ∑ v : V, T i (y i) v := by
  classical
  let g : (MaskCoordinates out → V) → ℝ :=
    fun u => ∏ i : Fin 3, T i (y i) (u (e i))
  have hpow : 4 - (maskSize r + maskSize z + maskSize out) =
      1 - (maskSize r + maskSize z) := by omega
  have hc (u : MaskCoordinates out → V) :
      Fintype.card {x : ShortenedGraph L r z // shortenedOutput L r z out x = u} =
        Fintype.card V ^ (1 - (maskSize r + maskSize z)) := by
    simpa only [hpow] using shortened_output_fiber_uniform L hL r z out hr (by omega) u
  change (∑ x : ShortenedGraph L r z, g (shortenedOutput L r z out x)) = _
  rw [← Fintype.sum_fiberwise' (shortenedOutput L r z out) g]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [hc]
  rw [← Finset.mul_sum, Nat.cast_pow]
  congr 1
  calc
    (∑ u : MaskCoordinates out → V, g u) =
        ∑ v : Fin 3 → V, ∏ i : Fin 3, T i (y i) (v i) := by
      have hs := Equiv.sum_comp (coordinateValuesEquiv (V := V) e).symm g
      simpa [g, coordinateValuesEquiv] using hs.symm
    _ = ∏ i : Fin 3, ∑ v : V, T i (y i) v :=
      (Fintype.prod_sum (fun i v => T i (y i) v)).symm

/-- Generic row-sum cancellation after the exact fiber calculation. -/
theorem shortened_response_low_zeros_zero
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (hr : MaskDisjoint r out)
    (hlow : maskSize r + maskSize z ≤ 1)
    (T : Fin 3 → V → V → ℝ)
    (hrow : ∀ i y, (∑ v : V, T i y v) = 0) (y : Fin 3 → V) :
    shortenedResponse L r z (markedPositions e) T y = 0 := by
  rw [shortened_response_low_zeros_factorization L hL r z out hout e hr hlow T y]
  have hp : (∏ i : Fin 3, ∑ v : V, T i (y i) v) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3))
    exact hrow 0 (y 0)
  rw [hp, mul_zero]

/-- Activity weights four and five give at most one zero constraint by
the existing balance identity, so the physical marked-output response dies. -/
theorem high_weight_contraction_zero (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (out : Fin 16) (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (a : Fin 16) (r : Fin 4) (b : Bool)
    (hdisj : MaskDisjoint (outputZeroMask r b) out)
    (hweight : 4 ≤ maskSize a + (if b then 1 else 0))
    (T : Fin 3 → V → V → ℝ)
    (hrow : ∀ i y, (∑ v : V, T i y v) = 0) (y : Fin 3 → V) :
    contraction (graphResponse L a r (markedPositions e) T y) b = 0 := by
  rw [graphResponse_contraction hV,
    shortened_response_low_zeros_zero L hL _ _ out hout e hdisj
      (by have hc := constraint_balance a r b; omega) T hrow y, zero_div]

end Generic

/-- Actual forward/inverse AES diffusion, any fixed actual orientation on
each ordinary residual leg, and the physical marked output triple.  The
disjointness premise is supplied by the complementary activity output. -/
theorem actual_high_weight_contraction_zero (inverse : Bool)
    (out : Fin 16) (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (a : Fin 16) (r : Fin 4) (b : Bool)
    (hdisj : MaskDisjoint (outputZeroMask r b) out)
    (hweight : 4 ≤ maskSize a + (if b then 1 else 0))
    (o : Fin 3 → Orientation) (y : Fin 3 → Byte) :
    contraction (graphResponse (byteDiffusionHom inverse) a r (markedPositions e)
      (fun i => leg (o i) false) y) b = 0 := by
  apply high_weight_contraction_zero (by norm_num [BinaryWord.card])
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    out hout e a r b hdisj hweight (fun i => leg (o i) false) _ y
  intro i v
  exact ByteGramDiagonal.residual_row_sum (channel_resources (o i)) v

end AESConcrete.ActivityHighWeightVanishing
