import AESConcrete.MarkedBlockShortening
import AESConcrete.WordColumnBounds

/-!
# Zero-dimensional and full-coordinate response endpoints

Four prescribed physical graph zeros leave only the zero graph point, so
any nonempty residual marking kills the contraction. A separate generic
full-coordinate reindexing lemma records the uniform-product cancellation.
No code energy bound is assumed. Constructive mathematics only; no attacks
or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MarkedBlockVanishing
open AESMixing AESMixing.AES
open AESConcrete.MarkedBlockVectorization AESConcrete.MarkedBlockShortening
open AESConcrete.ShortenedLineResponse
open AESConcrete.ByteOrientations (Orientation channel channel_resources)

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem rawResponse_zero_of_high_zeros
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hm : ∃ p, m p = true)
    (hz : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s))
    (T : Marked m → V → V → ℝ) (hT : ∀ p y, T p y 0 = 0)
    (y : Marked m → V) : rawResponse L m s T y = 0 := by
  obtain ⟨p,hp⟩ := hm
  unfold rawResponse
  apply Finset.sum_eq_zero
  intro c _
  have hc : c.val = 0 :=
    mds_graph_zero_high L hL (outputZeros m s) (inputZeros m s) hz c.val c.property
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨p,hp⟩ : Marked m))
  change T ⟨p,hp⟩ (y ⟨p,hp⟩) (graphCoordinate L c.val p) = 0
  rw [hc]
  have h0 : graphCoordinate L 0 p = 0 := by cases p <;> simp [graphCoordinate]
  rw [h0]
  exact hT _ _

theorem contractedResponse_zero_of_high_zeros (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (hm : ∃ p, m p = true)
    (hz : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s))
    (T : Marked m → V → V → ℝ) (hT : ∀ p y, T p y 0 = 0)
    (y : Marked m → V) : contractedResponse m T (graphCoordinate L) s y = 0 := by
  rw [contractedResponse_shortened hV,
    rawResponse_zero_of_high_zeros L hL m s hm hz T hT, zero_div]

end Generic

/-- Exact uniform endpoint for any actual coordinate equivalence. The
dependence on the original source is removed by that equivalence, not by
an independence assertion. -/
theorem response_zero_of_bijective_coordinates
    {C K V : Type*} [Fintype C] [Fintype K] [DecidableEq K] [Fintype V]
    (coord : C → K → V) (hc : Function.Bijective coord)
    (T : K → V → V → ℝ) (k : K) (hT : ∀ y, (∑ v : V, T k y v) = 0)
    (y : K → V) : (∑ c : C, ∏ i : K, T i (y i) (coord c i)) = 0 := by
  let e := Equiv.ofBijective coord hc
  calc
    _ = ∑ v : K → V, ∏ i : K, T i (y i) (v i) :=
      e.sum_comp (fun v => ∏ i : K, T i (y i) (v i))
    _ = ∏ i : K, ∑ v : V, T i (y i) v := (Fintype.prod_sum _).symm
    _ = 0 := Finset.prod_eq_zero (Finset.mem_univ k) (hT (y k))

theorem actual_markedLeg_zero_column (left right : Orientation)
    (m : GraphPosition → Bool) (p : Marked m) (y : BinaryWord 8) :
    markedLeg (channel left) (channel right) m p y 0 = 0 := by
  rcases p with ⟨p,hp⟩
  cases p with
  | inl i => exact AESConcrete.pointed_residual_zero_column (channel_resources left).pointed y
  | inr i => exact AESConcrete.pointed_residual_zero_row (channel_resources right).pointed y

/-- Both actual diffusion directions and independently chosen byte orientations. -/
theorem actual_contractedResponse_zero_of_high_zeros
    (left right : Orientation) (inverse : Bool) (m : GraphPosition → Bool)
    (s : Activity m → Bool) (hm : ∃ p, m p = true)
    (hz : 4 ≤ maskSize (outputZeros m s) + maskSize (inputZeros m s))
    (y : Marked m → BinaryWord 8) :
    contractedResponse m (markedLeg (channel left) (channel right) m)
      (graphCoordinate (byteDiffusionHom inverse)) s y = 0 :=
  contractedResponse_zero_of_high_zeros (by norm_num [BinaryWord.card])
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) m s hm hz _
    (actual_markedLeg_zero_column left right m) y

end AESConcrete.MarkedBlockVanishing
