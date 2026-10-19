import AESConcrete.MarkedBlockShortening
import AESConcrete.ShortenedPlane

/-!
# Actual physical information sets for marked shortened AES codes

An injected set of unconstrained physical graph positions determines a
shortened source as soon as the selected coordinates and prescribed zeros
total four. The actual MDS zero theorem proves injection and its exact
graph count proves surjection. These are the physical information sets
required by the mixed per-leg moment bound, not assumed independent laws.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualMarkedCodeMoment
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (remaining byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.MarkedBlockVectorization (Marked Activity markedLeg residualLeg)
open AESConcrete.MarkedBlockShortening
  (sourceCoordinates outputZeros inputZeros outputZeros_bit inputZeros_bit)
open AESConcrete.ByteOrientations (Orientation channel)
attribute [local instance] Classical.propDecidable

abbrev Byte := BinaryWord 8

section PhysicalProjection
variable {I V : Type*} [Fintype I] [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Distinct unconstrained physical positions give an injective information set. -/
theorem selected_projection_injective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (p : I → GraphPosition) (hp : Function.Injective p)
    (hfree : ∀ i, remaining r z (p i))
    (hsize : 4 ≤ maskSize r + maskSize z + Fintype.card I) :
    Function.Injective (fun c : ShortenedGraph L r z => fun i : I => graphCoordinate L c.val (p i)) := by
  let t : Finset GraphPosition := Finset.univ.image p
  have hcount : maskSize (outputPositionMask t) + maskSize (inputPositionMask t) = Fintype.card I := by
    calc
      _ = t.card := selected_position_count t
      _ = _ := by
        dsimp only [t]
        rw [Finset.card_image_of_injective _ hp, Finset.card_univ]
  have hr : MaskDisjoint r (outputPositionMask t) := by
    intro j hj ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((outputPositionMask_bit t j).mp ht)
    have hf : maskBit r j ≠ true := by
      simpa only [hi, remaining, Sum.elim_inl] using hfree i
    exact hf hj
  have hz : MaskDisjoint z (inputPositionMask t) := by
    intro j hj ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((inputPositionMask_bit t j).mp ht)
    have hf : maskBit z j ≠ true := by
      simpa only [hi, remaining, Sum.elim_inr] using hfree i
    exact hf hj
  intro c d he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply mds_graph_zero_high L hL (maskUnion r (outputPositionMask t))
    (maskUnion z (inputPositionMask t))
  · rw [maskUnion_size r _ hr, maskUnion_size z _ hz]
    omega
  · constructor
    · intro j hj
      rw [map_sub]
      change L c.val j - L d.val j = 0
      apply sub_eq_zero.mpr
      rw [maskUnion_bit, Bool.or_eq_true] at hj
      rcases hj with hj | hj
      · rw [c.property.1 j hj, d.property.1 j hj]
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((outputPositionMask_bit t j).mp hj)
        simpa only [hi, graphCoordinate, Sum.elim_inl] using congrFun he i
    · intro j hj
      change c.val j - d.val j = 0
      apply sub_eq_zero.mpr
      rw [maskUnion_bit, Bool.or_eq_true] at hj
      rcases hj with hj | hj
      · rw [c.property.2 j hj, d.property.2 j hj]
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ((inputPositionMask_bit t j).mp hj)
        simpa only [hi, graphCoordinate, Sum.elim_inr] using congrFun he i

/-- The exact source cardinality supplies surjectivity, with physical maps fixed. -/
theorem selected_projection_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (p : I → GraphPosition) (hp : Function.Injective p)
    (hfree : ∀ i, remaining r z (p i))
    (hsize : maskSize r + maskSize z + Fintype.card I = 4) :
    Function.Bijective (fun c : ShortenedGraph L r z => fun i : I => graphCoordinate L c.val (p i)) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · exact selected_projection_injective L hL r z p hp hfree (by omega)
  · change Fintype.card {x : Fin 4 → V // graphZeroConditions L r z x} = _
    rw [mds_graph_zero_count L hL, Fintype.card_fun]
    congr 1
    omega

/-- A marked coordinate is outside every zero frame condition. -/
theorem marked_remaining (m : GraphPosition → Bool) (s : Activity m → Bool) (p : Marked m) :
    remaining (outputZeros m s) (inputZeros m s) p.val := by
  cases hpos : p.val with
  | inl i =>
    change maskBit (outputZeros m s) i ≠ true
    intro hzero
    obtain ⟨hn, _⟩ := (outputZeros_bit m s i).mp hzero
    have hm : m (Sum.inl i) = true := by simpa only [hpos] using p.property
    exact hn hm
  | inr i =>
    change maskBit (inputZeros m s) i ≠ true
    intro hzero
    obtain ⟨hn, _⟩ := (inputZeros_bit m s i).mp hzero
    have hm : m (Sum.inr i) = true := by simpa only [hpos] using p.property
    exact hn hm

theorem marked_projection_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (m : GraphPosition → Bool) (s : Activity m → Bool) (p : I → Marked m)
    (hp : Function.Injective p)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card I = 4) :
    Function.Bijective (fun c : ShortenedGraph L (outputZeros m s) (inputZeros m s) =>
      fun i : I => sourceCoordinates L m s c (p i)) := by
  apply selected_projection_bijective L hL (outputZeros m s) (inputZeros m s)
    (fun i => (p i).val) _ (fun i => marked_remaining m s (p i)) hsize
  intro i j h
  exact hp (Subtype.ext h)

end PhysicalProjection

section ActualLow
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def markedOrientation (left right : Orientation) (m : GraphPosition → Bool)
    (p : Marked m) : Orientation :=
  Sum.elim (fun _ => left) (fun _ => MixedCodeMoment.adjointOrientation right) p.val

theorem actual_markedLeg (left right : Orientation) (m : GraphPosition → Bool) :
    markedLeg (channel left) (channel right) m =
      fun p => residualMatrix (channel (markedOrientation left right m p)) 0 := by
  funext p y x
  rcases p with ⟨p,hp⟩
  cases p with
  | inl i => rfl
  | inr i =>
    exact congrFun (congrFun (MixedCodeMoment.actual_residual_adjoint right) y) x

/-- Actual low-dimensional marked-code bound; no information-set premise remains. -/
theorem actual_normalized_low_energy_le (left right : Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (idx : CodePosition I J ≃ Marked m)
    (hsize : maskSize (outputZeros m s) + maskSize (inputZeros m s) + Fintype.card I = 4) :
    (∑ y : Marked m → Byte,
      MixedCodeMoment.normalizedResponse (markedLeg (channel left) (channel right) m)
        (sourceCoordinates (byteDiffusionHom inverse) m s) y^2) ≤
      (MixedCodeMoment.byteMoment / 256)^Fintype.card I * MixedCodeMoment.byteDelta^Fintype.card J := by
  rw [actual_markedLeg]
  apply MixedCodeMoment.actual_normalizedResponse_energy_le
    (markedOrientation left right m) (sourceCoordinates (byteDiffusionHom inverse) m s) idx
  · apply marked_projection_bijective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      m s (fun i : I => idx (Sum.inl i)) _ hsize
    intro i j h
    exact Sum.inl.inj (idx.injective h)
  · apply marked_projection_bijective (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      m s (fun i : I => idx (Sum.inr (Sum.inl i))) _ hsize
    intro i j h
    exact Sum.inl.inj (Sum.inr.inj (idx.injective h))

end ActualLow
end AESConcrete.ActualMarkedCodeMoment
