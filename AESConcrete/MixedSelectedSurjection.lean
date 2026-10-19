import AESConcrete.MixedMarkedCoordinates
import AESConcrete.ShortenedPlaneGeometry

/-!
# Surjectivity of an arbitrary physical selected projection

Up to four compatible prescribed physical graph coordinates are realized
by the actual additive MDS graph. Selected inputs and outputs retain their
tags. This extends the exact information-set bijection to smaller selected
sets using the proved MDS prescribed-count existence theorem, with no
independent-coordinate distribution assumption. Constructive mathematics
only; no attacks or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MixedSelectedSurjection
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse

attribute [local instance] Classical.propDecidable

section Generic
variable {I V : Type*} [Fintype I] [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem selected_projection_surjective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (selected : I → GraphPosition) (hselected : Function.Injective selected)
    (hfree : ∀ i, remaining r z (selected i))
    (hsize : maskSize r + maskSize z + Fintype.card I ≤ 4) :
    Function.Surjective (fun c : ShortenedGraph L r z => fun i : I => graphCoordinate L c.val (selected i)) := by
  intro y
  let t : Finset GraphPosition := Finset.univ.image selected
  have hcount : maskSize (outputPositionMask t) + maskSize (inputPositionMask t) = Fintype.card I := by
    calc
      _ = t.card := selected_position_count t
      _ = _ := by
        dsimp only [t]
        rw [Finset.card_image_of_injective _ hselected, Finset.card_univ]
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
  let values (p : GraphPosition) : V :=
    if h : ∃ i, selected i = p then y h.choose else 0
  have hvalues (i : I) : values (selected i) = y i := by
    have hex : ∃ j, selected j = selected i := ⟨i,rfl⟩
    have hj : hex.choose = i := hselected hex.choose_spec
    simp only [values, dif_pos hex, hj]
  let u (i : Fin 4) : V := if maskBit r i = true then 0 else values (Sum.inl i)
  let v (i : Fin 4) : V := if maskBit z i = true then 0 else values (Sum.inr i)
  have hle : maskSize (maskUnion r (outputPositionMask t)) +
      maskSize (maskUnion z (inputPositionMask t)) ≤ 4 := by
    rw [maskUnion_size _ _ hr, maskUnion_size _ _ hz]
    omega
  obtain ⟨x, hx⟩ := ShortenedPlaneGeometry.prescribed_exists L hL
    (maskUnion r (outputPositionMask t)) (maskUnion z (inputPositionMask t)) hle u v
  have hzeros : graphZeroConditions L r z x := by
    constructor
    · intro j hj
      have hh := hx.1 j (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl hj)
      simpa only [u, if_pos hj] using hh
    · intro j hj
      have hh := hx.2 j (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl hj)
      simpa only [v, if_pos hj] using hh
  refine ⟨⟨x,hzeros⟩, ?_⟩
  funext i
  cases hpos : selected i with
  | inl j =>
    have ht : maskBit (outputPositionMask t) j = true := by
      apply (outputPositionMask_bit t j).mpr
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hpos⟩
    have hf : maskBit r j ≠ true := by
      simpa only [hpos, remaining, Sum.elim_inl] using hfree i
    have hh := hx.1 j (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inr ht)
    change graphCoordinate L x (selected i) = y i
    rw [hpos]
    change L x j = y i
    change L x j = if maskBit r j = true then 0 else values (Sum.inl j) at hh
    rw [if_neg hf] at hh
    exact hh.trans (by rw [← hpos]; exact hvalues i)
  | inr j =>
    have ht : maskBit (inputPositionMask t) j = true := by
      apply (inputPositionMask_bit t j).mpr
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hpos⟩
    have hf : maskBit z j ≠ true := by
      simpa only [hpos, remaining, Sum.elim_inr] using hfree i
    have hh := hx.2 j (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inr ht)
    change graphCoordinate L x (selected i) = y i
    rw [hpos]
    change x j = y i
    change x j = if maskBit z j = true then 0 else values (Sum.inr j) at hh
    rw [if_neg hf] at hh
    exact hh.trans (by rw [← hpos]; exact hvalues i)

end Generic
end AESConcrete.MixedSelectedSurjection
