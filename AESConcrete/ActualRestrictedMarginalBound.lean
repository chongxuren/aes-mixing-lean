import AESConcrete.RestrictedCoordinateChoices
import AESConcrete.RestrictedSourcePushforward

/-!
# The restricted-marginal bound for actual AES columns

Coordinate subsets are selected by proved finite certificates. Both branches
are combined on the original marked output type, and the final theorem is
stated on the full-word source with only the intended output-zero event and
an arbitrary further event. No event probability is divided out.

Constructive mathematics only; no attacks or manuscript edits. This local
response estimate still needs orthogonal support aggregation to bound the
complete multibyte column.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualRestrictedMarginalBound
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.WordColumnGram (Byte Word tensorResponse)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom)
open AESConcrete.ActualRestrictedDensity (restrictedSource outputCoordinates)
open AESConcrete.RestrictedCoordinateChoices

theorem high_union_energy (right : Orientation) (inverse : Bool) (a : Word)
    (r z s u core extra : Fin 16) (hsu : MaskDisjoint s u)
    (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hd : MaskDisjoint core extra) (hr : MaskDisjoint r (maskUnion core extra))
    (hcore : maskSize r + maskSize z + maskSize core = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event]
    (o : MaskCoordinates (maskUnion core extra) → Orientation) :
    (∑ y : MaskCoordinates (maskUnion core extra) → Byte,
      tensorResponse (fun i => residualMatrix (channel (o i)) 0)
        (outputCoordinates inverse r z (maskUnion core extra))
        (restrictedSource right inverse a r z event) y^2) ≤
      ((1 : ℝ)/64)^(2*maskSize r) *
        (((65 : ℝ)/8192)*((9 : ℝ)/128)^2)^maskSize core *
          ((8383 : ℝ)/2088960)^maskSize extra := by
  let e := unionCoordinateEquiv core extra hd
  let oc := fun i : MaskCoordinates core => o (e (Sum.inl i))
  let oe := fun i : MaskCoordinates extra => o (e (Sum.inr i))
  have hrc : MaskDisjoint r core := by
    intro i hi hc
    apply hr i hi
    rw [maskUnion_bit, Bool.or_eq_true]
    exact Or.inl hc
  have h := ActualRestrictedColumnResponse.high_observed_energy right inverse a
    r z s u core extra hsu hzu hsize hrc hcore ha event oc oe
  have he := tensorResponse_reindex_energy e (fun i => residualMatrix (channel (o i)) 0)
    (outputCoordinates inverse r z (maskUnion core extra))
    (restrictedSource right inverse a r z event)
  have hT : (fun k => residualMatrix (channel (o (e k))) 0) =
      Sum.elim (fun i => residualMatrix (channel (oc i)) 0)
        (fun i => residualMatrix (channel (oe i)) 0) := by
    funext k
    cases k <;> rfl
  have hC : (fun c k => outputCoordinates inverse r z (maskUnion core extra) c (e k)) =
      (fun c => Sum.elim (outputCoordinates inverse r z core c)
        (outputCoordinates inverse r z extra c)) := by
    funext c k
    cases k <;> rfl
  rw [hT,hC] at he
  rw [← he]
  exact h

/-- The uniform two-branch statement, with actual source and channels. -/
theorem shortened_response_energy (right : Orientation) (inverse : Bool) (a : Word)
    (r z out : Fin 16) (hr : MaskDisjoint r out)
    (hshort : maskSize r + maskSize z ≤ 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event]
    (o : MaskCoordinates out → Orientation) :
    (∑ y : MaskCoordinates out → Byte,
      tensorResponse (fun i => residualMatrix (channel (o i)) 0)
        (outputCoordinates inverse r z out) (restrictedSource right inverse a r z event) y^2) ≤
      ((1 : ℝ)/64)^(2*maskSize r) *
        (((65 : ℝ)/8192)*((9 : ℝ)/128)^2)^(min (4-maskSize r-maskSize z) (maskSize out)) *
          ((8383 : ℝ)/2088960)^(maskSize out-min (4-maskSize r-maskSize z) (maskSize out)) := by
  let d : Fin 5 := ⟨4-maskSize r-maskSize z, by omega⟩
  by_cases hl : maskSize out ≤ d.val
  · let j : Fin 5 := ⟨maskSize out, by have h := AESMixing.maskSize_le_four out; omega⟩
    obtain ⟨s,u,hsu,hzu,hsum,hu⟩ := input_choices z d j (by dsimp [d]; omega) hl
    have hs : maskSize r + maskSize z + maskSize s + maskSize u = 4 := by
      dsimp [d] at hsum
      omega
    have ho : maskSize r + maskSize z + maskSize out + maskSize s = 4 := by
      dsimp [j] at hu
      omega
    have h := ActualRestrictedColumnResponse.low_observed_energy right inverse a
      r z s u out hsu hzu hs hr ho ha event o
    have hm : min (4-maskSize r-maskSize z) (maskSize out) = maskSize out :=
      Nat.min_eq_right hl
    simpa only [hm,Nat.sub_self,pow_zero,mul_one] using h
  · have hj : d.val ≤ maskSize out := by omega
    obtain ⟨s,u,hsu,hzu,hsum,hu⟩ := input_choices z d d (by dsimp [d]; omega) le_rfl
    obtain ⟨core,extra,hd,he,hc⟩ := output_choices out d hj
    subst out
    have hs : maskSize r + maskSize z + maskSize s + maskSize u = 4 := by
      dsimp [d] at hsum
      omega
    have hcore : maskSize r + maskSize z + maskSize core = 4 := by
      dsimp [d] at hc
      omega
    have h := high_union_energy right inverse a r z s u core extra hsu hzu hs hd hr hcore ha event o
    have hm : min (4-maskSize r-maskSize z) (maskSize (maskUnion core extra)) = maskSize core := by
      rw [Nat.min_eq_left hj]
      exact hc.symm
    have hextra : maskSize (maskUnion core extra)-maskSize core = maskSize extra := by
      rw [maskUnion_size core extra hd]
      omega
    simpa only [hm,hextra] using h

/-- The same bound on the full-word event law: a concrete AES restriction. -/
theorem full_response_energy (right : Orientation) (inverse : Bool) (a : Word)
    (r z out : Fin 16) (hr : MaskDisjoint r out)
    (hshort : maskSize r + maskSize z ≤ 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : Word → Prop) [DecidablePred event] (o : MaskCoordinates out → Orientation) :
    (∑ y : MaskCoordinates out → Byte,
      tensorResponse (fun i => residualMatrix (channel (o i)) 0)
        (RestrictedSourcePushforward.fullOutputCoordinates inverse out)
        (RestrictedSourcePushforward.fullWordSource right inverse a r event) y^2) ≤
      ((1 : ℝ)/64)^(2*maskSize r) *
        (((65 : ℝ)/8192)*((9 : ℝ)/128)^2)^(min (4-maskSize r-maskSize z) (maskSize out)) *
          ((8383 : ℝ)/2088960)^(maskSize out-min (4-maskSize r-maskSize z) (maskSize out)) := by
  rw [← RestrictedSourcePushforward.shortened_tensorResponse_eq_full right inverse a r z ha event]
  exact shortened_response_energy right inverse a r z out hr hshort ha (fun c => event c.val) o

end AESConcrete.ActualRestrictedMarginalBound
