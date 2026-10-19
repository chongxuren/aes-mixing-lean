import AESPaper.RestrictedSourceSections
import AESConcrete.RestrictedCoordinateChoices

/-!
# Finite masks for restricted whole-word responses

These wrappers reuse the frozen four-coordinate subset certificates. They
concern coordinate labels only; no byte response estimate is imported as a
whole-word estimate. The selected input masks avoid the inactive inputs, and
the output masks partition exactly the requested marked coordinates.
-/
set_option autoImplicit false
noncomputable section
namespace AESPaper.ResponseMaskSelection
open AESMixing
open AESMixing.AES (maskBit maskSize)

theorem maskSize_le_four (m : Fin 16) : maskSize m ≤ 4 :=
  AESConcrete.RestrictedCoordinateChoices.maskSize_le_four m

/-- Two disjoint free-input groups of prescribed total and observed sizes. -/
theorem input_choices (z : Fin 16) (d j : Fin 5)
    (hz : maskSize z + d.val ≤ 4) (hj : j.val ≤ d.val) :
    ∃ s u : Fin 16, MaskDisjoint s u ∧ MaskDisjoint z (maskUnion s u) ∧
      maskSize s + maskSize u = d.val ∧ maskSize u = j.val :=
  AESConcrete.RestrictedCoordinateChoices.input_choices z d j hz hj

/-- The low branch receives both size identities needed by its source API. -/
theorem low_input_choices (r z out : Fin 16)
    (hshort : maskSize r + maskSize z ≤ 4)
    (hlow : maskSize out ≤ 4-maskSize r-maskSize z) :
    ∃ s u : Fin 16, MaskDisjoint s u ∧ MaskDisjoint z (maskUnion s u) ∧
      maskSize r + maskSize z + maskSize s + maskSize u = 4 ∧
      maskSize u = maskSize out ∧
      maskSize r + maskSize z + maskSize out + maskSize s = 4 := by
  let d : Fin 5 := ⟨4-maskSize r-maskSize z, by omega⟩
  let j : Fin 5 := ⟨maskSize out, by have h := maskSize_le_four out; omega⟩
  obtain ⟨s,u,hsu,hzu,hs,hu⟩ := input_choices z d j (by dsimp [d]; omega) hlow
  refine ⟨s,u,hsu,hzu,?_,hu,?_⟩ <;> dsimp [d,j] at * <;> omega

/-- A marked core and its disjoint complement partition the requested mask. -/
theorem output_choices (out : Fin 16) (d : ℕ) (hd : d ≤ maskSize out) :
    ∃ core extra : Fin 16, MaskDisjoint core extra ∧ maskUnion core extra = out ∧
      maskSize core = d ∧ maskSize extra = maskSize out-d := by
  let d' : Fin 5 := ⟨d, by have h := maskSize_le_four out; omega⟩
  obtain ⟨core,extra,hce,he,hc⟩ :=
    AESConcrete.RestrictedCoordinateChoices.output_choices out d' hd
  refine ⟨core,extra,hce,he,hc,?_⟩
  have hsize := maskUnion_size core extra hce
  rw [he] at hsize
  dsimp [d'] at hc
  omega

/-- Disjointness from the marked set passes to its selected core. -/
theorem disjoint_core (r core extra : Fin 16)
    (hr : MaskDisjoint r (maskUnion core extra)) : MaskDisjoint r core := by
  intro i hi hc
  apply hr i hi
  rw [maskUnion_bit, Bool.or_eq_true]
  exact Or.inl hc

/-- The explicit coordinate map keeps the physical coordinate value. -/
def unionCoordinateEquiv (core extra : Fin 16) (hd : MaskDisjoint core extra) :
    MaskCoordinates core ⊕ MaskCoordinates extra ≃ MaskCoordinates (maskUnion core extra) :=
  AESConcrete.RestrictedCoordinateChoices.unionCoordinateEquiv core extra hd

theorem unionCoordinateEquiv_val (core extra : Fin 16) (hd : MaskDisjoint core extra)
    (i : MaskCoordinates core ⊕ MaskCoordinates extra) :
    (unionCoordinateEquiv core extra hd i).val = Sum.elim Subtype.val Subtype.val i :=
  AESConcrete.RestrictedCoordinateChoices.unionCoordinateEquiv_val core extra hd i

/-- The same explicit partition with the caller's requested output mask. -/
def splitCoordinateEquiv (out core extra : Fin 16) (hd : MaskDisjoint core extra)
    (he : maskUnion core extra = out) :
    MaskCoordinates out ≃ MaskCoordinates core ⊕ MaskCoordinates extra := by
  subst out
  exact (unionCoordinateEquiv core extra hd).symm

theorem splitCoordinateEquiv_symm_val (out core extra : Fin 16)
    (hd : MaskDisjoint core extra) (he : maskUnion core extra = out)
    (i : MaskCoordinates core ⊕ MaskCoordinates extra) :
    ((splitCoordinateEquiv out core extra hd he).symm i).val =
      Sum.elim Subtype.val Subtype.val i := by
  subst out
  exact unionCoordinateEquiv_val core extra hd i

end AESPaper.ResponseMaskSelection
