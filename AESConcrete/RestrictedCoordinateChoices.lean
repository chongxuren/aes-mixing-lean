import AESConcrete.ActualRestrictedColumnResponse

/-!
# Coordinate choices and reindexing for a restricted column

Finite certificates select subsets of four coordinate labels only. The
response reindexing theorem applies to arbitrary signed source weights.
No alphabet-vector enumeration or probabilistic independence is used.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.RestrictedCoordinateChoices
open AESMixing
open AESMixing.AES (maskBit maskSize)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem input_choices : ∀ (z : Fin 16) (d k : Fin 5),
    maskSize z + d.val ≤ 4 → k.val ≤ d.val →
    ∃ s u : Fin 16, MaskDisjoint s u ∧ MaskDisjoint z (maskUnion s u) ∧
      maskSize s + maskSize u = d.val ∧ maskSize u = k.val := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem output_choices : ∀ (out : Fin 16) (d : Fin 5),
    d.val ≤ maskSize out → ∃ core extra : Fin 16,
      MaskDisjoint core extra ∧ maskUnion core extra = out ∧ maskSize core = d.val := by decide

theorem maskSize_le_four (m : Fin 16) : maskSize m ≤ 4 := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

def unionCoordinate (core extra : Fin 16) :
    MaskCoordinates core ⊕ MaskCoordinates extra → MaskCoordinates (maskUnion core extra)
  | Sum.inl i => ⟨i.val, by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl i.property⟩
  | Sum.inr i => ⟨i.val, by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inr i.property⟩

theorem unionCoordinate_bijective (core extra : Fin 16) (hd : MaskDisjoint core extra) :
    Function.Bijective (unionCoordinate core extra) := by
  constructor
  · intro i j h
    have hv := congrArg Subtype.val h
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subtype.ext hv)
      | inr j =>
        change i.val = j.val at hv
        have hj : maskBit extra i.val = true := by simpa only [hv] using j.property
        exact (hd i.val i.property hj).elim
    | inr i =>
      cases j with
      | inl j =>
        change i.val = j.val at hv
        have hi : maskBit extra j.val = true := by simpa only [← hv] using i.property
        exact (hd j.val j.property hi).elim
      | inr j => exact congrArg Sum.inr (Subtype.ext hv)
  · intro i
    have hi := i.property
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact ⟨Sum.inl ⟨i.val,hi⟩, Subtype.ext rfl⟩
    · exact ⟨Sum.inr ⟨i.val,hi⟩, Subtype.ext rfl⟩

def unionCoordinateEquiv (core extra : Fin 16) (hd : MaskDisjoint core extra) :
    MaskCoordinates core ⊕ MaskCoordinates extra ≃ MaskCoordinates (maskUnion core extra) :=
  Equiv.ofBijective (unionCoordinate core extra) (unionCoordinate_bijective core extra hd)

theorem unionCoordinateEquiv_val (core extra : Fin 16) (hd : MaskDisjoint core extra)
    (i : MaskCoordinates core ⊕ MaskCoordinates extra) :
    (unionCoordinateEquiv core extra hd i).val = Sum.elim Subtype.val Subtype.val i := by
  cases i <;> rfl

theorem tensorResponse_reindex_energy {X I K V : Type*}
    [Fintype X] [Fintype I] [Fintype K] [Fintype V] [DecidableEq I] [DecidableEq K]
    (e : K ≃ I) (T : I → V → V → ℝ) (coord : X → I → V) (g : X → ℝ) :
    (∑ y : K → V, WordColumnGram.tensorResponse (fun k => T (e k))
      (fun c k => coord c (e k)) g y ^ 2) =
    ∑ y : I → V, WordColumnGram.tensorResponse T coord g y ^ 2 := by
  let E := FiniteTensorEnergy.indexTupleEquiv (V := V) e
  have hv (y : K → V) : WordColumnGram.tensorResponse (fun k => T (e k))
      (fun c k => coord c (e k)) g y = WordColumnGram.tensorResponse T coord g (E y) := by
    unfold WordColumnGram.tensorResponse WordColumnGram.tensorColumn
    apply Finset.sum_congr rfl
    intro c _
    apply congrArg (· * g c)
    have he := e.prod_comp (fun i => T i (E y i) (coord c i))
    simpa only [E, FiniteTensorEnergy.indexTupleEquiv, Equiv.coe_fn_mk,
      Equiv.symm_apply_apply] using he
  simp_rw [hv]
  exact E.sum_comp (fun y => WordColumnGram.tensorResponse T coord g y^2)

end AESConcrete.RestrictedCoordinateChoices
