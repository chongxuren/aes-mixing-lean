import AESMixing.AESMDSCount

/-! Prescribing zeros shortens the MDS graph. Every remaining information set
of the resulting dimension is a bijective projection, proved by subtraction
and the concrete graph count rather than an assumed coding-theory theorem. -/
namespace AESMixing
open AES

def maskUnion (r s : Fin 16) : Fin 16 :=
  ((BitVec.ofFin r : BitVec 4) ||| (BitVec.ofFin s : BitVec 4)).toFin

def MaskDisjoint (r s : Fin 16) : Prop :=
  ∀ i : Fin 4, maskBit r i = true → maskBit s i ≠ true

instance (r s : Fin 16) : Decidable (MaskDisjoint r s) := by
  unfold MaskDisjoint
  infer_instance

set_option maxRecDepth 100000 in
theorem maskUnion_bit : ∀ r s : Fin 16, ∀ i : Fin 4,
    maskBit (maskUnion r s) i = (maskBit r i || maskBit s i) := by decide

set_option maxRecDepth 100000 in
theorem maskUnion_size : ∀ r s : Fin 16, MaskDisjoint r s →
    maskSize (maskUnion r s) = maskSize r + maskSize s := by decide

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

abbrev ShortenedGraph (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) :=
  {x : Fin 4 → V // graphZeroConditions L r z x}

def shortenedProjection (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (x : ShortenedGraph L r z) :
    (MaskCoordinates out → V) × (MaskCoordinates inp → V) :=
  (fun i => L x.val i.val, fun i => x.val i.val)

omit [Fintype V] [DecidableEq V] in
theorem shortened_projection_injective (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize out + maskSize inp = 4) :
    Function.Injective (shortenedProjection L r z out inp) := by
  intro x y he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply mds_graph_zero_high L hL (maskUnion r out) (maskUnion z inp)
  · rw [maskUnion_size r out hr, maskUnion_size z inp hz]
    omega
  · constructor
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rw [map_sub]
      change L x.val i - L y.val i = 0
      apply sub_eq_zero.mpr
      rcases hi with hi | hi
      · rw [x.property.1 i hi, y.property.1 i hi]
      · exact congrFun (congrArg Prod.fst he) (⟨i,hi⟩ : MaskCoordinates out)
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      change x.val i - y.val i = 0
      apply sub_eq_zero.mpr
      rcases hi with hi | hi
      · rw [x.property.2 i hi, y.property.2 i hi]
      · exact congrFun (congrArg Prod.snd he) (⟨i,hi⟩ : MaskCoordinates inp)

theorem shortened_projection_bijective (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize out + maskSize inp = 4) :
    Function.Bijective (shortenedProjection L r z out inp) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨shortened_projection_injective L hL r z out inp hr hz hsize, ?_⟩
  change Fintype.card {x : Fin 4 → V // graphZeroConditions L r z x} = _
  rw [mds_graph_zero_count L hL, Fintype.card_prod]
  simp only [Fintype.card_fun, maskCoordinates_card]
  rw [← pow_add]
  congr 1
  omega

noncomputable def shortenedProjectionEquiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize out + maskSize inp = 4) :
    ShortenedGraph L r z ≃ ((MaskCoordinates out ⊕ MaskCoordinates inp) → V) :=
  (Equiv.ofBijective (shortenedProjection L r z out inp)
    (shortened_projection_bijective L hL r z out inp hr hz hsize)).trans
      (Equiv.sumArrowEquivProdArrow (MaskCoordinates out) (MaskCoordinates inp) V).symm

end AESMixing
