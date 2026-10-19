import AESConcrete.FifthMomentHolder
import AESConcrete.ActualMarkedCodeMoment
import AESConcrete.RestrictedMDSCoordinates

/-!
# Five-factor entry bounds on the actual shortened MDS graph

A physical partition separates d-1 fixed coordinates from five remaining
coordinates. Each fixed section is parametrized by one byte; every one
of its five physical coordinate maps is proved bijective using an actual
MDS information projection. Holder and the mass-one fixed factors bound
the raw graph sum. No independence of graph coordinates is assumed.

Constructive mathematics only; no attacks, numerical workloads,
manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MDSFiveFactorEntry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse (remaining)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

abbrev RemainingPosition (r z : Fin 16) := {p : GraphPosition // remaining r z p}

def remainingEquiv (r z : Fin 16) : RemainingPosition r z ≃
    MaskCoordinates (maskComplement r) ⊕ MaskCoordinates (maskComplement z) where
  toFun p := match p with
    | ⟨Sum.inl i,h⟩ => Sum.inl ⟨i,by
        cases hb : maskBit r i <;> simp_all [remaining, maskComplement_bit]⟩
    | ⟨Sum.inr i,h⟩ => Sum.inr ⟨i,by
        cases hb : maskBit z i <;> simp_all [remaining, maskComplement_bit]⟩
  invFun p := match p with
    | Sum.inl i => ⟨Sum.inl i.val,by
        have hi := i.property
        cases hb : maskBit r i.val <;> simp_all [remaining, maskComplement_bit]⟩
    | Sum.inr i => ⟨Sum.inr i.val,by
        have hi := i.property
        cases hb : maskBit z i.val <;> simp_all [remaining, maskComplement_bit]⟩
  left_inv p := by rcases p with ⟨p,h⟩; cases p <;> rfl
  right_inv p := by cases p <;> rfl

theorem remaining_card (r z : Fin 16) :
    Fintype.card (RemainingPosition r z) = 8 - (maskSize r + maskSize z) := by
  have h := Fintype.card_congr (remainingEquiv r z)
  rw [Fintype.card_sum, maskCoordinates_card, maskCoordinates_card,
    maskComplement_size, maskComplement_size] at h
  have hr := maskSize_le_four r
  have hz := maskSize_le_four z
  omega

section PhysicalSections
variable {I V : Type*} [Fintype I] [DecidableEq I]
    [AddCommGroup V] [Fintype V] [DecidableEq V]

def extendIndex (k : Fin 5) : I ⊕ Unit → I ⊕ Fin 5 :=
  Sum.elim Sum.inl (fun _ => Sum.inr k)

theorem extendIndex_injective (k : Fin 5) : Function.Injective (extendIndex (I := I) k) := by
  intro a b h
  cases a <;> cases b <;> simp_all [extendIndex]

def selectedPositions {r z : Fin 16} (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (k : Fin 5) : I ⊕ Unit → GraphPosition := fun a => (idx (extendIndex k a)).val

theorem selectedPositions_injective {r z : Fin 16}
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z) (k : Fin 5) :
    Function.Injective (selectedPositions idx k) := by
  intro a b h
  exact extendIndex_injective k (idx.injective (Subtype.ext h))

def sumUnitArrowEquiv : ((I ⊕ Unit) → V) ≃ (I → V) × V where
  toFun f := (fun i => f (Sum.inl i), f (Sum.inr ()))
  invFun a := Sum.elim a.1 (fun _ => a.2)
  left_inv f := by funext a; cases a <;> rfl
  right_inv a := rfl

def projectionPair (L : (Fin 4 → V) →+ (Fin 4 → V)) {r z : Fin 16}
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z) (k : Fin 5) (c : ShortenedGraph L r z) :
    (I → V) × V :=
  (fun i => graphCoordinate L c.val (idx (Sum.inl i)).val,
    graphCoordinate L c.val (idx (Sum.inr k)).val)

theorem projectionPair_bijective (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : maskSize r + maskSize z + Fintype.card I + 1 = 4) (k : Fin 5) :
    Function.Bijective (projectionPair L idx k) := by
  have hb := ActualMarkedCodeMoment.selected_projection_bijective L hL r z
    (selectedPositions idx k) (selectedPositions_injective idx k)
    (fun a => (idx (extendIndex k a)).property) (by
      simp only [Fintype.card_sum, Fintype.card_unit]
      omega)
  exact (sumUnitArrowEquiv (I := I) (V := V)).bijective.comp hb

def projectionEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : maskSize r + maskSize z + Fintype.card I + 1 = 4) (k : Fin 5) :
    ShortenedGraph L r z ≃ (I → V) × V :=
  Equiv.ofBijective (projectionPair L idx k) (projectionPair_bijective L hL r z idx hsize k)

def sectionSource (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : maskSize r + maskSize z + Fintype.card I + 1 = 4)
    (a : I → V) (v : V) : ShortenedGraph L r z :=
  (projectionEquiv L hL r z idx hsize 0).symm (a,v)

theorem section_fixed (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : maskSize r + maskSize z + Fintype.card I + 1 = 4)
    (a : I → V) (v : V) (i : I) :
    graphCoordinate L (sectionSource L hL r z idx hsize a v).val (idx (Sum.inl i)).val = a i := by
  exact congrFun (congrArg Prod.fst ((projectionEquiv L hL r z idx hsize 0).apply_symm_apply (a,v))) i

theorem section_coordinate_bijective (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : maskSize r + maskSize z + Fintype.card I + 1 = 4)
    (a : I → V) (k : Fin 5) :
    Function.Bijective (fun v : V =>
      graphCoordinate L (sectionSource L hL r z idx hsize a v).val (idx (Sum.inr k)).val) :=
  RestrictedMDSCoordinates.section_bijective (projectionEquiv L hL r z idx hsize 0)
    (projectionEquiv L hL r z idx hsize k) (fun _ => rfl) a

def sectionEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : maskSize r + maskSize z + Fintype.card I + 1 = 4)
    (a : I → V) (k : Fin 5) : V ≃ V :=
  Equiv.ofBijective (fun v =>
    graphCoordinate L (sectionSource L hL r z idx hsize a v).val (idx (Sum.inr k)).val)
    (section_coordinate_bijective L hL r z idx hsize a k)

end PhysicalSections

section Entry
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def graphResponse (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (T : RemainingPosition r z → V → ℝ) : ℝ :=
  ∑ c : ShortenedGraph L r z, ∏ p : RemainingPosition r z, T p (graphCoordinate L c.val p.val)

theorem graphResponse_zero_of_high_zeros
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hz : 4 ≤ maskSize r + maskSize z) (T : RemainingPosition r z → V → ℝ)
    (p : RemainingPosition r z) (hp : T p 0 = 0) : graphResponse L r z T = 0 := by
  unfold graphResponse
  apply Finset.sum_eq_zero
  intro c _
  have hc : c.val = 0 := mds_graph_zero_high L hL r z hz c.val c.property
  apply Finset.prod_eq_zero (Finset.mem_univ p)
  rw [hc]
  have h0 : graphCoordinate L (0 : Fin 4 → V) p.val = 0 := by
    cases p.val <;> simp [graphCoordinate]
  rw [h0, hp]

theorem graphResponse_le_of_split {I : Type*} [Fintype I] [DecidableEq I]
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (idx : I ⊕ Fin 5 ≃ RemainingPosition r z)
    (hsize : maskSize r + maskSize z + Fintype.card I + 1 = 4)
    (T : RemainingPosition r z → V → ℝ) (hnonneg : ∀ p v, 0 ≤ T p v)
    (hmass : ∀ p, (∑ v : V, T p v) = 1) (H : ℝ)
    (hmoment : ∀ p, (∑ v : V, T p v ^ 5) ≤ H) : graphResponse L r z T ≤ H := by
  let weight (a : I → V) : ℝ := ∏ i : I, T (idx (Sum.inl i)) (a i)
  let remainder (a : I → V) (v : V) : ℝ := ∏ k : Fin 5,
    T (idx (Sum.inr k))
      (graphCoordinate L (sectionSource L hL r z idx hsize a v).val (idx (Sum.inr k)).val)
  have hsection (a : I → V) : (∑ v : V, remainder a v) ≤ H :=
    FifthMomentHolder.sum_prod_bijective_le (sectionEquiv L hL r z idx hsize a)
      (fun k => T (idx (Sum.inr k))) (fun k v => hnonneg _ v) H (fun k => hmoment _)
  have hweight (a : I → V) : 0 ≤ weight a :=
    Finset.prod_nonneg (fun i _ => hnonneg _ _)
  have hmassfixed : (∑ a : I → V, weight a) = 1 := by
    dsimp only [weight]
    rw [← Fintype.prod_sum]
    simp only [hmass, Finset.prod_const_one]
  have hprod (a : I → V) (v : V) :
      (∏ p : RemainingPosition r z,
        T p (graphCoordinate L (sectionSource L hL r z idx hsize a v).val p.val)) =
        weight a * remainder a v := by
    rw [← idx.prod_comp (fun p : RemainingPosition r z =>
      T p (graphCoordinate L (sectionSource L hL r z idx hsize a v).val p.val))]
    rw [Fintype.prod_sum_type]
    dsimp only [weight, remainder]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [section_fixed]
  have hsum : graphResponse L r z T = ∑ a : I → V, weight a * ∑ v : V, remainder a v := by
    calc
      _ = ∑ av : (I → V) × V, ∏ p : RemainingPosition r z,
          T p (graphCoordinate L (sectionSource L hL r z idx hsize av.1 av.2).val p.val) :=
        ((projectionEquiv L hL r z idx hsize 0).symm.sum_comp (fun c : ShortenedGraph L r z =>
          ∏ p : RemainingPosition r z, T p (graphCoordinate L c.val p.val))).symm
      _ = ∑ a : I → V, ∑ v : V, weight a * remainder a v := by
        rw [Fintype.sum_prod_type]
        simp only [hprod]
      _ = _ := by simp only [Finset.mul_sum]
  rw [hsum]
  calc
    _ ≤ ∑ a : I → V, weight a * H :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hsection a) (hweight a))
    _ = H := by rw [← Finset.sum_mul, hmassfixed, one_mul]

/-- Actual physical selection is constructed internally. The only
analytic premises are per-leg nonnegativity, mass one and a raw fifth cap. -/
theorem graphResponse_le_fifth
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (hz : maskSize r + maskSize z ≤ 3)
    (T : RemainingPosition r z → V → ℝ) (hnonneg : ∀ p v, 0 ≤ T p v)
    (hmass : ∀ p, (∑ v : V, T p v) = 1) (H : ℝ)
    (hmoment : ∀ p, (∑ v : V, T p v ^ 5) ≤ H) : graphResponse L r z T ≤ H := by
  let idx : (Fin (3 - (maskSize r + maskSize z))) ⊕ Fin 5 ≃ RemainingPosition r z :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, remaining_card]
      omega)
  exact graphResponse_le_of_split L hL r z idx (by
    rw [Fintype.card_fin]
    omega) T hnonneg hmass H hmoment

end Entry
end AESConcrete.MDSFiveFactorEntry
