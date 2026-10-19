import AESMixing.WordDiffusion

/-! The concrete MDS zero condition implies bijective coordinate projections.
Counts are derived from finite bijections, not from assumed rank formulas. -/
namespace AESMixing
open scoped BigOperators
open AES

abbrev MaskCoordinates (mask : Fin 16) := {i : Fin 4 // maskBit mask i = true}

theorem maskCoordinates_card (mask : Fin 16) :
    Fintype.card (MaskCoordinates mask) = maskSize mask := by
  exact Fintype.card_subtype _

def maskProjection {V : Type*} [Zero V] (mask : Fin 16) (x : Fin 4 → V) : Fin 4 → V :=
  fun i => if maskBit mask i then x i else 0

def extendCoordinates {V : Type*} [Zero V] (mask : Fin 16)
    (x : MaskCoordinates mask → V) : Fin 4 → V :=
  fun i => if h : maskBit mask i = true then x ⟨i, h⟩ else 0

def restrictCoordinates {V : Type*} (mask : Fin 16) (x : Fin 4 → V) : MaskCoordinates mask → V :=
  fun i => x i.val

theorem restrict_extend {V : Type*} [Zero V] (mask : Fin 16)
    (x : MaskCoordinates mask → V) : restrictCoordinates mask (extendCoordinates mask x) = x := by
  funext i
  simp [restrictCoordinates, extendCoordinates, i.property]

theorem extend_supported {V : Type*} [Zero V] (mask : Fin 16)
    (x : MaskCoordinates mask → V) : maskProjection mask (extendCoordinates mask x) = extendCoordinates mask x := by
  funext i
  by_cases h : maskBit mask i = true <;> simp [maskProjection, extendCoordinates, h]

def restrictedMap {V : Type*} [Zero V] (L : (Fin 4 → V) → (Fin 4 → V))
    (r c : Fin 16) (x : MaskCoordinates c → V) : MaskCoordinates r → V :=
  restrictCoordinates r (L (extendCoordinates c x))

def ZeroMDS {V : Type*} [Zero V] (L : (Fin 4 → V) → (Fin 4 → V)) : Prop :=
  ∀ r c : Fin 16, maskSize r = maskSize c → ∀ x,
    maskProjection c x = x → maskProjection r (L x) = 0 → x = 0

theorem mds_restricted_injective {V : Type*} [AddCommGroup V]
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hsize : maskSize r = maskSize c) :
    Function.Injective (restrictedMap L r c) := by
  intro x y he
  have hext : extendCoordinates c x - extendCoordinates c y = 0 := by
    apply hL r c hsize
    · funext i
      by_cases hi : maskBit c i = true <;>
        simp [maskProjection, extendCoordinates, hi]
    · rw [map_sub]
      funext i
      by_cases hi : maskBit r i = true
      · have hh := congrFun he (⟨i,hi⟩ : MaskCoordinates r)
        change L (extendCoordinates c x) i = L (extendCoordinates c y) i at hh
        simp [maskProjection, hi, hh]
      · simp [maskProjection, hi]
  have hf : extendCoordinates c x = extendCoordinates c y := sub_eq_zero.mp hext
  have hr := congrArg (restrictCoordinates c) hf
  simpa only [restrict_extend] using hr

theorem mds_restricted_bijective {V : Type*} [AddCommGroup V] [Fintype V]
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r c : Fin 16) (hsize : maskSize r = maskSize c) :
    Function.Bijective (restrictedMap L r c) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨mds_restricted_injective L hL r c hsize, ?_⟩
  simp only [Fintype.card_fun, maskCoordinates_card, hsize]

theorem byteMixColumns_zeroMDS : ZeroMDS (columnMatrix mixEntry) := by
  intro r c h x hs hz
  exact mixColumns_mds_zero r c h x hs hz

theorem byteMixColumns_restricted_bijective (r c : Fin 16) (h : maskSize r = maskSize c) :
    Function.Bijective (restrictedMap (columnMatrix mixEntry) r c) :=
  mds_restricted_bijective (columnMatrix mixEntry) byteMixColumns_zeroMDS r c h

end AESMixing
