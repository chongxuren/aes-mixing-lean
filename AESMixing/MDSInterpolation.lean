import AESMixing.MDSProjection

/-! Arbitrary prescribed input/output information sets of the MDS graph.
Any equal number of unknown inputs and prescribed outputs determine one word. -/
namespace AESMixing
open AES

variable {V : Type*} [AddCommGroup V] [Fintype V]

def ComplementCoordinates (mask : Fin 16) := {i : Fin 4 // maskBit mask i ≠ true}

instance (mask : Fin 16) : Fintype (ComplementCoordinates mask) := inferInstanceAs
  (Fintype {i : Fin 4 // maskBit mask i ≠ true})

def extendComplement (mask : Fin 16) (x : ComplementCoordinates mask → V) : Fin 4 → V :=
  fun i => if h : maskBit mask i = true then 0 else x ⟨i, h⟩

def mdsInformation (L : (Fin 4 → V) →+ (Fin 4 → V)) (r c : Fin 16)
    (x : Fin 4 → V) : (MaskCoordinates r → V) × (ComplementCoordinates c → V) :=
  (restrictCoordinates r (L x), fun i => x i.val)

omit [Fintype V] in
theorem mds_information_injective (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r c : Fin 16) (hsize : maskSize r = maskSize c) :
    Function.Injective (mdsInformation L r c) := by
  intro x y he
  apply sub_eq_zero.mp
  apply hL r c hsize
  · funext i
    by_cases hi : maskBit c i = true
    · simp [maskProjection, hi]
    · have hh := congrFun (congrArg Prod.snd he) (⟨i,hi⟩ : ComplementCoordinates c)
      change x i = y i at hh
      simp [maskProjection, hi, hh]
  · rw [map_sub]
    funext i
    by_cases hi : maskBit r i = true
    · have hh := congrFun (congrArg Prod.fst he) (⟨i,hi⟩ : MaskCoordinates r)
      change L x i = L y i at hh
      simp [maskProjection, hi, hh]
    · simp [maskProjection, hi]

theorem mds_information_surjective (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r c : Fin 16) (hsize : maskSize r = maskSize c) :
    Function.Surjective (mdsInformation L r c) := by
  rintro ⟨out, known⟩
  let base : Fin 4 → V := extendComplement c known
  obtain ⟨unknown, hu⟩ := (mds_restricted_bijective L hL r c hsize).surjective
    (out - restrictCoordinates r (L base))
  refine ⟨extendCoordinates c unknown + base, ?_⟩
  apply Prod.ext
  · funext i
    have hh := congrFun hu i
    change L (extendCoordinates c unknown) i.val = out i - L base i.val at hh
    change L (extendCoordinates c unknown + base) i.val = out i
    rw [map_add]
    change L (extendCoordinates c unknown) i.val + L base i.val = out i
    rw [hh, sub_add_cancel]
  · funext i
    change extendCoordinates c unknown i.val + extendComplement c known i.val = known i
    simp [extendCoordinates, extendComplement, i.property]

theorem mds_information_bijective (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r c : Fin 16) (hsize : maskSize r = maskSize c) :
    Function.Bijective (mdsInformation L r c) :=
  ⟨mds_information_injective L hL r c hsize, mds_information_surjective L hL r c hsize⟩

end AESMixing
