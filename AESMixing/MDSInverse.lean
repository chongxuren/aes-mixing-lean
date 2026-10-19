import AESMixing.MDSProjection
import AESMixing.ActivitySpan

/-! The inverse of a four-coordinate MDS additive permutation is MDS.
The proof exchanges supported and zero coordinates by complementation. -/
noncomputable section
namespace AESMixing
open AES (maskBit maskSize)

def maskComplement (m : Fin 16) : Fin 16 := ⟨15-m.val,by omega⟩

theorem maskComplement_bit : ∀ (m : Fin 16) (i : Fin 4),
    maskBit (maskComplement m) i = !(maskBit m i) := by decide

theorem maskComplement_size : ∀ m : Fin 16,
    maskSize (maskComplement m) = 4-maskSize m := by decide

theorem maskComplement_involutive : ∀ m : Fin 16,
    maskComplement (maskComplement m) = m := by decide

theorem maskProjection_complement_iff {V : Type*} [Zero V]
    (m : Fin 16) (x : Fin 4 → V) :
    maskProjection (maskComplement m) x = x ↔ maskProjection m x = 0 := by
  constructor <;> intro h <;> funext i
  all_goals
    have hi := congrFun h i
    cases hb : maskBit m i <;> simp_all [maskProjection,maskComplement_bit]

theorem zeroMDS_inverse {V : Type*} [AddCommGroup V]
    (L : (Fin 4 → V) ≃+ (Fin 4 → V)) (hL : ZeroMDS L) : ZeroMDS L.symm := by
  intro r c hrc y hy hz
  have hs : maskProjection (maskComplement r) (L.symm y) = L.symm y :=
    (maskProjection_complement_iff r _).mpr hz
  have hz' : maskProjection (maskComplement c) (L (L.symm y)) = 0 := by
    rw [L.apply_symm_apply]
    apply (maskProjection_complement_iff (maskComplement c) y).mp
    simpa only [maskComplement_involutive] using hy
  have he := hL (maskComplement c) (maskComplement r)
    (by rw [maskComplement_size,maskComplement_size,hrc]) (L.symm y) hs hz'
  have hh := congrArg L he
  simpa only [L.apply_symm_apply,map_zero] using hh

def byteDiffusionAddEquiv : (Fin 4 → BinaryWord 8) ≃+ (Fin 4 → BinaryWord 8) :=
  {byteDiffusionEquiv with map_add' := (AES.columnMatrix AES.mixEntry).map_add}

theorem byteDiffusionAddEquiv_zeroMDS : ZeroMDS byteDiffusionAddEquiv :=
  byteMixColumns_zeroMDS

theorem byteDiffusionAddEquiv_inverse_zeroMDS : ZeroMDS byteDiffusionAddEquiv.symm :=
  zeroMDS_inverse byteDiffusionAddEquiv byteDiffusionAddEquiv_zeroMDS

end AESMixing
