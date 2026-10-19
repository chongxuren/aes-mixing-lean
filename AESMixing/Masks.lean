import AESMixing.MatrixLinear
import AESMixing.AESState

/-! Four-coordinate zero constraints. Masks name subsets, not activity laws. -/
namespace AESMixing.AES
open scoped BigOperators

def maskBit (mask : Fin 16) (i : Fin 4) : Bool := mask.val.testBit i.val

def maskSize (mask : Fin 16) : ℕ :=
  (Finset.univ.filter (fun i : Fin 4 => maskBit mask i)).card

def projectMask (mask : Fin 16) :
    (Fin 4 → BinaryWord 8) →+ (Fin 4 → BinaryWord 8) where
  toFun x i := if maskBit mask i then x i else 0
  map_zero' := by funext i; simp
  map_add' x y := by funext i; cases h : maskBit mask i <;> simp [h]

theorem projectMask_idempotent (mask : Fin 16) (x : Fin 4 → BinaryWord 8) :
    projectMask mask (projectMask mask x) = projectMask mask x := by
  funext i
  simp only [projectMask, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs <;> rfl

/-- A certificate on the binary basis reconstructs every allowed input. -/
theorem masked_reconstruction_from_basis (M R : Fin 4 → Fin 4 → Byte) (r c : Fin 16)
    (h : ∀ j b,
      columnMatrix R (projectMask r (columnMatrix M (projectMask c (injectByte j (byteBasis b))))) =
        projectMask c (injectByte j (byteBasis b))) (x : Fin 4 → BinaryWord 8) :
    columnMatrix R (projectMask r (columnMatrix M (projectMask c x))) = projectMask c x := by
  let f := (columnMatrix R).comp ((projectMask r).comp ((columnMatrix M).comp (projectMask c)))
  have he : f = projectMask c := column_addHom_ext f (projectMask c) h
  exact DFunLike.congr_fun he x

theorem masked_zero_from_reconstruction (M R : Fin 4 → Fin 4 → Byte) (r c : Fin 16)
    (h : ∀ x, columnMatrix R (projectMask r (columnMatrix M (projectMask c x))) = projectMask c x)
    (x : Fin 4 → BinaryWord 8) (hs : projectMask c x = x)
    (hz : projectMask r (columnMatrix M x) = 0) : x = 0 := by
  have he := h x
  rw [hs, hz, map_zero] at he
  exact he.symm

end AESMixing.AES
