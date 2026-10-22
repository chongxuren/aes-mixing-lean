import AES8.Estimates.Word.PaperSharpEntriesInventoryAssembly

/-! Coverage interfaces only. A numerical pair module supplies PairCells; an
alpha-row module assembles255 pairs; the final theorem assembles255 rows.
Numerical data and transcript stages are not part of these interfaces. -/
namespace AES8.PaperSharpEntriesPairCoverage
open AES8.PaperSharpEntriesFinite AES8.PaperSharpEntriesInventoryAssembly
set_option autoImplicit false

structure PairCells (a b : Fin 255) : Prop where
  ordinary : ∀ (r : Fin 4) (gamma : Byte),
    mixedSum q ordinaryMapHom (nonzeroByte a) (nonzeroByte b) gamma (r.val+1) ≤ 111
  balanced : ∀ (r : Fin 2) (gamma : Byte),
    mixedSum h fourierMapHom (nonzeroByte a) (nonzeroByte b) gamma (r.val+2) ≤ 7247757311
  homogeneous : ∀ (r : Fin 2),
    mixedSum h fourierMapHom (nonzeroByte a) (nonzeroByte b) 0 (extremePower r) ≤ 7247757311

def RowCells (a : Fin 255) : Prop := ∀ b : Fin 255, PairCells a b

theorem complete_inventory_of_rows (rows : ∀ a : Fin 255, RowCells a) :
    CompleteInventory where
  ordinary a b r gamma := (rows a b).ordinary r gamma
  balanced a b r gamma := (rows a b).balanced r gamma
  homogeneous a b r := (rows a b).homogeneous r

theorem required_raw_bounds_of_rows (rows : ∀ a : Fin 255, RowCells a) :
    OrdinaryRawBound ∧ FourierRawBound fourierMapHom :=
  required_raw_bounds (complete_inventory_of_rows rows)

end AES8.PaperSharpEntriesPairCoverage
