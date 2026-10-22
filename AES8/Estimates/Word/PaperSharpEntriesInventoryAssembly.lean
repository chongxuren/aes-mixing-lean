import AES8.Estimates.Word.PaperSharpEntriesByteMaps

/-! Quantified assembly only. Supplying these cells still requires the full
finite certificate inventory; this leaf proves no unprovided numerical cap. -/
namespace AES8.PaperSharpEntriesInventoryAssembly
open AES8.PaperSharpEntriesFinite
set_option autoImplicit false

def OrdinaryCells : Prop := ∀ (a b : Fin 255) (r : Fin 4) (gamma : Byte),
  mixedSum q ordinaryMapHom (nonzeroByte a) (nonzeroByte b) gamma (r.val+1) ≤ 111
def FourierBalancedCells : Prop := ∀ (a b : Fin 255) (r : Fin 2) (gamma : Byte),
  mixedSum h fourierMapHom (nonzeroByte a) (nonzeroByte b) gamma (r.val+2) ≤ 7247757311
def extremePower (r : Fin 2) : ℕ := if r.val = 0 then 1 else 4
def FourierHomogeneousCells : Prop := ∀ (a b : Fin 255) (r : Fin 2),
  mixedSum h fourierMapHom (nonzeroByte a) (nonzeroByte b) 0 (extremePower r) ≤ 7247757311

structure CompleteInventory : Prop where
  ordinary : OrdinaryCells
  balanced : FourierBalancedCells
  homogeneous : FourierHomogeneousCells

theorem ordinary_of_cells (hc : OrdinaryCells) : OrdinaryRawBound := by
  intro alpha beta gamma r ha hb hlo hhi
  obtain ⟨a, rfl⟩ := nonzeroByte_covers alpha ha
  obtain ⟨b, rfl⟩ := nonzeroByte_covers beta hb
  let t : Fin 4 := ⟨r-1, by omega⟩
  have ht : t.val+1 = r := by dsimp [t]; omega
  simpa only [ht] using hc a b t gamma

theorem fourier_of_cells (hbalanced : FourierBalancedCells)
    (hhomogeneous : FourierHomogeneousCells) : FourierRawBound fourierMapHom := by
  constructor
  · intro alpha beta gamma r ha hb hr
    obtain ⟨a, rfl⟩ := nonzeroByte_covers alpha ha
    obtain ⟨b, rfl⟩ := nonzeroByte_covers beta hb
    rcases hr with rfl | rfl
    · exact hbalanced a b 0 gamma
    · exact hbalanced a b 1 gamma
  · intro alpha beta r ha hb hr
    obtain ⟨a, rfl⟩ := nonzeroByte_covers alpha ha
    obtain ⟨b, rfl⟩ := nonzeroByte_covers beta hb
    rcases hr with rfl | rfl
    · exact hhomogeneous a b 0
    · exact hhomogeneous a b 1

theorem required_raw_bounds (certificate : CompleteInventory) :
    OrdinaryRawBound ∧ FourierRawBound fourierMapHom :=
  ⟨ordinary_of_cells certificate.ordinary,
    fourier_of_cells certificate.balanced certificate.homogeneous⟩

end AES8.PaperSharpEntriesInventoryAssembly
