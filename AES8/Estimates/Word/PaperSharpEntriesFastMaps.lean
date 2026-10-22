import AES8.Estimates.Word.PaperSharpEntriesKernelTables
import AES8.Estimates.Word.PaperSharpEntriesMapAdjoints

namespace AES8.PaperSharpEntriesFastMaps
open AESMixing AES8.PaperSharpEntriesFinite AES8.PaperSharpEntriesFWHT
open AES8.PaperSharpEntriesKernelTables AES8.PaperSharpEntriesMapAdjoints
set_option maxRecDepth 65536
set_option maxHeartbeats 80000000
def ordinaryAdjointTable : Array ℕ := #[30,110,60,152,203,223,23,156]
def ordinaryAdjointBasis (i : Fin 8) : Byte := ⟨BitVec.ofNat 8 ordinaryAdjointTable[i.val]!⟩
def ordinaryAdjointFast : Byte →+ Byte := linearFromBasis ordinaryAdjointBasis
def fourierFast : Byte →+ Byte := linearFromBasis adjointFast
theorem fourierFast_spec (v : Byte) : fourierFast v = fourierMapHom v := by
  have he : adjointFast = adjointBasis := funext adjointFast_spec
  rw [fourierFast, he]
  rfl
theorem inverse_identity : fourierFast.comp ordinaryAdjointFast = AddMonoidHom.id Byte := by
  apply AES.byte_addHom_ext
  intro i
  fin_cases i <;> decide +kernel
theorem ordinaryAdjointFast_spec (k : Byte) : fourierMapHom (ordinaryAdjointFast k) = k := by
  rw [← fourierFast_spec]
  exact DFunLike.congr_fun inverse_identity k
theorem qFast_eq (v : Byte) : qFast v = q v := by
  have hv : byteOf v.bits.toFin = v := by cases v; rfl
  simpa only [hv] using qFast_spec v.bits.toFin
theorem hFast_eq (v : Byte) : hFast v = h v := by
  have hv : byteOf v.bits.toFin = v := by cases v; rfl
  simpa only [hv] using hFast_spec v.bits.toFin
theorem traceFast_eq (v : Byte) : traceFast v = traceIndex v := by
  have hv : byteOf v.bits.toFin = v := by cases v; rfl
  simpa only [hv] using traceFast_spec v.bits.toFin
end AES8.PaperSharpEntriesFastMaps
