import AES8.Estimates.Word.PaperSharpEntriesPackedAllPowers
import AES8.Estimates.Word.PaperSharpEntriesVectorChecker

/-! Shared semantic closure for packed numerical transcript leaves. Numerical
data, checks and quantified inventory assembly have separate ownership. -/
namespace AES8.PaperSharpEntriesPackedEntryChecker
open AES8.PaperSharpEntriesFinite AES8.PaperSharpEntriesFWHT
open AES8.PaperSharpEntriesKernelTables AES8.PaperSharpEntriesFastMaps
open AES8.PaperSharpEntriesMapAdjoints AES8.PaperSharpEntriesTransformChecker
open AES8.PaperSharpEntriesPackedAllPowers AES8.PaperSharpEntriesConvolution
set_option autoImplicit false

noncomputable def qPower (r : ℕ) : Byte → ℤ := match r with
  | 1 => q1Fast | 2 => q2Fast | 3 => q3Fast | 4 => q4Fast | _ => fun _ => 0
noncomputable def hPower (r : ℕ) : Byte → ℤ := match r with
  | 1 => h1Fast | 2 => h2Fast | 3 => h3Fast | 4 => h4Fast | _ => fun _ => 0

theorem qPower_hat (hcoeff : CoefficientSpec) (r : ℕ) (hlo : 1 ≤ r) (hhi : r ≤ 4)
    (k : Byte) : hat (powerProfile qFast r) k = qPower r k := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr with rfl | rfl | rfl | rfl
  · exact q1_fast_hat hcoeff k
  · exact q2_fast_hat hcoeff k
  · exact q3_fast_hat hcoeff k
  · exact q4_fast_hat hcoeff k

theorem hPower_hat (hcoeff : CoefficientSpec) (r : ℕ) (hlo : 1 ≤ r) (hhi : r ≤ 4)
    (k : Byte) : hat (powerProfile hFast r) k = hPower r k := by
  have hr : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases hr with rfl | rfl | rfl | rfl
  · exact h1_fast_hat hcoeff k
  · exact h2_fast_hat hcoeff k
  · exact h3_fast_hat hcoeff k
  · exact h4_fast_hat hcoeff k

def ordinaryLt (alpha beta : Byte) : Byte → Byte :=
  mixedAdjoint ordinaryAdjointFast alpha beta
def fourierLt (alpha beta : Byte) : Byte → Byte :=
  mixedAdjoint AESMixing.AES.affineLinear alpha beta
noncomputable def ordinaryInitial (alpha beta : Byte) (r : ℕ) : Vector :=
  fun i => qPower r (ordinaryLt alpha beta (byteOf i)) * qPower (5-r) (byteOf i)
noncomputable def fourierInitial (alpha beta : Byte) (r : ℕ) : Vector :=
  fun i => hPower r (fourierLt alpha beta (byteOf i)) * hPower (5-r) (byteOf i)

theorem ordinary_cap (hcoeff : CoefficientSpec) (alpha beta : Byte) (r : ℕ)
    (hlo : 1 ≤ r) (hhi : r ≤ 4) (stages : PaperSharpEntriesVectorChecker.VectorStages)
    (hi : PaperSharpEntriesVectorChecker.checkInitial stages (ordinaryInitial alpha beta r) = true)
    (hs : ∀ s, PaperSharpEntriesVectorChecker.checkStage stages s = true)
    (hc : PaperSharpEntriesVectorChecker.checkCaps stages 111 = true) (gamma : Byte) :
    mixedSum q ordinaryMapHom alpha beta gamma r ≤ 111 := by
  have hC := ordinary_adjoint_sign ordinaryAdjointFast ordinaryAdjointFast_spec
  have hLt := mixed_adjoint_sign ordinaryMapHom ordinaryAdjointFast hC alpha beta
  have hb := mixedSum_le_of_cached_transcript hcoeff qFast ordinaryMapHom alpha beta r 111
    (ordinaryLt alpha beta) hLt (qPower r) (qPower (5-r))
    (qPower_hat hcoeff r hlo hhi) (qPower_hat hcoeff (5-r) (by omega) (by omega))
    (PaperSharpEntriesVectorChecker.encode stages)
    (PaperSharpEntriesVectorChecker.initial_sound _ _ hi)
    (PaperSharpEntriesVectorChecker.stages_sound _ hs)
    (PaperSharpEntriesVectorChecker.caps_sound _ _ hc) gamma
  have hp : qFast = q := funext qFast_eq
  rw [hp] at hb
  exact hb

theorem fourier_cap (hcoeff : CoefficientSpec) (alpha beta : Byte) (r : ℕ)
    (hlo : 1 ≤ r) (hhi : r ≤ 4) (stages : PaperSharpEntriesVectorChecker.VectorStages)
    (hi : PaperSharpEntriesVectorChecker.checkInitial stages (fourierInitial alpha beta r) = true)
    (hs : ∀ s, PaperSharpEntriesVectorChecker.checkStage stages s = true)
    (hc : PaperSharpEntriesVectorChecker.checkCaps stages 7247757311 = true) (gamma : Byte) :
    mixedSum h fourierMapHom alpha beta gamma r ≤ 7247757311 := by
  have hC : ∀ k u, sign k (fourierFast u) = sign (AESMixing.AES.affineLinear k) u := by
    intro k u
    simpa only [fourierFast_spec] using fourier_adjoint_sign k u
  have hLt := mixed_adjoint_sign fourierFast AESMixing.AES.affineLinear hC alpha beta
  have hb := mixedSum_le_of_cached_transcript hcoeff hFast fourierFast alpha beta r 7247757311
    (fourierLt alpha beta) hLt (hPower r) (hPower (5-r))
    (hPower_hat hcoeff r hlo hhi) (hPower_hat hcoeff (5-r) (by omega) (by omega))
    (PaperSharpEntriesVectorChecker.encode stages)
    (PaperSharpEntriesVectorChecker.initial_sound _ _ hi)
    (PaperSharpEntriesVectorChecker.stages_sound _ hs)
    (PaperSharpEntriesVectorChecker.caps_sound _ _ hc) gamma
  have hp : hFast = h := funext hFast_eq
  have hB : (fourierFast : Byte → Byte) = fourierMapHom := funext fourierFast_spec
  rw [hp, hB] at hb
  exact hb

end AES8.PaperSharpEntriesPackedEntryChecker
