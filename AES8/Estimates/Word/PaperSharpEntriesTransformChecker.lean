import AES8.Estimates.Word.PaperSharpEntriesConvolution

/-!
# Exact scaled transform-cap checker

The checker theorem consumes three independently verified interfaces: a fixed
transform correspondence, an exact trace-adjoint map, and a literal stage
transcript. It does not assert that any untested affine-map inventory is covered.
All data are untrusted; only ordinary Lean proofs discharge these interfaces.
-/

open scoped BigOperators

namespace AES8.PaperSharpEntriesTransformChecker
open AESMixing
open AES8.PaperSharpEntriesFinite
open AES8.PaperSharpEntriesFWHT
open AES8.PaperSharpEntriesConvolution

set_option autoImplicit false

theorem sign_comm (k x : Byte) : sign k x = sign x k := by
  unfold sign
  rw [AES.mul_comm]

theorem transform_byte_formula (hcoeff : CoefficientSpec)
    (f : Byte → ℤ) (gamma : Byte) :
    transform (fun i : Index => f (byteOf i)) (traceIndex gamma) =
      ∑ k : Byte, sign k gamma * f k := by
  rw [← hat_fast hcoeff f gamma]
  unfold hat
  apply Finset.sum_congr rfl
  intro k _
  rw [sign_comm]

theorem hat_of_transcript (hcoeff : CoefficientSpec) (f : Byte → ℤ)
    (stages : StageTables)
    (hinitial : checkInitial stages (fun i : Index => f (byteOf i)) = true)
    (hsteps : checkStages stages = true) (k : Byte) :
    hat f k = stageVector stages 8 (traceIndex k) := by
  have he := congrFun (transcript_transform stages _ hinitial hsteps) (traceIndex k)
  rw [← hat_fast hcoeff f k] at he
  exact he.symm

theorem correlation_output (hcoeff : CoefficientSpec)
    (f g : Byte → ℤ) (L : Byte →+ Byte) (Lt : Byte → Byte)
    (hLt : ∀ k u, sign k (L u) = sign (Lt k) u)
    (stages : StageTables)
    (hinitial : checkInitial stages (fun i : Index =>
      hat f (Lt (byteOf i)) * hat g (byteOf i)) = true)
    (hsteps : checkStages stages = true) (gamma : Byte) :
    256 * correlation f g L gamma = stageVector stages 8 (traceIndex gamma) := by
  rw [correlation_transform f g L Lt hLt gamma]
  rw [← transform_byte_formula hcoeff (fun k => hat f (Lt k) * hat g k) gamma]
  exact congrFun (transcript_transform stages _ hinitial hsteps).symm (traceIndex gamma)

def checkCaps (stages : StageTables) (cap : ℤ) : Bool :=
  decide (∀ i : Index, stageVector stages 8 i ≤ 256 * cap)

theorem correlation_le_of_transcript (hcoeff : CoefficientSpec)
    (f g : Byte → ℤ) (L : Byte →+ Byte) (Lt : Byte → Byte)
    (hLt : ∀ k u, sign k (L u) = sign (Lt k) u)
    (stages : StageTables) (cap : ℤ)
    (hinitial : checkInitial stages (fun i : Index =>
      hat f (Lt (byteOf i)) * hat g (byteOf i)) = true)
    (hsteps : checkStages stages = true) (hcaps : checkCaps stages cap = true)
    (gamma : Byte) : correlation f g L gamma ≤ cap := by
  have he := correlation_output hcoeff f g L Lt hLt stages hinitial hsteps gamma
  have hb := (of_decide_eq_true hcaps) (traceIndex gamma)
  rw [← he] at hb
  omega

def powerProfile (p : Byte → ℕ) (r : ℕ) : Byte → ℤ := fun v => (p v : ℤ)^r

def mixedMap (B : Byte →+ Byte) (alpha beta : Byte) : Byte →+ Byte where
  toFun u := alpha * B (beta * u)
  map_zero' := by simp
  map_add' u v := by simp only [mul_add, map_add]

theorem mixedSum_correlation (p : Byte → ℕ) (B : Byte →+ Byte)
    (alpha beta gamma : Byte) (r : ℕ) :
    (mixedSum p B alpha beta gamma r : ℤ) =
      correlation (powerProfile p r) (powerProfile p (5-r)) (mixedMap B alpha beta) gamma := by
  simp only [mixedSum, correlation, powerProfile, mixedMap, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

theorem mixedSum_le_of_transcript (hcoeff : CoefficientSpec)
    (p : Byte → ℕ) (B : Byte →+ Byte) (alpha beta : Byte) (r cap : ℕ)
    (Lt : Byte → Byte)
    (hLt : ∀ k u, sign k (mixedMap B alpha beta u) = sign (Lt k) u)
    (stages : StageTables)
    (hinitial : checkInitial stages (fun i : Index =>
      hat (powerProfile p r) (Lt (byteOf i)) *
        hat (powerProfile p (5-r)) (byteOf i)) = true)
    (hsteps : checkStages stages = true) (hcaps : checkCaps stages cap = true)
    (gamma : Byte) : mixedSum p B alpha beta gamma r ≤ cap := by
  have hb := correlation_le_of_transcript hcoeff (powerProfile p r)
    (powerProfile p (5-r)) (mixedMap B alpha beta) Lt hLt stages cap
    hinitial hsteps hcaps gamma
  rw [← mixedSum_correlation] at hb
  exact_mod_cast hb

/-- Cached transform values have their own exact equality proofs. The expensive
hat specification therefore does not appear in the finite initial-table check. -/
theorem mixedSum_le_of_cached_transcript (hcoeff : CoefficientSpec)
    (p : Byte → ℕ) (B : Byte →+ Byte) (alpha beta : Byte) (r cap : ℕ)
    (Lt : Byte → Byte)
    (hLt : ∀ k u, sign k (mixedMap B alpha beta u) = sign (Lt k) u)
    (F G : Byte → ℤ)
    (hF : ∀ k, hat (powerProfile p r) k = F k)
    (hG : ∀ k, hat (powerProfile p (5-r)) k = G k)
    (stages : StageTables)
    (hinitial : checkInitial stages (fun i : Index => F (Lt (byteOf i)) * G (byteOf i)) = true)
    (hsteps : checkStages stages = true) (hcaps : checkCaps stages cap = true)
    (gamma : Byte) : mixedSum p B alpha beta gamma r ≤ cap := by
  have hi : checkInitial stages (fun i : Index =>
      hat (powerProfile p r) (Lt (byteOf i)) *
        hat (powerProfile p (5-r)) (byteOf i)) = true := by
    have he := of_decide_eq_true hinitial
    simp only [checkInitial, decide_eq_true_eq]
    intro i
    rw [hF, hG]
    exact he i
  exact mixedSum_le_of_transcript hcoeff p B alpha beta r cap Lt hLt
    stages hi hsteps hcaps gamma

end AES8.PaperSharpEntriesTransformChecker
