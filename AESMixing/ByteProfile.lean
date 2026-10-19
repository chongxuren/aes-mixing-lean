import AESMixing.ByteCertificate

/-! Exact ordinary-DDT profile of the inversion byte. Only the one-row
certificate is enumerated; field scaling supplies all other nonzero columns. -/
namespace AESMixing.AES
open scoped BigOperators

def inversionProfile (b : Byte) : ℕ :=
  if b = 0 then 0 else
    (if traceBit (invLookup b) then 0 else 2) + (if b = 1 then 2 else 0)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem inversion_profile_correct (b : Byte) : inversionRowOneCount b = inversionProfile b := by
  by_cases hb : b = 0
  · subst b
    have h : inversionRowOneCount (0#8) = 0 := by decide
    change inversionRowOneCount (0#8) = 0
    exact h
  · have hfin : b.toFin ≠ 0 := by
      intro h
      apply hb
      exact congrArg BitVec.ofFin h
    have h := inversion_row_one_certificate b.toFin hfin
    have hone : b.toFin = 1 ↔ b = 1 := by
      constructor
      · intro he; exact congrArg BitVec.ofFin he
      · rintro rfl; rfl
    simpa only [inversionProfile, if_neg hb, hone] using h

theorem inversion_profile_bound (b : Byte) : inversionProfile b ≤ 4 := by
  unfold inversionProfile
  split_ifs <;> norm_num

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem inversion_profile_square_sum :
    (∑ b : Fin 256, inversionProfile (BitVec.ofFin b)^2) = 520 := by decide

end AESMixing.AES
