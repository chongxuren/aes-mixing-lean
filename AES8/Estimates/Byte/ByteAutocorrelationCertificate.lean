/- Module role: Checked byte-channel resources and certificate consequences.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESMixing.ByteWalshCertificate

/-!
# Signed range of the already checked inversion Walsh lookup

This only reduces the finite predicate on the existing stored table. It
does not recompute any inversion sums or generate a new table. The table's
identity with the actual sums remains ByteWalshCertificate's existing
kernel-checked theorem. Isolating this certificate lets subsequent algebra
diagnostics reuse its object without reevaluating the finite range check.
No native_decide, new axiom or proof bypass is used.
-/
set_option autoImplicit false
namespace AES8.ByteAutocorrelationCertificate

set_option maxRecDepth 65536 in
theorem signed_lookup_all : ∀ v : Fin 256,
    (-28 : ℤ) ≤ AESMixing.AES.inversionWalshLookup (BitVec.ofFin v) ∧
      AESMixing.AES.inversionWalshLookup (BitVec.ofFin v) ≤ 32 := by
  decide

end AES8.ByteAutocorrelationCertificate
