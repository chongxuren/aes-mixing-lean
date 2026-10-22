import AES8.Reductions.Return.ReturnCentering

/-!
# Complete centered memory identity, including the two-round source

Module role: an exact index and centering adapter for the paper's memory
identity. No norm, support-block estimate, profile recurrence or final mixing
bound is asserted. Constructive proofs only; no attacks or manuscript edits.

`AESPaper.GroupedLaw.groupedLaw n a` is defined using the physical difference
law after `2 * n + 2` AES rounds, in the fixed output coordinates. Thus
`error n a`, `error (n + 1) a`, `error (n + 2) a` correspond respectively to
paper errors at `r`, `r + 2`, `r + 4`, where `r = 2 * n + 2`. Naturals `n`
cover exactly the even paper source-round counts `r >= 2`; in particular,
`n = 0` is the paper endpoint `r = 2`.

The older `TransferAssembly.centered_actual_memory j` substitutes `n = j + 1`
and therefore starts at physical `r = 4`. This leaf leaves that declaration
unchanged and exposes the complete range of `SupportEvolution.error_memory`.
The high-return centering cancellation is valid for every signed joint input
by `ReturnCentering.highReturn_eq_uncentered`; only the low error term uses
the actual error's zero extension and zero total mass.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.PaperMemoryIdentity
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (error)
open AESPaper.GroupedRecurrence (step)
open AES8.SupportEvolution (lowPart highPart)
open AES8.TransferAssembly (centeredStep highReturn)

/-- The paper memory identity for every grouped source index, including zero.
Under `r = 2 * n + 2`, this is exactly the even-round range `r >= 2`. -/
theorem centered_error_memory (n : ℕ) (a : AES.State) (ha : a ≠ 0) :
    error (n + 2) a = centeredStep (lowPart (error (n + 1) a)) +
      highReturn (error n a) := by
  calc
    error (n + 2) a = step (lowPart (error (n + 1) a)) +
        step (highPart (step (error n a))) :=
      SupportEvolution.error_memory n a ha
    _ = centeredStep (lowPart (error (n + 1) a)) + highReturn (error n a) := by
      rw [TransferAssembly.centeredStep_low_eq_step _
        (AESPaper.GroupedLaw.error_zero _ a ha)
        (AESPaper.GroupedLaw.error_sum _ a), ReturnCentering.highReturn_eq_uncentered]

/-- The previously unexposed paper endpoint: physical rounds 2, 4, and 6. -/
theorem centered_error_memory_two_rounds (a : AES.State) (ha : a ≠ 0) :
    error 2 a = centeredStep (lowPart (error 1 a)) + highReturn (error 0 a) := by
  simpa only [Nat.zero_add] using centered_error_memory 0 a ha

end AES8.PaperMemoryIdentity
