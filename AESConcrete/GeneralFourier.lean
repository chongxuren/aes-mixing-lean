import AESConcrete.OrdinaryGraph
import AESConcrete.GeneralFourierGraphEnergy
import AESConcrete.MultiUniformExpansion

/-! Public extension: arbitrary-mask Fourier graph energy for the
actual AES residual tensor, plus exact normalized multi-uniform expansion.
The inherited 142 step caps and local return (13,13) remain available.
No new step cap follows without applying the expansion and proving its exact
scalar comparison. The full 10/14/16 theorem, remaining caps, initialization,
experiment linkage and ordered-pair TV lifting remain open.
Constructive mathematics only; no attacks or manuscript edits. -/
