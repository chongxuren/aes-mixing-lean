import AESMixing.MDSInterpolation

/-! Exhaustive proofs about the sixteen subsets of four coordinate positions.
These certificates concern only subset selection and cardinality, not AES values. -/
namespace AESMixing
open AES

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem low_mask_extension : ∀ r z : Fin 16,
    maskSize r + maskSize z ≤ 4 → ∃ c : Fin 16,
      maskSize r = maskSize c ∧
      (∀ i : Fin 4, maskBit z i = true → maskBit c i ≠ true) := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem high_mask_restriction : ∀ r z : Fin 16,
    4 ≤ maskSize r + maskSize z → ∃ r' c : Fin 16,
      maskSize r' = maskSize c ∧
      (∀ i : Fin 4, maskBit r' i = true → maskBit r i = true) ∧
      (∀ i : Fin 4, maskBit c i ≠ true → maskBit z i = true) := by
  decide

end AESMixing
