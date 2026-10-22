import AES8.Estimates.Word.PaperSharpEntriesFinite

/-!
# Computable trace-adjoint byte map and semantic binding

Draft only. The eight candidate images are found by a bounded search through
bytes. Only their 64 basis-pair equations need kernel evaluation. Additivity
then proves the trace-pairing equation on every byte pair. This is an exact
definition, not a numerical search for an improved constant or construction.
The production checker may replace the bounded search by a literal eight-item
lookup only after proving its equality to these candidate images.

Constructive mathematics only; no attacks or imported-source changes.
-/

open scoped BigOperators

namespace AES8.PaperSharpEntriesFinite
open AESMixing

set_option autoImplicit false
set_option maxRecDepth 65536

/-- Build an additive byte map from its eight binary basis images. -/
def linearFromBasis (image : Fin 8 → Byte) : Byte →+ Byte where
  toFun v := ∑ i : Fin 8, if v.bits.getLsbD i.val then image i else 0
  map_zero' := by
    change (∑ i : Fin 8, if (0#8).getLsbD i.val then image i else 0) = 0
    simp
  map_add' v w := by
    simp only [BinaryWord.add_bits, BitVec.getLsbD_xor]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases hv : v.bits.getLsbD i.val <;> cases hw : w.bits.getLsbD i.val <;>
      simp [hv, hw, BinaryWord.add_self]

theorem basis_bit (i j : Fin 8) :
    (AES.byteBasis i).bits.getLsbD j.val = decide (i = j) := by
  fin_cases i <;> fin_cases j <;> decide

theorem linearFromBasis_basis (image : Fin 8 → Byte) (i : Fin 8) :
    linearFromBasis image (AES.byteBasis i) = image i := by
  change (∑ j : Fin 8, if (AES.byteBasis i).bits.getLsbD j.val then image j else 0) = _
  simp only [basis_bit, decide_eq_true_eq]
  simp

/-- A fully bounded candidate. The mathematical guarantee is supplied by
`adjointBasis_trace` below and does not assume search success. -/
def adjointBasis (i : Fin 8) : Byte :=
  ⟨BitVec.ofFin (((List.finRange 256).find? (fun w : Fin 256 =>
    decide (∀ j : Fin 8,
      AES.traceBit (AES.mul (AES.byteBasis i).bits
        (AES.affineLinearByte (AES.byteBasis j).bits)) =
      AES.traceBit (AES.mul (BitVec.ofFin w) (AES.byteBasis j).bits)))).getD 0)⟩

set_option maxHeartbeats 80000000 in
theorem adjointBasis_trace (i j : Fin 8) :
    AES.traceBit (AES.mul (AES.byteBasis i).bits
      (AES.affineLinearByte (AES.byteBasis j).bits)) =
    AES.traceBit (AES.mul (adjointBasis i).bits (AES.byteBasis j).bits) := by
  fin_cases i <;> fin_cases j <;> decide

def fourierMapHom : Byte →+ Byte := linearFromBasis adjointBasis

private theorem character_sum {I : Type*} (s : Finset I) (f : I → Byte) :
    byteCharacter (∑ i ∈ s, f i) = ∏ i ∈ s, byteCharacter (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [byteCharacter_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, byteCharacter_add, ih]

private theorem character_agree_basis (f g : Byte →+ Byte)
    (hfg : ∀ i : Fin 8, byteCharacter (f (AES.byteBasis i)) =
      byteCharacter (g (AES.byteBasis i))) (x : Byte) :
    byteCharacter (f x) = byteCharacter (g x) := by
  rw [AES.byte_basis_decomposition x, map_sum, map_sum]
  rw [character_sum, character_sum]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp [hfg]

private def mulRightHom (c : Byte) : Byte →+ Byte where
  toFun v := v * c
  map_zero' := zero_mul c
  map_add' v w := add_mul v w c

private def mulLeftHom (c : Byte) : Byte →+ Byte where
  toFun v := c * v
  map_zero' := mul_zero c
  map_add' v w := mul_add c v w

private theorem fourierMap_basis_character (v : Byte) (j : Fin 8) :
    byteCharacter (v * AES.affineLinearEquiv (AES.byteBasis j)) =
      byteCharacter (fourierMapHom v * AES.byteBasis j) := by
  apply character_agree_basis
    (mulRightHom (AES.affineLinearEquiv (AES.byteBasis j)))
    ((mulRightHom (AES.byteBasis j)).comp fourierMapHom) ?_ v
  intro i
  change byteCharacter (AES.byteBasis i * AES.affineLinearEquiv (AES.byteBasis j)) =
    byteCharacter (fourierMapHom (AES.byteBasis i) * AES.byteBasis j)
  rw [show fourierMapHom (AES.byteBasis i) = adjointBasis i from
    linearFromBasis_basis adjointBasis i]
  unfold byteCharacter
  change (if AES.traceBit (AES.mul (AES.byteBasis i).bits
      (AES.affineLinearByte (AES.byteBasis j).bits)) then (-1 : ℝ) else 1) = _
  rw [adjointBasis_trace]
  rfl

theorem fourierMapHom_character (v x : Byte) :
    byteCharacter (v * AES.affineLinearEquiv x) =
      byteCharacter (fourierMapHom v * x) := by
  exact character_agree_basis
    ((mulLeftHom v).comp AES.affineLinearEquiv.toAddMonoidHom)
    (mulLeftHom (fourierMapHom v)) (fourierMap_basis_character v) x

theorem fourierMap_apply (v : Byte) : fourierMap v = fourierMapHom v := by
  apply byte_character_index_unique
  intro x
  change byteCharacter (byteDualEquiv AES.affineLinearEquiv v * x) = _
  rw [← AESConcrete.ByteGramFourier.dual_spec]
  exact fourierMapHom_character v x

end AES8.PaperSharpEntriesFinite
