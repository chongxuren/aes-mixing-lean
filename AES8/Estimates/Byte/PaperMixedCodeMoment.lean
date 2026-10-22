import AES8.Estimates.Byte.PaperByteGramPrinted
import AESConcrete.MixedCodeMoment

/-!
# Actual code-energy boundary from the printed Gram inequality

These wrappers replace only the finite exact moment premise by the printed
upper bound. Generic information-set, code, Fourier and diagonal arguments
remain unchanged. The legacy actual wrappers retain their historical meaning;
this leaf needs explicit downstream consumers before it changes a live HS path.
Constructive source candidate only; no attacks or historical edits.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperMixedCodeMoment
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.ByteGramCore (Byte)
open AESConcrete.ByteGramFourier
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.MixedCodeMoment

/-- Bound-bearing counterpart of the predecessor's exact moment equality. -/
theorem actual_residual_moment_le (o : Orientation) :
    (∑ ab : Byte × Byte, gram (residualMatrix (channel o) 0) ab.1 ab.2^2) ≤ byteMoment := by
  change (∑ ab : Byte × Byte, residualGram (channel o) ab.1 ab.2^2) ≤ byteMoment
  rw [Fintype.sum_prod_type]
  exact AES8.PaperByteGramPrinted.actual_gram_square_moment_le o

variable {K I J : Type*} [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
attribute [local instance] Classical.propDecidable

theorem actual_normalizedResponse_energy_le {C : Type*} [Fintype C]
    (o : K → Orientation) (coord : C → K → Byte) (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : I => coord c (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : C => fun i : I => coord c (idx (Sum.inr (Sum.inl i))))) :
    (∑ y : K → Byte, normalizedResponse (fun k => residualMatrix (channel (o k)) 0) coord y^2) ≤
      (byteMoment / 256)^Fintype.card I * byteDelta^Fintype.card J := by
  have h := normalizedResponse_energy_le_of_bijective
    (fun k => residualMatrix (channel (o k)) 0) coord idx he hf byteMoment byteDelta
    (by norm_num [byteMoment]) (by norm_num [byteDelta])
    (fun k => actual_residual_moment_le (o k)) (fun k => actual_residual_diagonal_le (o k))
  simpa only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] using h

theorem actual_subgroup_energy_le (o : K → Orientation)
    (C : AddSubgroup (K → Byte)) [Fintype C] (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : I => c.val (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : C => fun i : I => c.val (idx (Sum.inr (Sum.inl i))))) :
    (∑ y : K → Byte, action (coordinateKernel (fun k => residualMatrix (channel (o k)) 0))
      (unitSubgroupIndicator C) y^2) ≤
      (byteMoment / 256)^Fintype.card I * byteDelta^Fintype.card J := by
  rw [subgroup_response]
  exact AES8.PaperMixedCodeMoment.actual_normalizedResponse_energy_le o (fun c : C => c.val) idx he hf

theorem actual_subgroup_energy_dual_le (o : K → Orientation)
    (C : AddSubgroup (K → Byte)) [Fintype C] (idx : CodePosition I J ≃ K)
    (he : Function.Bijective (fun c : (bytePairing.product K).annihilator C =>
      fun i : I => c.val (idx (Sum.inl i))))
    (hf : Function.Bijective (fun c : (bytePairing.product K).annihilator C =>
      fun i : I => c.val (idx (Sum.inr (Sum.inl i))))) :
    (∑ y : K → Byte, action (coordinateKernel (fun k => residualMatrix (channel (o k)) 0))
      (unitSubgroupIndicator C) y^2) ≤
      (byteMoment / 256)^Fintype.card I * byteDelta^Fintype.card J := by
  have h := subgroup_energy_dual_le bytePairing BinaryWord.add_self
    (fun k => residualMatrix (channel (o k)) 0) C idx he hf byteMoment byteDelta
    (by norm_num [byteMoment]) (by norm_num [byteDelta])
    (fun k => actual_residual_moment_le (o k))
    (fun k a => by rw [actual_residual_conjugate]; exact actual_residual_diagonal_le _ a)
  simpa only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] using h

#print axioms actual_residual_moment_le
#print axioms actual_normalizedResponse_energy_le
#print axioms actual_subgroup_energy_le
#print axioms actual_subgroup_energy_dual_le
end AES8.PaperMixedCodeMoment
