import AESConcrete.ByteFifthMoments
import AESConcrete.ByteGramFourier

/-!
# Fixed finite interfaces for sharp AES entry certificates

Draft source only until a source-bound formal-node diagnostic is retained.
The integer profiles are tied to the already certified ordinary inversion row
and Walsh lookup.  These definitions specify the finite obligation; they do not
assert that its 65,025 nonzero affine maps have been checked.

Constructive mathematics only. No attacks, numerical search, manuscript edits,
custom axioms, native evaluation oracle, or modifications of imported sources.
-/

open scoped BigOperators

namespace AES8.PaperSharpEntriesFinite
open AESMixing

abbrev Byte := BinaryWord 8

set_option autoImplicit false
set_option maxRecDepth 65536

/-- Half the exact ordinary inversion DDT row count. -/
def q (v : Byte) : ℕ := AES.inversionProfile v.bits / 2

/-- Squared quarter-Walsh profile. `natAbs` avoids signed division conventions. -/
def h (v : Byte) : ℕ := (AES.inversionWalshLookup v.bits).natAbs ^ 2 / 16

/-- Computable actual inverse AES affine-linear map, before adding any constant. -/
def ordinaryMapHom : Byte →+ Byte := AES.invAffineLinear

noncomputable def ordinaryMap : Byte ≃+ Byte := AES.affineLinearEquiv.symm

theorem ordinaryMap_apply (v : Byte) : ordinaryMap v = ordinaryMapHom v := by
  have hi := AES.affineLinear_left_inverse (AES.affineLinearEquiv.symm v)
  change AES.invAffineLinear (AES.affineLinearEquiv (AES.affineLinearEquiv.symm v)) =
    AES.affineLinearEquiv.symm v at hi
  rw [AddEquiv.apply_symm_apply] at hi
  exact hi.symm

/-- Actual trace-pairing adjoint, kept distinct from the ordinary bit transpose.
The separately checked computable byte implementation must be proved equal to
this semantic map before a finite certificate can be used by the entry proof. -/
noncomputable def fourierMap : Byte ≃+ Byte :=
  AESConcrete.ByteGramFourier.byteDualAddEquiv AES.affineLinearEquiv

noncomputable def rhoOrd (v : Byte) : ℝ := (q v : ℝ) / 128
noncomputable def rhoFourier (v : Byte) : ℝ := (h v : ℝ) / 4096

theorem q_twice (v : Byte) : 2 * q v = AES.inversionProfile v.bits := by
  unfold q AES.inversionProfile
  split_ifs <;> norm_num

set_option maxHeartbeats 8000000 in
theorem h_times_sixteen_fin (v : Fin 256) :
    (16 : ℤ) * (h (⟨BitVec.ofFin v⟩ : Byte) : ℤ) =
      AES.inversionWalshLookup (BitVec.ofFin v) ^ 2 := by
  fin_cases v <;> decide

theorem h_times_sixteen (v : Byte) :
    (16 : ℤ) * (h v : ℤ) = AES.inversionWalshLookup v.bits ^ 2 :=
  h_times_sixteen_fin v.bits.toFin

theorem rhoOrd_spec (v : Byte) :
    rhoOrd v = differenceChannel invPermutation v 1 := by
  rw [inversion_row_one_profile]
  have hq : (2 : ℝ) * (q v : ℝ) = (AES.inversionProfile v.bits : ℝ) := by
    exact_mod_cast q_twice v
  unfold rhoOrd
  rw [← hq]
  ring

theorem rhoFourier_spec (v : Byte) :
    rhoFourier v = fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ^ 2 / 65536 := by
  rw [byte_walsh_one_lookup]
  have hh : (16 : ℝ) * (h v : ℝ) = (AES.inversionWalshLookup v.bits : ℝ)^2 := by
    exact_mod_cast h_times_sixteen v
  unfold rhoFourier
  rw [← hh]
  ring

/-- Fixed integer mixed moment. The second exponent is the complement to five.
Keeping this specification independent of the checker avoids trusting generated
tables or a transform implementation. -/
def mixedSum (profile : Byte → ℕ) (B : Byte → Byte)
    (alpha beta gamma : Byte) (r : ℕ) : ℕ :=
  ∑ u : Byte, profile u ^ r * profile (alpha * B (beta * u) + gamma) ^ (5 - r)

theorem normalized_mixed_sum (profile : Byte → ℕ) (B : Byte → Byte)
    (alpha beta gamma : Byte) (r : ℕ) (hr : r ≤ 5) (d : ℝ) :
    (∑ u : Byte, ((profile u : ℝ) / d)^r *
      ((profile (alpha * B (beta * u) + gamma) : ℝ) / d)^(5-r)) =
        (mixedSum profile B alpha beta gamma r : ℝ) / d^5 := by
  have hpow : d^r * d^(5-r) = d^5 := by
    rw [← pow_add, Nat.add_sub_of_le hr]
  calc
    _ = ∑ u : Byte, ((profile u : ℝ)^r *
        (profile (alpha * B (beta * u) + gamma) : ℝ)^(5-r)) / d^5 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [div_pow, div_pow, div_mul_div_comm, hpow]
    _ = _ := by
      rw [← Finset.sum_div]
      congr 1
      simp only [mixedSum, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

theorem ordinary_normalization (alpha beta gamma : Byte) (r : ℕ) (hr : r ≤ 5) :
    (∑ u : Byte, rhoOrd u ^ r *
      rhoOrd (alpha * ordinaryMap (beta * u) + gamma)^(5-r)) =
        (mixedSum q ordinaryMapHom alpha beta gamma r : ℝ) / 2^35 := by
  have hd : (128 : ℝ)^5 = 2^35 := by norm_num
  simpa only [rhoOrd, ordinaryMap_apply, hd] using
    normalized_mixed_sum q ordinaryMapHom alpha beta gamma r hr 128

theorem fourier_normalization (B : Byte → Byte)
    (alpha beta gamma : Byte) (r : ℕ) (hr : r ≤ 5) :
    (∑ u : Byte, rhoFourier u ^ r *
      rhoFourier (alpha * B (beta * u) + gamma)^(5-r)) =
        (mixedSum h B alpha beta gamma r : ℝ) / 2^60 := by
  have hd : (4096 : ℝ)^5 = 2^60 := by norm_num
  simpa only [rhoFourier, hd] using
    normalized_mixed_sum h B alpha beta gamma r hr 4096

theorem ordinary_cap_lt_fourteen : (111 : ℝ) / 2^35 < 14 / 2^32 := by norm_num
theorem fourier_cap_lt_twenty_seven :
    (7247757311 : ℝ) / 2^60 < 27 / 2^32 := by norm_num

def OrdinaryRawBound : Prop :=
  ∀ (alpha beta gamma : Byte) (r : ℕ), alpha ≠ 0 → beta ≠ 0 →
    1 ≤ r → r ≤ 4 → mixedSum q ordinaryMapHom alpha beta gamma r ≤ 111

def FourierRawBound (B : Byte → Byte) : Prop :=
  (∀ (alpha beta gamma : Byte) (r : ℕ), alpha ≠ 0 → beta ≠ 0 →
    (r = 2 ∨ r = 3) → mixedSum h B alpha beta gamma r ≤ 7247757311) ∧
  (∀ (alpha beta : Byte) (r : ℕ), alpha ≠ 0 → beta ≠ 0 →
    (r = 1 ∨ r = 4) → mixedSum h B alpha beta 0 r ≤ 7247757311)

/-- The two masks are nonzero by construction, rather than by a condition in
the expensive arithmetic loop. -/
def nonzeroByte (i : Fin 255) : Byte := ⟨BitVec.ofNat 8 (i.val + 1)⟩

theorem nonzeroByte_ne_zero (i : Fin 255) : nonzeroByte i ≠ 0 := by
  intro hi
  have he := congrArg (fun v : Byte => v.bits.toNat) hi
  simp only [nonzeroByte, BitVec.toNat_ofNat, Nat.reducePow,
    show (0 : Byte).bits.toNat = 0 by rfl] at he
  rw [Nat.mod_eq_of_lt (by omega)] at he
  omega

theorem nonzeroByte_covers (v : Byte) (hv : v ≠ 0) :
    ∃ i : Fin 255, nonzeroByte i = v := by
  have hupper : v.bits.toNat < 256 := v.bits.isLt
  have hpos : 0 < v.bits.toNat := by
    by_contra h
    have hz : v.bits.toNat = 0 := by omega
    apply hv
    apply BinaryWord.ext
    exact BitVec.eq_of_toNat_eq hz
  let i : Fin 255 := ⟨v.bits.toNat-1, by omega⟩
  refine ⟨i, ?_⟩
  apply BinaryWord.ext
  apply BitVec.eq_of_toNat_eq
  simp only [nonzeroByte, BitVec.toNat_ofNat, Nat.reducePow]
  dsimp only [i]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Kernel-checkable direct fixture: checking one nonzero alpha and beta for
the entire translation inventory. This is deliberately not the production
checker; it measures the direct baseline against the transform checker. -/
def checkDirectMap (profile : Byte → ℕ) (B : Byte → Byte)
    (alpha beta : Fin 255) (r cap : ℕ) : Bool :=
  decide (∀ gamma : Byte,
    mixedSum profile B (nonzeroByte alpha) (nonzeroByte beta) gamma r ≤ cap)

theorem checkDirectMap_sound (profile : Byte → ℕ) (B : Byte → Byte)
    (alpha beta : Fin 255) (r cap : ℕ)
    (hc : checkDirectMap profile B alpha beta r cap = true) (gamma : Byte) :
    mixedSum profile B (nonzeroByte alpha) (nonzeroByte beta) gamma r ≤ cap := by
  exact (of_decide_eq_true hc) gamma

end AES8.PaperSharpEntriesFinite
