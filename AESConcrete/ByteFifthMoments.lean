import AESConcrete.ByteFifthFinite
import AESConcrete.ByteOrientations

/-!
# Exact fifth moments of the four actual AES byte channels

The ordinary DDT profile gives fifth sum 5056 before division by 256^5.
The already verified inversion Walsh lookup gives tenth sum
48193441*2^28 before division by 65536^5. Actual field scaling and AES
affine/dual relabelings transport these statements to every nonzero row
and column. Zero labels are excluded: their full-channel fifth moment
is one. No word-entry bound or whole-word Fourier identification follows
from this module alone. Constructive mathematics only; no attacks,
manuscript changes or edits to frozen and historical sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ByteFifthMoments
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel)

abbrev Byte := BinaryWord 8
set_option maxRecDepth 65536

def ddtMoment : ℝ := 79 / (4*(2 : ℝ)^32)
def walshMoment : ℝ := 48193441 / (2 : ℝ)^52

def moment : Orientation → ℝ
  | .ordinary => ddtMoment
  | .transposed => ddtMoment
  | .fourier => walshMoment
  | .fourierTransposed => walshMoment

def uniformH : ℝ := walshMoment

theorem inversion_row_one_fifth :
    (∑ b : Byte, differenceChannel invPermutation b 1 ^ 5) = ddtMoment := by
  have he := Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun b : Byte => (AES.inversionProfile b.bits : ℝ)^5)
  have hp : (∑ b : Byte, (AES.inversionProfile b.bits : ℝ)^5) = 5056 := by
    rw [← he]
    exact_mod_cast ByteFifthFinite.inversion_profile_fifth_sum
  simp_rw [inversion_row_one_profile,div_pow]
  rw [← Finset.sum_div,hp]
  norm_num [ddtMoment]

theorem inversion_column_fifth (a : Byte) (ha : a ≠ 0) :
    (∑ b : Byte, differenceChannel invPermutation b a ^ 5) = ddtMoment := by
  simp_rw [inversion_channel_scale a _ ha]
  have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha)
    (fun b => differenceChannel invPermutation b 1 ^ 5)
  change (∑ b, differenceChannel invPermutation (a*b) 1 ^ 5) = _ at he
  rw [he,inversion_row_one_fifth]

theorem aes_column_fifth (a : Byte) (ha : a ≠ 0) :
    (∑ b : Byte, aesByteChannel b a ^ 5) = ddtMoment := by
  simp_rw [aesByteChannel_affine]
  have he := Equiv.sum_comp AES.affineLinearEquiv.symm.toEquiv
    (fun b => differenceChannel invPermutation b a ^ 5)
  change (∑ b, differenceChannel invPermutation (AES.affineLinearEquiv.symm b) a ^ 5) = _ at he
  rw [he,inversion_column_fifth a ha]

theorem aes_row_fifth (b : Byte) (hb : b ≠ 0) :
    (∑ a : Byte, aesByteChannel b a ^ 5) = ddtMoment := by
  have hne : AES.affineLinearEquiv.symm b ≠ 0 := by
    intro h
    apply hb
    have he := congrArg AES.affineLinearEquiv h
    simpa only [AES.affineLinearEquiv.apply_symm_apply,map_zero] using he
  simp_rw [aesByteChannel_affine,inversion_channel_symmetric]
  exact inversion_column_fifth _ hne

theorem inversion_walsh_one_tenth :
    (∑ v : Byte, fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ^ 10) =
      (48193441 : ℝ)*2^28 := by
  simp_rw [byte_walsh_one_lookup]
  rw [← Equiv.sum_comp (BinaryWord.equivFin 8).symm
    (fun v : Byte => (AES.inversionWalshLookup v.bits : ℝ)^10)]
  exact_mod_cast ByteFifthFinite.inversion_walsh_tenth_sum

theorem inversion_walsh_tenth (u : Byte) (hu : u ≠ 0) :
    (∑ v : Byte, fieldWalsh byteCharacter (fun x => x⁻¹) u v ^ 10) =
      (48193441 : ℝ)*2^28 := by
  simp_rw [inversion_walsh_scale byteCharacter u _ hu]
  have he := Equiv.sum_comp (Equiv.mulLeft₀ u hu)
    (fun v => fieldWalsh byteCharacter (fun x => x⁻¹) 1 v ^ 10)
  change (∑ v, fieldWalsh byteCharacter (fun x => x⁻¹) 1 (u*v) ^ 10) = _ at he
  rw [he,inversion_walsh_one_tenth]

/-- Even powers remove the AES affine-output character sign; the actual
dual relabeling of the Walsh output label is retained. -/
theorem aes_walsh_tenth (u v : Byte) :
    fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 10 =
      fieldWalsh byteCharacter (fun x => x⁻¹) u (byteDualEquiv AES.affineLinearEquiv v) ^ 10 := by
  calc
    _ = (fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 2)^5 := by ring
    _ = _ := by rw [aes_walsh_square]; ring

theorem aes_walsh_tenth_column (u : Byte) (hu : u ≠ 0) :
    (∑ v : Byte, fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 10) =
      (48193441 : ℝ)*2^28 := by
  simp_rw [aes_walsh_tenth]
  rw [Equiv.sum_comp (byteDualEquiv AES.affineLinearEquiv)
    (fun v => fieldWalsh byteCharacter (fun x => x⁻¹) u v ^ 10)]
  exact inversion_walsh_tenth u hu

theorem aes_walsh_tenth_row (v : Byte) (hv : v ≠ 0) :
    (∑ u : Byte, fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 10) =
      (48193441 : ℝ)*2^28 := by
  calc
    _ = ∑ u : Byte, fieldWalsh byteCharacter (fun x => x⁻¹)
        (byteDualEquiv AES.affineLinearEquiv v) u ^ 10 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [aes_walsh_tenth,inversion_walsh_symmetric byteCharacter u
        (byteDualEquiv AES.affineLinearEquiv v)]
    _ = _ := inversion_walsh_tenth _ (byteDualEquiv_ne_zero _ v hv)

theorem squared_walsh_column_fifth (u : Byte) (hu : u ≠ 0) :
    (∑ v : Byte, aesSquaredWalshChannel v u ^ 5) = walshMoment := by
  have hp (v : Byte) : aesSquaredWalshChannel v u ^ 5 =
      fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 10 / 65536^5 := by
    unfold aesSquaredWalshChannel
    ring
  simp_rw [hp]
  rw [← Finset.sum_div,aes_walsh_tenth_column u hu]
  norm_num [walshMoment]

theorem squared_walsh_row_fifth (v : Byte) (hv : v ≠ 0) :
    (∑ u : Byte, aesSquaredWalshChannel v u ^ 5) = walshMoment := by
  have hp (u : Byte) : aesSquaredWalshChannel v u ^ 5 =
      fieldWalsh byteCharacter BinaryWord.sboxPerm u v ^ 10 / 65536^5 := by
    unfold aesSquaredWalshChannel
    ring
  simp_rw [hp]
  rw [← Finset.sum_div,aes_walsh_tenth_row v hv]
  norm_num [walshMoment]

/-- Exact nonzero-column fifth moment for each of the four actual byte
orientations. The transpose cases use actual row moments. -/
theorem actual_column_fifth (o : Orientation) (a : Byte) (ha : a ≠ 0) :
    (∑ b : Byte, channel o b a ^ 5) = moment o := by
  cases o
  · exact aes_column_fifth a ha
  · exact aes_row_fifth a ha
  · exact squared_walsh_column_fifth a ha
  · exact squared_walsh_row_fifth a ha

theorem actual_row_fifth (o : Orientation) (b : Byte) (hb : b ≠ 0) :
    (∑ a : Byte, channel o b a ^ 5) = moment o := by
  cases o
  · exact aes_row_fifth b hb
  · exact aes_column_fifth b hb
  · exact squared_walsh_row_fifth b hb
  · exact squared_walsh_column_fifth b hb

theorem uniformH_pos : 0 < uniformH := by
  norm_num [uniformH,walshMoment]

theorem moment_le_uniform (o : Orientation) : moment o ≤ uniformH := by
  cases o <;> norm_num [moment,uniformH,ddtMoment,walshMoment]

theorem uniformH_lt_target : uniformH < 46/(2 : ℝ)^32 := by
  norm_num [uniformH,walshMoment]

theorem actual_column_fifth_le_uniform (o : Orientation) (a : Byte) (ha : a ≠ 0) :
    (∑ b : Byte, channel o b a ^ 5) ≤ uniformH := by
  rw [actual_column_fifth o a ha]
  exact moment_le_uniform o

theorem actual_row_fifth_le_uniform (o : Orientation) (b : Byte) (hb : b ≠ 0) :
    (∑ a : Byte, channel o b a ^ 5) ≤ uniformH := by
  rw [actual_row_fifth o b hb]
  exact moment_le_uniform o

end AESConcrete.ByteFifthMoments
