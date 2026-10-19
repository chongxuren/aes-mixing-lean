import AESPaper.SingleByteSourceGram
import AESPaper.StartingWordDegrees
import AESConcrete.ByteColumnMoments
import AESConcrete.ColumnSupportResponse

/-!
# Actual one-active-byte source degrees

The first byte source is the actual nonzero AES byte column. Projection of
its four correlated outputs is identified with a tensor response whose
marked factors are residual byte channels. Their actual Grams coincide by
`SingleByteSourceGram`; each unmarked factor contributes exactly `1/255`.
The resulting signed Gram moments retain the common source and are summed
over the genuine residual-position patterns. No source-energy premise or
independence between the output bytes is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators Matrix

namespace AESPaper.SingleByteSourceDegrees
open AESMixing AESConcrete
open AESPaper.StartingWord (q wordLaw)
open AESPaper.StartingWordDegrees (centeredWordLaw byteDegreeEnergy inputByteWeight)
open AESPaper.SourceNumbers (sourceZ)
open AESConcrete.ByteGramCore (Byte NonzeroByte)
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteColumnMoments (nonzeroColumn)
open AESConcrete.ColumnFourthMoment (weightedMoment)
open AESConcrete.SingleByteCoordinates (coordinatePerm)
open AESConcrete.WordColumnGram (tensorResponse tensorColumn)

def sourceGram (x z : NonzeroByte) : ℝ := residualGram aesByteChannel x.val z.val

/-- The actual single-byte source has no discarded mass at zero. -/
theorem single_nonzero_response (a : AES.Word) (k : Fin 4)
    (hs : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) :
    wordLaw a = tensorResponse (fun _ : Fin 4 => aesByteChannel)
      (fun t : NonzeroByte => fun i => coordinatePerm false k i t.val)
      (nonzeroColumn .ordinary (a k)) := by
  have h := WordColumnGram.actual_single_active_response .ordinary .ordinary false a k hs
  rw [WordOrientationClosure.ordinary_word_kernel] at h
  funext y
  change AES.wordSuperboxKernel y a = _
  rw [congrFun h y]
  let f : Byte → ℝ := fun t =>
    (∏ i : Fin 4, aesByteChannel (y i) (coordinatePerm false k i t)) * aesByteChannel t (a k)
  have h0 : f 0 = 0 := by
    dsimp only [f]
    rw [aes_byte_resources.zero_row, if_neg ha, mul_zero]
  have hn := ByteColumnMoments.nonzero_sum f h0
  simpa only [f, SingleByteCoordinates.coordinatePerm_apply, tensorResponse, tensorColumn,
    nonzeroColumn, ByteOrientations.channel] using hn

/-- Projection acts on the response channels, with the original common source
label and its weight kept fixed. -/
theorem projected_tensor_response {X : Type*} [Fintype X]
    (b : Fin 4 → Bool) (coord : X → AES.Word) (mu : X → ℝ) :
    action (productProjection (0 : Byte) b)
        (tensorResponse (fun _ : Fin 4 => aesByteChannel) coord mu) =
      tensorResponse (fun i => bytePiece aesByteChannel (b i)) coord mu := by
  have hk : kernelCompose (productProjection (0 : Byte) b)
      (substitutionKernel aesByteChannel) =
      coordinateKernel (fun i => bytePiece aesByteChannel (b i)) := by
    change kernelCompose (coordinateKernel (fun i => degreePiece (0 : Byte) (b i)))
      (coordinateKernel (fun _ : Fin 4 => aesByteChannel)) = _
    rw [coordinateKernel_compose]
    simp_rw [byte_degree_left aes_byte_resources]
  funext y
  rw [ColumnSupportResponse.project_tensorResponse]
  simp only [hk, tensorResponse, tensorColumn, coordinateKernel]

theorem activity_gram (x z : Byte) :
    gram (activityMatrix (0 : Byte)) x z = activityMatrix 0 x z := by
  unfold gram
  simp_rw [activityMatrix_symmetric (0 : Byte) _ x]
  change kernelCompose (activityMatrix (0 : Byte)) (activityMatrix 0) x z = _
  rw [activityMatrix_idempotent (0 : Byte) (by norm_num [BinaryWord.card])]

theorem projected_piece_gram (k i : Fin 4) (b : Bool) (x z : NonzeroByte) :
    gram (bytePiece aesByteChannel b)
        (coordinatePerm false k i x.val) (coordinatePerm false k i z.val) =
      if b then sourceGram x z else 1/255 := by
  cases b
  · have hx := SingleByteCoordinates.coordinatePerm_ne_zero false k i x.val x.property
    have hz := SingleByteCoordinates.coordinatePerm_ne_zero false k i z.val z.property
    simp only [bytePiece, Bool.false_eq_true, if_false, activity_gram]
    norm_num [activityMatrix, hx, hz, BinaryWord.card]
  · change residualGram aesByteChannel
      (coordinatePerm false k i x.val) (coordinatePerm false k i z.val) = sourceGram x z
    exact SingleByteSourceGram.forward_residual_gram k i x.val z.val

-- These identities enumerate only the sixteen residual-position patterns.
theorem unmarked_pattern_count : ∀ b : Fin 4 → Bool,
    (Finset.univ.filter (fun i => ¬ b i = true)).card = 4-residualDegree b := by decide

theorem degree_pattern_count : ∀ j : Fin 5,
    (Finset.univ.filter (fun b : Fin 4 → Bool => degreeIndex b = j)).card =
      Nat.choose 4 j.val := by decide

theorem pattern_product (b : Fin 4 → Bool) (g c : ℝ) :
    (∏ i, if b i = true then g else c) =
      g ^ residualDegree b * c ^ (4-residualDegree b) := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, unmarked_pattern_count]
  rfl

/-- One selected residual pattern has the actual common-source Gram moment. -/
theorem pattern_energy (a : AES.Word) (k : Fin 4)
    (hs : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) (b : Fin 4 → Bool) :
    (∑ y, action (productProjection (0 : Byte) b) (wordLaw a) y ^ 2) =
      (1/255 : ℝ) ^ (4-residualDegree b) *
        weightedMoment (nonzeroColumn .ordinary (a k)) sourceGram (residualDegree b) := by
  rw [single_nonzero_response a k hs ha, projected_tensor_response,
    WordColumnGram.tensorResponse_energy]
  simp_rw [projected_piece_gram, pattern_product]
  unfold weightedMoment
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The five degrees sum the genuine patterns, with their binomial count. -/
theorem source_degree_energy_exact (a : AES.Word) (k : Fin 4)
    (hs : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) (j : Fin 5) :
    (∑ y, degreeComponent (0 : Byte) j (wordLaw a) y ^ 2) =
      (Nat.choose 4 j.val : ℝ) * (1/255 : ℝ) ^ (4-j.val) *
        weightedMoment (nonzeroColumn .ordinary (a k)) sourceGram j.val := by
  rw [degreeComponent_energy (0 : Byte) (by norm_num [BinaryWord.card])]
  have hterm (b : Fin 4 → Bool) :
      (if degreeIndex b = j then
        (∑ y, action (productProjection (0 : Byte) b) (wordLaw a) y ^ 2) else 0) =
      if degreeIndex b = j then
        (1/255 : ℝ) ^ (4-j.val) *
          weightedMoment (nonzeroColumn .ordinary (a k)) sourceGram j.val else 0 := by
    by_cases hb : degreeIndex b = j
    · rw [if_pos hb, if_pos hb, pattern_energy a k hs ha]
      have hd : residualDegree b = j.val := congrArg Fin.val hb
      rw [hd]
    · rw [if_neg hb, if_neg hb]
  simp_rw [hterm]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, degree_pattern_count]
  ring

def momentCap : Fin 5 → ℝ :=
  ![1, (9/128)^2 * (8383/2088960),
    (65/8192)*(8383/2088960)^2 + (1-65/8192)*(319/4177920)^2,
    (65/8192)*(8383/2088960)^3 + (1-65/8192)*(191/4177920)^3,
    (65/8192)*(8383/2088960)^4 + (1-65/8192)*(319/4177920)^4]

theorem actual_moment_le (a : Byte) (ha : a ≠ 0) (j : Fin 5) :
    weightedMoment (nonzeroColumn .ordinary a) sourceGram j.val ≤ momentCap j := by
  have hm := ByteColumnMoments.nonzeroColumn_mass .ordinary a ha
  have hc := ByteColumnMoments.nonzeroColumn_collision .ordinary a ha
  have hn (x : NonzeroByte) : 0 ≤ nonzeroColumn .ordinary a x :=
    aes_byte_resources.nonnegative x.val a
  have hd (x : NonzeroByte) : sourceGram x x = 8383/2088960 :=
    ByteGramDiagonal.residual_gram_diagonal_nonzero aes_byte_resources x.val x.property
  have ho (x z : NonzeroByte) (hxz : x ≠ z) :
      -(319/4177920 : ℝ) ≤ sourceGram x z ∧ sourceGram x z ≤ 191/4177920 :=
    ByteGramResources.actual_gram_offdiagonal .ordinary x.val z.val
      (fun h => hxz (Subtype.ext h))
  have h234 := ColumnFourthMoment.signed_moments (nonzeroColumn .ordinary a) sourceGram
    (65/8192) (8383/2088960) (319/4177920) (191/4177920)
    hn hm hc (by norm_num) (by norm_num) hd ho
  fin_cases j
  · simp only [Fin.val_zero, pow_zero, weightedMoment, mul_one]
    rw [ColumnFourthMoment.pair_mass _ hm]
    norm_num [momentCap]
  · have h1 := ByteColumnMoments.permuted_nonzero_first_moment .ordinary .ordinary
      (Equiv.refl Byte) rfl a ha
    change weightedMoment (nonzeroColumn .ordinary a) sourceGram 1 ≤
      (9/128 : ℝ)^2 * (8383/2088960)
    simp only [Equiv.refl_apply, ByteOrientations.channel] at h1
    have hgram : (fun x z : NonzeroByte => residualGram aesByteChannel x.val z.val) =
        sourceGram := rfl
    rw [hgram] at h1
    exact h1
  · change weightedMoment (nonzeroColumn .ordinary a) sourceGram 2 ≤
      (65/8192 : ℝ)*(8383/2088960)^2 + (1-65/8192)*(319/4177920)^2
    exact h234.1
  · change weightedMoment (nonzeroColumn .ordinary a) sourceGram 3 ≤
      (65/8192 : ℝ)*(8383/2088960)^3 + (1-65/8192)*(191/4177920)^3
    exact h234.2.1
  · change weightedMoment (nonzeroColumn .ordinary a) sourceGram 4 ≤
      (65/8192 : ℝ)*(8383/2088960)^4 + (1-65/8192)*(319/4177920)^4
    exact h234.2.2

def singleCap (j : Fin 5) : ℝ :=
  if j=0 then (1/255 : ℝ)^4 - 1/(q-1)
  else (Nat.choose 4 j.val : ℝ) * (1/255 : ℝ)^(4-j.val) * momentCap j

theorem source_energy_le_singleCap (a : AES.Word) (k : Fin 4)
    (hs : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) (j : Fin 5) :
    byteDegreeEnergy a j ≤ singleCap j := by
  have ha0 : a ≠ 0 := fun hz => ha (congrFun hz k)
  have hraw := source_degree_energy_exact a k hs ha j
  have hle := mul_le_mul_of_nonneg_left (actual_moment_le (a k) ha j)
    (by positivity : 0 ≤ (Nat.choose 4 j.val : ℝ) * (1/255 : ℝ)^(4-j.val))
  by_cases hj : j=0
  · subst j
    rw [StartingWordDegrees.byteDegreeEnergy_zero a ha0]
    rw [hraw]
    simpa only [singleCap, if_true, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one,
      one_mul, momentCap, Matrix.cons_val_zero, mul_one] using sub_le_sub_right hle (1/(q-1))
  · unfold byteDegreeEnergy
    rw [StartingWordDegrees.centered_positive_degree a j hj, hraw]
    simpa only [singleCap, if_neg hj] using hle

theorem singleCap_scaled_lt (j : Fin 5) : q * singleCap j < sourceZ 1 j ^ 2 := by
  fin_cases j <;> norm_num [singleCap, q, momentCap, sourceZ, Nat.choose]

/-- The actual weight-one source row, with a concrete single input position. -/
theorem source_degree_energy_lt_at (a : AES.Word) (k : Fin 4)
    (hs : ∀ i, i ≠ k → a i = 0) (ha : a k ≠ 0) (j : Fin 5) :
    q * byteDegreeEnergy a j < sourceZ 1 j ^ 2 := by
  exact (mul_le_mul_of_nonneg_left (source_energy_le_singleCap a k hs ha j)
    (by norm_num [q])).trans_lt (singleCap_scaled_lt j)

/-- The position and source law are derived from the actual input zero mask. -/
theorem source_degree_energy_lt_single (a : AES.Word) (ha : a ≠ 0)
    (hw : inputByteWeight a = 1) (j : Fin 5) :
    q * byteDegreeEnergy a j < sourceZ 1 j ^ 2 := by
  let z := AllColumnBound.inputZeroMask a
  have hm := AllColumnBound.inputZeroMask_size_lt_four a ha
  have hz : AES.maskSize z = 3 := by
    unfold inputByteWeight at hw
    dsimp only [z]
    omega
  obtain ⟨k,hk⟩ := StartingWord.one_active_choice z hz
  have hb (i : Fin 4) : a i = 0 ↔ AES.maskBit z i = true :=
    (AllColumnBound.inputZeroMask_bit a i).symm
  have hs : ∀ i, i ≠ k → a i = 0 := fun i hi => (hb i).mpr ((hk i).mpr hi)
  have hak : a k ≠ 0 := fun h => ((hk k).mp ((hb k).mp h)) rfl
  exact source_degree_energy_lt_at a k hs hak j

/-- All nonzero actual input words satisfy their own byte-weight source row. -/
theorem source_degree_energy_lt (a : AES.Word) (ha : a ≠ 0) (j : Fin 5) :
    q * byteDegreeEnergy a j < sourceZ (inputByteWeight a) j ^ 2 := by
  have hr := StartingWordDegrees.inputByteWeight_range a ha
  by_cases hw : inputByteWeight a = 1
  · rw [hw]
    exact source_degree_energy_lt_single a ha hw j
  · exact StartingWordDegrees.source_degree_energy_lt_multi a ha (inputByteWeight a)
      ⟨by omega, hr.2⟩ rfl j

end AESPaper.SingleByteSourceDegrees
