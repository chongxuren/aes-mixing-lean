import AESConcrete.ByteGramResources
import AESConcrete.ColumnFourthMoment

/-!
# Fourth moments for actual byte columns after arbitrary zero-fixing permutations

The source law is an actual AES byte column. The first residual-Gram moment
uses the byte operator bound on the centered, permuted source; its energy is
exactly the collision probability minus 1/255. Higher moments use the proved
signed Gram entries. No word-column or MDS estimate is assumed here.
Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ByteColumnMoments
open AESMixing
open AESConcrete.ByteGramCore (Byte NonzeroByte)
open AESConcrete.ByteGramDiagonal (residualGram residual_gram_formula residual_gram_diagonal_nonzero)
open AESConcrete.ByteGramResources (actual_gram_offdiagonal)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.ColumnFourthMoment

theorem nonzero_sum (f : Byte → ℝ) (h0 : f 0 = 0) :
    (∑ x : Byte, f x) = ∑ x : NonzeroByte, f x.val := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0, h0, zero_add]

theorem centered_source_energy (μ : Byte → ℝ) (h0 : μ 0 = 0)
    (hmass : (∑ x, μ x) = 1) (hcollision : (∑ x, μ x ^ 2) = (65 : ℝ)/8192) :
    (∑ x, wordResidual 0 μ x ^ 2) = (8383 : ℝ)/2088960 := by
  have hn : 1 < Fintype.card Byte := by norm_num [BinaryWord.card]
  have h := wordResidual_inner 0 hn μ μ
  rw [wordAverage_inner 0 hn μ μ] at h
  simp only [← sq, h0, hmass, hcollision, BinaryWord.card] at h
  norm_num at h ⊢
  exact h

/-- Exact first-moment estimate, allowing an arbitrary zero-fixing permutation.
The source is centered only after being transported to the Gram's labels. -/
theorem permuted_gram_first_moment (o : Orientation) (e : Equiv.Perm Byte)
    (he0 : e 0 = 0) (μ : Byte → ℝ) (h0 : μ 0 = 0)
    (hmass : (∑ x, μ x) = 1) (hcollision : (∑ x, μ x ^ 2) = (65 : ℝ)/8192) :
    (∑ x, ∑ z, μ x * μ z * residualGram (channel o) (e x) (e z)) ≤
      (9/128 : ℝ)^2 * ((8383 : ℝ)/2088960) := by
  let f : Byte → ℝ := fun x => μ (e.symm x)
  have hes : e.symm 0 = 0 := by
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using he0.symm
  have hf0 : f 0 = 0 := by simp only [f, hes, h0]
  have hfm : (∑ x, f x) = 1 := (Equiv.sum_comp e.symm μ).trans hmass
  have hfc : (∑ x, f x ^ 2) = (65 : ℝ)/8192 :=
    (Equiv.sum_comp e.symm (fun x => μ x ^ 2)).trans hcollision
  have henergy := centered_source_energy f hf0 hfm hfc
  have hn : 1 < Fintype.card Byte := by norm_num [BinaryWord.card]
  have hbound := (channel_resources o).residual (wordResidual 0 f)
    (wordResidual_at_zero 0 f) (wordResidual_sum 0 f hn)
  rw [henergy] at hbound
  have haction (y : Byte) :
      (∑ x, residualMatrix (channel o) 0 y (e x) * μ x) =
        action (residualMatrix (channel o) 0) f y := by
    simpa only [action, f, Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun x => residualMatrix (channel o) 0 y x * f x))
  have hgram := gram_quadratic
    (fun y x : Byte => residualMatrix (channel o) 0 y (e x)) μ
  have hge : (∑ y, action (residualMatrix (channel o) 0) f y ^ 2) =
      ∑ x, ∑ z, μ x * μ z * residualGram (channel o) (e x) (e z) := by
    simpa only [haction, residualGram, gram] using hgram
  rw [← hge, residualMatrix_action (channel_resources o).pointed]
  exact hbound

def nonzeroColumn (o : Orientation) (a : Byte) (x : NonzeroByte) : ℝ :=
  channel o x.val a

theorem nonzeroColumn_mass (o : Orientation) (a : Byte) (ha : a ≠ 0) :
    (∑ x, nonzeroColumn o a x) = 1 := by
  unfold nonzeroColumn
  rw [← nonzero_sum (fun x => channel o x a)
    (by rw [(channel_resources o).zero_row, if_neg ha])]
  exact (channel_resources o).column_sum a

theorem nonzeroColumn_collision (o : Orientation) (a : Byte) (ha : a ≠ 0) :
    (∑ x, nonzeroColumn o a x ^ 2) = (65 : ℝ)/8192 := by
  unfold nonzeroColumn
  rw [← nonzero_sum (fun x => channel o x a ^ 2)
    (by rw [(channel_resources o).zero_row, if_neg ha]; norm_num)]
  exact (channel_resources o).collision_column a ha

theorem permuted_nonzero_first_moment (left right : Orientation)
    (e : Equiv.Perm Byte) (he0 : e 0 = 0) (a : Byte) (ha : a ≠ 0) :
    weightedMoment (nonzeroColumn right a)
      (fun x z => residualGram (channel left) (e x.val) (e z.val)) 1 ≤
        (9/128 : ℝ)^2 * ((8383 : ℝ)/2088960) := by
  have h0 : channel right 0 a = 0 := by
    rw [(channel_resources right).zero_row, if_neg ha]
  have h := permuted_gram_first_moment left e he0 (fun x => channel right x a)
    h0 ((channel_resources right).column_sum a)
    ((channel_resources right).collision_column a ha)
  rw [nonzero_sum _ (by simp only [h0, zero_mul, Finset.sum_const_zero])] at h
  have hz (x : NonzeroByte) :
      (∑ z : Byte, channel right x.val a * channel right z a *
        residualGram (channel left) (e x.val) (e z)) =
      ∑ z : NonzeroByte, channel right x.val a * channel right z.val a *
        residualGram (channel left) (e x.val) (e z.val) :=
    nonzero_sum _ (by simp only [h0, mul_zero, zero_mul])
  simp_rw [hz] at h
  simpa only [weightedMoment, nonzeroColumn, pow_one] using h

/-- Each coordinate may use its own actual zero-fixing permutation. -/
theorem permuted_column_fourth_moment (left right : Orientation)
    (e : Equiv.Perm Byte) (he0 : e 0 = 0) (a : Byte) (ha : a ≠ 0) :
    weightedMoment (nonzeroColumn right a)
      (fun x z => gram (channel left) (e x.val) (e z.val)) 4 ≤ aesFourthBound := by
  have hne (x : NonzeroByte) : e x.val ≠ 0 := by
    intro hx
    exact x.property (e.injective (hx.trans he0.symm))
  have hdiag (x : NonzeroByte) :
      residualGram (channel left) (e x.val) (e x.val) = (8383 : ℝ)/2088960 :=
    residual_gram_diagonal_nonzero (channel_resources left) _ (hne x)
  have hoff (x z : NonzeroByte) (hxz : x ≠ z) :
      -((319 : ℝ)/4177920) ≤ residualGram (channel left) (e x.val) (e z.val) ∧
      residualGram (channel left) (e x.val) (e z.val) ≤ (191 : ℝ)/4177920 := by
    apply actual_gram_offdiagonal
    intro h
    exact hxz (Subtype.ext (e.injective h))
  have h := full_fourth_moment_le (nonzeroColumn right a)
    (fun x z => residualGram (channel left) (e x.val) (e z.val))
    (1/255) (9/128) (65/8192) (8383/2088960) (319/4177920) (191/4177920)
    (fun x => (channel_resources right).nonnegative _ _)
    (nonzeroColumn_mass right a ha) (nonzeroColumn_collision right a ha)
    (by norm_num) (by norm_num) (by norm_num) hdiag hoff
    (permuted_nonzero_first_moment left right e he0 a ha)
  have hf (x z : NonzeroByte) :
      gram (channel left) (e x.val) (e z.val) =
        (1/255 : ℝ) + residualGram (channel left) (e x.val) (e z.val) := by
    rw [residual_gram_formula (channel_resources left)]
    norm_num [activityMatrix, hne x, hne z, BinaryWord.card]
  simp_rw [hf]
  convert h using 1 <;> norm_num [aesFourthBound, fourthBound]

end AESConcrete.ByteColumnMoments
