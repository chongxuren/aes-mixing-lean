import AESConcrete.MixedCodeBounds
import AESConcrete.PlaneWeightEnumerator

/-!
# Analytic containment line/plane interval

A caller-supplied permutation shift reindexes each line/plane pair by its
plane difference.  The zero difference contributes exactly 255*delta^3.
The remaining differences are bounded by the exact nonzero plane spike
enumerator.  The line and plane normalizations then give z3 plus/minus h3.

All code geometry is explicit in the hypotheses.  Actual AES shortening
instantiation, centered-word identification, and metric assembly are separate.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ContainmentCodeBounds
open AESMixing
open AESConcrete.ByteGramCore (Byte)
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.LineOverlap (delta offdiag)
open AESConcrete.MixedCodeBounds (gramProduct lineCodeResponse planeCodeResponse)

attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D]

def rawGramSum (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte)
    (d : D → Fin 3 → Byte) : ℝ :=
  ∑ x : C, ∑ z : D, gramProduct o c d (x, z)

def shiftedRemainder (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte)
    (d : D → Fin 3 → Byte) (shift : C → Equiv.Perm D) (d0 : D) : ℝ :=
  ∑ x : C, ∑ w : {w : D // w ≠ d0}, gramProduct o c d (x, shift x w.val)

def z3 : ℝ := 4096 * 255 * delta^3
def h3 : ℝ := 1048576 * 255 * (3*delta*offdiag^2 + 254*offdiag^3)

/-- Reindexing and the distinguished-point split are independent of all
diagonal and off-diagonal estimates. -/
theorem shifted_decomposition
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (shift : C → Equiv.Perm D) (d0 : D) :
    rawGramSum o c d =
      (∑ x : C, gramProduct o c d (x, shift x d0)) + shiftedRemainder o c d shift d0 := by
  unfold rawGramSum
  calc
    _ = ∑ x : C, ∑ w : D, gramProduct o c d (x, shift x w) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Equiv.sum_comp (shift x) (fun z => gramProduct o c d (x, z))).symm
    _ = ∑ x : C, (gramProduct o c d (x, shift x d0) +
        ∑ w : {w : D // w ≠ d0}, gramProduct o c d (x, shift x w.val)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Fintype.sum_eq_add_sum_subtype_ne (fun w => gramProduct o c d (x, shift x w)) d0
    _ = _ := by rw [Finset.sum_add_distrib]; rfl

/-- Zero difference identifies equal input coordinates.  The actual zero
row kills c0; every other line point contributes the exact diagonal cube. -/
theorem gramProduct_shift_diagonal
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (c0 : C) (d0 : D) (hc0 : c c0 = 0) (hd0 : d d0 = 0)
    (hline : ∀ x, x ≠ c0 → ∀ i, c x i ≠ 0)
    (shift : C → Equiv.Perm D)
    (hshift : ∀ x w i, c x i - d (shift x w) i = d w i) (x : C) :
    gramProduct o c d (x, shift x d0) = if x = c0 then 0 else delta^3 := by
  have heq (i : Fin 3) : c x i = d (shift x d0) i := by
    apply sub_eq_zero.mp
    rw [hshift, hd0]
    rfl
  by_cases hx : x = c0
  · subst x
    rw [if_pos rfl]
    unfold gramProduct
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3))
    rw [hc0]
    exact ByteGramDiagonal.actual_gram_zero_row (o 0) _
  · rw [if_neg hx]
    unfold gramProduct
    have hg (i : Fin 3) : residualGram (channel (o i)) (c x i) (d (shift x d0) i) = delta := by
      rw [← heq i, ByteGramDiagonal.actual_gram_diagonal, if_neg (hline x hx i)]
      norm_num [delta]
    simp_rw [hg]
    simp

theorem shifted_diagonal_sum
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (c0 : C) (d0 : D) (hc0 : c c0 = 0) (hd0 : d d0 = 0)
    (hcard : Fintype.card C = 256) (hline : ∀ x, x ≠ c0 → ∀ i, c x i ≠ 0)
    (shift : C → Equiv.Perm D)
    (hshift : ∀ x w i, c x i - d (shift x w) i = d w i) :
    (∑ x : C, gramProduct o c d (x, shift x d0)) = 255*delta^3 := by
  simp_rw [gramProduct_shift_diagonal o c d c0 d0 hc0 hd0 hline shift hshift]
  have he (x : C) : (if x = c0 then (0 : ℝ) else delta^3) =
      delta^3 - (if x = c0 then delta^3 else 0) := by
    split_ifs <;> ring
  simp_rw [he, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num
  ring

/-- Every shifted pair is bounded by the spike of its actual difference. -/
theorem gramProduct_shift_abs_le_spike
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (shift : C → Equiv.Perm D)
    (hshift : ∀ x w i, c x i - d (shift x w) i = d w i) (x : C) (w : D) :
    |gramProduct o c d (x, shift x w)| ≤ PlaneWeightEnumerator.spikeProduct delta offdiag d w := by
  unfold gramProduct PlaneWeightEnumerator.spikeProduct
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
  intro i _
  have heq : c x i = d (shift x w) i ↔ d w i = 0 := by
    rw [← hshift x w i, sub_eq_zero]
  simpa only [heq] using MixedCodeBounds.actual_gram_spike_all (o i) (c x i) (d (shift x w) i)

/-- The finite line cardinality multiplies the exact nonzero plane
enumerator.  No unproved pair-difference fiber count is used here: the
per-line reindexing is already the supplied permutation shift. -/
theorem shifted_remainder_bound
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (d0 : D) (hd0 : d d0 = 0) (hcardC : Fintype.card C = 256)
    (hcardD : Fintype.card D = 65536)
    (hfiber : ∀ i, Fintype.card {w : D // d w i = 0} = 256)
    (htwo : ∀ w i j, i ≠ j → d w i = 0 → d w j = 0 → w = d0)
    (shift : C → Equiv.Perm D)
    (hshift : ∀ x w i, c x i - d (shift x w) i = d w i) :
    |shiftedRemainder o c d shift d0| ≤ 256*255*(3*delta*offdiag^2 + 254*offdiag^3) := by
  unfold shiftedRemainder
  calc
    _ ≤ ∑ x : C, |∑ w : {w : D // w ≠ d0}, gramProduct o c d (x, shift x w.val)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : C, ∑ w : {w : D // w ≠ d0}, |gramProduct o c d (x, shift x w.val)| :=
      Finset.sum_le_sum (fun x _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _x : C, ∑ w : {w : D // w ≠ d0},
        PlaneWeightEnumerator.spikeProduct delta offdiag d w.val := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.sum_le_sum (fun w _ => gramProduct_shift_abs_le_spike o c d shift hshift x w.val)
    _ = 256*(3*255*delta*offdiag^2 + 255*254*offdiag^3) := by
      simp_rw [PlaneWeightEnumerator.plane_nonzero_spike_sum delta offdiag d d0 hd0 hcardD hfiber htwo]
      simp [hcardC]
      ring
    _ = _ := by ring

theorem actual_containment_raw_bound
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (c0 : C) (d0 : D) (hc0 : c c0 = 0) (hd0 : d d0 = 0)
    (hcardC : Fintype.card C = 256) (hcardD : Fintype.card D = 65536)
    (hline : ∀ x, x ≠ c0 → ∀ i, c x i ≠ 0)
    (hfiber : ∀ i, Fintype.card {w : D // d w i = 0} = 256)
    (htwo : ∀ w i j, i ≠ j → d w i = 0 → d w j = 0 → w = d0)
    (shift : C → Equiv.Perm D)
    (hshift : ∀ x w i, c x i - d (shift x w) i = d w i) :
    |rawGramSum o c d - 255*delta^3| ≤ 256*255*(3*delta*offdiag^2 + 254*offdiag^3) := by
  have hd := shifted_decomposition o c d shift d0
  rw [shifted_diagonal_sum o c d c0 d0 hc0 hd0 hcardC hline shift hshift] at hd
  have he : rawGramSum o c d - 255*delta^3 = shiftedRemainder o c d shift d0 := by linarith
  rw [he]
  exact shifted_remainder_bound o c d d0 hd0 hcardC hcardD hfiber htwo shift hshift

/-- Signed midpoint/error estimate with source line /256 and plane /4096
normalizations.  Both compared responses use the same ordinary actual
residual orientation on each leg. -/
theorem actual_containment_bound
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (c0 : C) (d0 : D) (hc0 : c c0 = 0) (hd0 : d d0 = 0)
    (hcardC : Fintype.card C = 256) (hcardD : Fintype.card D = 65536)
    (hline : ∀ x, x ≠ c0 → ∀ i, c x i ≠ 0)
    (hfiber : ∀ i, Fintype.card {w : D // d w i = 0} = 256)
    (htwo : ∀ w i j, i ≠ j → d w i = 0 → d w j = 0 → w = d0)
    (shift : C → Equiv.Perm D)
    (hshift : ∀ x w i, c x i - d (shift x w) i = d w i) :
    |(4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      lineCodeResponse c (fun i => leg (o i) false) y *
      planeCodeResponse d (fun i => leg (o i) false) y) - z3| ≤ h3 := by
  have hi : (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      lineCodeResponse c (fun i => leg (o i) false) y *
      planeCodeResponse d (fun i => leg (o i) false) y) = 4096*rawGramSum o c d :=
    MixedCodeBounds.scaled_mixed_inner c d (fun i => leg (o i) false) (fun i => leg (o i) false)
  rw [hi]
  have he : 4096*rawGramSum o c d - z3 = 4096*(rawGramSum o c d - 255*delta^3) := by
    unfold z3
    ring
  rw [he, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4096)]
  calc
    _ ≤ 4096*(256*255*(3*delta*offdiag^2 + 254*offdiag^3)) :=
      mul_le_mul_of_nonneg_left
        (actual_containment_raw_bound o c d c0 d0 hc0 hd0 hcardC hcardD hline hfiber htwo shift hshift)
        (by norm_num)
    _ = h3 := by unfold h3; ring

theorem actual_containment_interval
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (c0 : C) (d0 : D) (hc0 : c c0 = 0) (hd0 : d d0 = 0)
    (hcardC : Fintype.card C = 256) (hcardD : Fintype.card D = 65536)
    (hline : ∀ x, x ≠ c0 → ∀ i, c x i ≠ 0)
    (hfiber : ∀ i, Fintype.card {w : D // d w i = 0} = 256)
    (htwo : ∀ w i j, i ≠ j → d w i = 0 → d w j = 0 → w = d0)
    (shift : C → Equiv.Perm D)
    (hshift : ∀ x w i, c x i - d (shift x w) i = d w i) :
    z3-h3 ≤ (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      lineCodeResponse c (fun i => leg (o i) false) y *
      planeCodeResponse d (fun i => leg (o i) false) y) ∧
    (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      lineCodeResponse c (fun i => leg (o i) false) y *
      planeCodeResponse d (fun i => leg (o i) false) y) ≤ z3+h3 := by
  have h := abs_le.mp
    (actual_containment_bound o c d c0 d0 hc0 hd0 hcardC hcardD hline hfiber htwo shift hshift)
  constructor <;> linarith [h.1, h.2]

end AESConcrete.ContainmentCodeBounds
