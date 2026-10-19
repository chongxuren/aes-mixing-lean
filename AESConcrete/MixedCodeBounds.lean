import AESConcrete.LineOverlap

/-!
# Analytic transverse line/plane bounds for actual residual codes

The response inner product is expanded in its original joint output space.
For a bijective line/plane difference map, each byte triple occurs once.
The unique zero difference comes from the distinguished zero pair and is
killed by an actual residual Gram zero row.  Bounding the other differences
by diagonal/off-diagonal spikes yields the transverse f3 estimate.

The code geometry is an explicit hypothesis.  This module does not assert
that a particular AES shortening has that geometry, does not prove the
containment case, and does not assemble the centered word operator.
Constructive proof work only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.MixedCodeBounds
open AESMixing
open AESConcrete.ByteGramCore (Byte)
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteOrientations (Orientation channel)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.DampedLineGram (crossGram)
open AESConcrete.LineOverlap (delta offdiag)

variable {C D : Type*} [Fintype C] [Fintype D]

/-- Raw code response, retaining every source point and its multiplicity. -/
def codeResponse (c : C → Fin 3 → Byte) (T : Fin 3 → Byte → Byte → ℝ)
    (y : Fin 3 → Byte) : ℝ :=
  ∑ x : C, ∏ i : Fin 3, T i (y i) (c x i)

def lineCodeResponse (c : C → Fin 3 → Byte) (T : Fin 3 → Byte → Byte → ℝ)
    (y : Fin 3 → Byte) : ℝ := codeResponse c T y / 256

def planeCodeResponse (d : D → Fin 3 → Byte) (T : Fin 3 → Byte → Byte → ℝ)
    (y : Fin 3 → Byte) : ℝ := codeResponse d T y / 4096

/-- Raw joint-output Gram identity for arbitrary finite coordinate maps.
No injectivity, independence, or Fourier transport is used. -/
theorem codeResponse_inner (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (T U : Fin 3 → Byte → Byte → ℝ) :
    (∑ y : Fin 3 → Byte, codeResponse c T y * codeResponse d U y) =
      ∑ x : C, ∑ z : D, ∏ i : Fin 3, crossGram (T i) (U i) (c x i) (d z i) := by
  unfold codeResponse
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i v => T i v (c x i) * U i v (d z i))).symm

/-- The line /256 and plane /4096 normalizations give q/(256*4096)=4096.
The underlying raw Gram identity is kept separate from this scalar step. -/
theorem scaled_mixed_inner (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (T U : Fin 3 → Byte → Byte → ℝ) :
    (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      lineCodeResponse c T y * planeCodeResponse d U y) =
      4096 * ∑ x : C, ∑ z : D, ∏ i : Fin 3,
        crossGram (T i) (U i) (c x i) (d z i) := by
  unfold lineCodeResponse planeCodeResponse
  simp_rw [div_mul_div_comm]
  rw [← Finset.sum_div, codeResponse_inner]
  ring

def codeDifference (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (p : C × D) : Fin 3 → Byte := fun i => c p.1 i - d p.2 i

def gramProduct (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte)
    (d : D → Fin 3 → Byte) (p : C × D) : ℝ :=
  ∏ i : Fin 3, residualGram (channel (o i)) (c p.1 i) (d p.2 i)

def differenceSpike (w : Fin 3 → Byte) : ℝ :=
  ∏ i : Fin 3, if w i = 0 then delta else offdiag

def puncturedSpike (w : Fin 3 → Byte) : ℝ :=
  if w = 0 then 0 else differenceSpike w

def f3 : ℝ := 4096 * ((delta + 255 * offdiag)^3 - delta^3)

/-- The zero row extends the frozen nonzero-column spike bound to all inputs. -/
theorem actual_gram_spike_all (o : Orientation) (u v : Byte) :
    |residualGram (channel o) u v| ≤ if u = v then delta else offdiag := by
  by_cases hu : u = 0
  · subst u
    rw [ByteGramDiagonal.actual_gram_zero_row]
    simp only [abs_zero]
    split_ifs <;> norm_num [delta, offdiag]
  · exact LineOverlap.actual_gram_spike o u v hu

theorem byte_spike_sum :
    (∑ v : Byte, if v = 0 then delta else offdiag) = delta + 255 * offdiag := by
  classical
  have he (v : Byte) : (if v = 0 then delta else offdiag) =
      offdiag + (if v = 0 then delta - offdiag else 0) := by
    split_ifs <;> ring
  simp_rw [he, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  norm_num [BinaryWord.card]
  ring

theorem differenceSpike_zero : differenceSpike (0 : Fin 3 → Byte) = delta^3 := by
  simp [differenceSpike]

theorem differenceSpike_sum :
    (∑ w : Fin 3 → Byte, differenceSpike w) = (delta + 255 * offdiag)^3 := by
  calc
    _ = ∏ _ : Fin 3, ∑ v : Byte, if v = 0 then delta else offdiag :=
      (Fintype.prod_sum (fun (_ : Fin 3) (v : Byte) =>
        if v = 0 then delta else offdiag)).symm
    _ = _ := by simp_rw [byte_spike_sum]; simp

/-- Exact full difference-spike sum with the all-zero triple removed. -/
theorem puncturedSpike_sum :
    (∑ w : Fin 3 → Byte, puncturedSpike w) =
      (delta + 255 * offdiag)^3 - delta^3 := by
  classical
  have he (w : Fin 3 → Byte) : puncturedSpike w =
      differenceSpike w - (if w = 0 then delta^3 else 0) := by
    by_cases hw : w = 0
    · subst w
      simp [puncturedSpike, differenceSpike_zero]
    · simp [puncturedSpike, hw]
  simp_rw [he, Finset.sum_sub_distrib]
  rw [differenceSpike_sum]
  simp

/-- Under bijective difference, zero difference is the distinguished zero
pair.  It contributes zero rather than the all-diagonal spike delta^3. -/
theorem gramProduct_abs_le_puncturedSpike
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (c0 : C) (d0 : D) (hc0 : c c0 = 0) (hd0 : d d0 = 0)
    (hbij : Function.Bijective (codeDifference c d)) (p : C × D) :
    |gramProduct o c d p| ≤ puncturedSpike (codeDifference c d p) := by
  classical
  have hmap0 : codeDifference c d (c0, d0) = 0 := by
    funext i
    simp [codeDifference, hc0, hd0]
  by_cases hp : codeDifference c d p = 0
  · have hpair : p = (c0, d0) := hbij.1 (hp.trans hmap0.symm)
    have hz : gramProduct o c d p = 0 := by
      rw [hpair]
      unfold gramProduct
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3))
      rw [hc0]
      exact ByteGramDiagonal.actual_gram_zero_row (o 0) (d d0 0)
    simp [puncturedSpike, hp, hz]
  · rw [puncturedSpike, if_neg hp]
    unfold gramProduct differenceSpike
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    intro i _
    simpa only [codeDifference, sub_eq_zero] using
      actual_gram_spike_all (o i) (c p.1 i) (d p.2 i)

/-- Analytic transverse raw bound.  Bijective difference is the sole code
geometry hypothesis; the actual caller must prove it from its shortenings. -/
theorem actual_transverse_raw_bound
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (c0 : C) (d0 : D) (hc0 : c c0 = 0) (hd0 : d d0 = 0)
    (hbij : Function.Bijective (codeDifference c d)) :
    |∑ x : C, ∑ z : D, ∏ i : Fin 3,
      residualGram (channel (o i)) (c x i) (d z i)| ≤
        (delta + 255 * offdiag)^3 - delta^3 := by
  classical
  have he : (∑ x : C, ∑ z : D, ∏ i : Fin 3,
      residualGram (channel (o i)) (c x i) (d z i)) =
      ∑ p : C × D, gramProduct o c d p := by
    rw [Fintype.sum_prod_type]
    rfl
  rw [he]
  calc
    _ ≤ ∑ p : C × D, |gramProduct o c d p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : C × D, puncturedSpike (codeDifference c d p) :=
      Finset.sum_le_sum (fun p _ =>
        gramProduct_abs_le_puncturedSpike o c d c0 d0 hc0 hd0 hbij p)
    _ = ∑ w : Fin 3 → Byte, puncturedSpike w :=
      Equiv.sum_comp (Equiv.ofBijective (codeDifference c d) hbij) puncturedSpike
    _ = _ := puncturedSpike_sum

/-- Actual ordinary-residual line/plane transverse f3 bound, with exact
source normalizations and unchanged joint output labels. -/
theorem actual_transverse_bound
    (o : Fin 3 → Orientation) (c : C → Fin 3 → Byte) (d : D → Fin 3 → Byte)
    (c0 : C) (d0 : D) (hc0 : c c0 = 0) (hd0 : d d0 = 0)
    (hbij : Function.Bijective (codeDifference c d)) :
    (4294967296 : ℝ) * |∑ y : Fin 3 → Byte,
      lineCodeResponse c (fun i => leg (o i) false) y *
      planeCodeResponse d (fun i => leg (o i) false) y| ≤ f3 := by
  have hi : (4294967296 : ℝ) * (∑ y : Fin 3 → Byte,
      lineCodeResponse c (fun i => leg (o i) false) y *
      planeCodeResponse d (fun i => leg (o i) false) y) =
      4096 * ∑ x : C, ∑ z : D, ∏ i : Fin 3,
        residualGram (channel (o i)) (c x i) (d z i) :=
    scaled_mixed_inner c d (fun i => leg (o i) false) (fun i => leg (o i) false)
  have ha := congrArg abs hi
  simp only [abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4294967296),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4096)] at ha
  rw [ha]
  exact mul_le_mul_of_nonneg_left
    (actual_transverse_raw_bound o c d c0 d0 hc0 hd0 hbij) (by norm_num)

end AESConcrete.MixedCodeBounds
