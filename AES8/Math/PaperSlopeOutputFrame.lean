import AES8.Math.PaperSlopeCoincidenceMatrix
import AESConcrete.ActivityFrame

/-! Exact output-frame signs and the positive constant kernel discarded by
 the degree-two argument. The output labels are the two unmarked graph positions.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeOutputFrame
open PaperSlopeCoincidences PaperSymbolicSlopeTable PaperSlopeCoincidenceMatrix
open AESMixing AESConcrete.ActivityFrame
set_option autoImplicit false
set_option maxRecDepth 100000

def outputBits (p : Fin 6) (k : Fin 20) : Fin 2 → Bool := fun i =>
  decide ((if i = 0 then (if pairType p then 5 else 6) else 7 : Fin 8) ∈
    triples (pairType p) k)

theorem output_mismatches (p : Fin 6) (k l : Fin 20) :
    (Finset.univ.filter (fun i : Fin 2 => outputBits p k i ≠ outputBits p l i)).card =
      outputDistance p k l := by
  revert p k l
  decide

theorem product_form (t : ℝ) (p : Fin 6) (k l : Fin 20) :
    (∏ i : Fin 2, if outputBits p k i = outputBits p l i then 1 else t) =
      t^outputDistance p k l := by
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [output_mismatches]

theorem frame_metric (p : Fin 6) (k l : Fin 20) :
    frameMetric (outputBits p k) (outputBits p l) = (1/16 : ℝ)^outputDistance p k l := by
  exact product_form (1/16) p k l

theorem frame_inverse (p : Fin 6) (k l : Fin 20) :
    frameInverse (outputBits p k) (outputBits p l) =
      (256/255 : ℝ)^2 * (-(1/16 : ℝ))^outputDistance p k l := by
  unfold frameInverse byteInverse
  rw [Finset.prod_mul_distrib, product_form]
  norm_num [div_pow]

def inputSign (p : Fin 6) (k : Fin 20) : ℝ := (-1)^(inputSet p k).card

theorem sign_identity_integer (p : Fin 6) (k l : Fin 20) :
    (-1 : ℤ)^(inputSet p k).card * (-1)^(inputSet p l).card *
      (-1)^outputDistance p k l = 1 := by
  revert p k l
  decide

theorem sign_identity (p : Fin 6) (k l : Fin 20) :
    inputSign p k * inputSign p l * (-1)^outputDistance p k l = 1 := by
  unfold inputSign
  exact_mod_cast sign_identity_integer p k l

theorem signed_inverse (p : Fin 6) (k l : Fin 20) :
    inputSign p k * inputSign p l * frameInverse (outputBits p k) (outputBits p l) =
      (256/255 : ℝ)^2 * (1/16 : ℝ)^outputDistance p k l := by
  rw [frame_inverse, neg_eq_neg_one_mul, mul_pow]
  calc
    _ = (256/255 : ℝ)^2 *
        (inputSign p k * inputSign p l * (-1)^outputDistance p k l) *
          (1/16 : ℝ)^outputDistance p k l := by ring
    _ = _ := by rw [sign_identity]; ring

/-- The discarded constant term is an actual Gram quadratic, even when
multiple contraction labels use the same output frame vector. -/
theorem distance_quadratic_nonneg (p : Fin 6) (x : Fin 20 → ℝ) :
    0 ≤ ∑ k : Fin 20, ∑ l : Fin 20,
      x k*x l*(1/16 : ℝ)^outputDistance p k l := by
  let F : (Fin 2 → Fin 256) → Fin 20 → ℝ :=
    fun y k => frameColumn (outputBits p k) y
  have hg (k l : Fin 20) : gram F k l = (1/16 : ℝ)^outputDistance p k l := by
    change (∑ y : Fin 2 → Fin 256,
      frameColumn (outputBits p k) y * frameColumn (outputBits p l) y) = _
    rw [AESConcrete.ActivityFrame.frame_gram (by simp), frame_metric]
  have he := gram_quadratic F x
  simp only [hg] at he
  rw [← he]
  exact Finset.sum_nonneg (fun y _ => sq_nonneg _)

end AES8.PaperSlopeOutputFrame
