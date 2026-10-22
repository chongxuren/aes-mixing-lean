import AES8.Math.PaperActivityInputArithmetic
import AES8.Math.PaperActivityInputCounts

/-! Arbitrary-coefficient assembly using the genuine word frame. Input and
output losses are proved from the frame Gram rather than assumed. This leaf
is generic in the response blocks; their actual graph identification and MDS
moments belong to the physical reduction. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityInputAssembly
open AESMixing WordActivityFrame PaperActivityInputGram PaperActivityInputArithmetic
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

variable {N : Type*} [Fintype N] [DecidableEq N]

def synthesize (c : (N → Bool) → ℝ) (x : N → AES.Word) : ℝ :=
  ∑ a, frameColumn 0 a x * c a
def analyze (f : (N → AES.Word) → ℝ) (a : N → Bool) : ℝ :=
  ∑ x, frameColumn 0 a x * f x

/-- Analysis controls the energy on the actual tensor-frame range. -/
theorem analysis_energy_lower (hn : Fintype.card N ≤ 6)
    (c : (N → Bool) → ℝ) :
    (∑ x, synthesize c x ^ 2) ≤ loss * ∑ a, analyze (synthesize c) a ^ 2 := by
  let e : ℝ := ∑ x, synthesize c x ^ 2
  have he : 0 ≤ e := by positivity
  have hid : (∑ a, c a * analyze (synthesize c) a) = e := by
    unfold e analyze
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    calc
      _ = (∑ a, frameColumn 0 a x * c a) * synthesize c x := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by change synthesize c x * synthesize c x = _; ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (analyze (synthesize c))
  rw [hid] at hcs
  have hc := word_frame_coefficients hn c
  change (∑ a, c a ^ 2) ≤ loss * e at hc
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ ∑ a, analyze (synthesize c) a ^ 2 by positivity)
  change e ≤ _
  by_cases hz : e = 0
  · rw [hz]; exact mul_nonneg (by norm_num [loss]) (by positivity)
  · have hp : 0 < e := lt_of_le_of_ne he (Ne.symm hz)
    nlinarith

variable {X A B : Type*} [Fintype X] [Fintype A] [Fintype B] [DecidableEq B]

/-- Only the scalar matrix of block lengths enters the comparison.
The response vectors may have arbitrary signs and correlations. -/
theorem vector_block_energy (w : A → B → X → ℝ) (C : A → B → ℝ)
    (hC : ∀ a b, 0 ≤ C a b)
    (hw : ∀ a b, l2 (w a b) ≤ C a b)
    (r : ℝ) (hr : 0 ≤ r)
    (hrow : ∀ a a', 0 ≤ ∑ b, C a b * C a' b)
    (hgram : ∀ a, (∑ a', ∑ b, C a b * C a' b) ≤ r)
    (c : B → ℝ) :
    (∑ a, ∑ x, (∑ b, c b * w a b x)^2) ≤ r * ∑ b, c b ^ 2 := by
  have hpoint (a : A) : l2 (fun x => ∑ b, c b * w a b x) ≤
      action C (fun b => |c b|) a := by
    calc
      _ ≤ ∑ b, l2 (fun x => c b * w a b x) := l2_finset_sum_le Finset.univ _
      _ = ∑ b, |c b| * l2 (w a b) := by simp only [l2_scale]
      _ ≤ ∑ b, |c b| * C a b := Finset.sum_le_sum
        (fun b _ => mul_le_mul_of_nonneg_left (hw a b) (abs_nonneg _))
      _ = _ := by simp only [action, mul_comm]
  have h := energy_of_rowGram C r hr hrow hgram (fun b => |c b|)
  simp only [sq_abs] at h
  apply le_trans _ h
  apply Finset.sum_le_sum
  intro a _
  have hp : 0 ≤ action C (fun b => |c b|) a := by
    exact Finset.sum_nonneg (fun b _ => mul_nonneg (hC a b) (abs_nonneg _))
  have hs := (sq_le_sq₀ (l2_nonneg _) hp).mpr (hpoint a)
  simpa only [l2_sq] using hs

section TwoFrames
variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]

/-- Both nonorthogonal frame losses are derived from their actual Gram.
The only response premises are literal vector lengths and the scalar row-Gram
certificate, which are supplied separately by geometry and Boolean counting. -/
theorem two_frame_energy (hI : Fintype.card I ≤ 6) (hO : Fintype.card O ≤ 6)
    (c : (I → Bool) → ℝ) (g : X × (O → AES.Word) → ℝ)
    (d : X → (O → Bool) → ℝ)
    (hRange : ∀ x u, g (x,u) = synthesize (d x) u)
    (w : (O → Bool) → (I → Bool) → X → ℝ)
    (hJoin : ∀ a x, analyze (fun u => g (x,u)) a = ∑ b, c b * w a b x)
    (C : (O → Bool) → (I → Bool) → ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (hw : ∀ a b, l2 (w a b) ≤ C a b)
    (r : ℝ) (hr : 0 ≤ r)
    (hrow : ∀ a a', 0 ≤ ∑ b, C a b * C a' b)
    (hgram : ∀ a, (∑ a', ∑ b, C a b * C a' b) ≤ r) :
    (∑ p, g p ^ 2) ≤ loss^2*r*∑ x, synthesize c x ^ 2 := by
  have hL : 0 ≤ loss := by norm_num [loss]
  have hout : (∑ p, g p ^ 2) ≤ loss * ∑ x : X, ∑ a, analyze (fun u => g (x,u)) a ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have h := analysis_energy_lower hO (d x)
    simpa only [hRange] using h
  have hblocks := vector_block_energy w C hC hw r hr hrow hgram c
  have hmid : (∑ x : X, ∑ a, analyze (fun u => g (x,u)) a ^ 2) ≤ r*∑ b, c b^2 := by
    simp_rw [hJoin]
    rw [Finset.sum_comm]
    exact hblocks
  have hin := word_frame_coefficients hI c
  change (∑ b, c b^2) ≤ loss * ∑ x, synthesize c x^2 at hin
  calc
    _ ≤ loss * (r * ∑ b, c b^2) :=
      hout.trans (mul_le_mul_of_nonneg_left hmid hL)
    _ ≤ loss * (r * (loss * ∑ x, synthesize c x^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin hr) hL
    _ = _ := by ring

end TwoFrames

end AES8.PaperActivityInputAssembly
