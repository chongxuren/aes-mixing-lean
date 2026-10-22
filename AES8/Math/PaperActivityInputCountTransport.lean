import AES8.Math.PaperActivityInputCounts

/-! Boolean support certificates transported along actual position bijections.
Only names of frame coordinates change; the row-Gram and weights remain exact. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityInputCountTransport
open AESMixing PaperActivityInputCounts
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

variable {N : Type*} [Fintype N] [DecidableEq N]

def weightOn (a : N → Bool) : ℕ :=
  (Finset.univ.filter (fun j => a j = true)).card

def labelEquiv {m : ℕ} (e : N ≃ Fin m) : (N → Bool) ≃ Mask m where
  toFun a k := a (e.symm k)
  invFun b j := b (e j)
  left_inv a := by funext j; simp
  right_inv b := by funext k; simp

omit [DecidableEq N] in
theorem weight_label {m : ℕ} (e : N ≃ Fin m) (a : N → Bool) :
    weight (labelEquiv e a) = weightOn a := by
  unfold weight weightOn
  simp only [Finset.card_filter]
  have h := e.sum_comp (fun k : Fin m => if labelEquiv e a k = true then (1 : ℕ) else 0)
  simpa only [labelEquiv,Equiv.coe_fn_mk,Equiv.symm_apply_apply] using h.symm

def supportedTwo (a : N → Bool) (b : Mask 4) : Prop := weightOn a + weight b = 3
def supportedThree (a : N → Bool) (b : Mask 4) : Prop :=
  weightOn a + weight b = 2 ∨ weightOn a + weight b = 3

instance (a : N → Bool) (b : Mask 4) : Decidable (supportedTwo a b) := inferInstanceAs
  (Decidable (weightOn a + weight b = 3))
instance (a : N → Bool) (b : Mask 4) : Decidable (supportedThree a b) := inferInstanceAs
  (Decidable (weightOn a + weight b = 2 ∨ weightOn a + weight b = 3))

theorem two_gram (e : N ≃ Fin 2) (a : N → Bool) :
    (∑ a' : N → Bool, ∑ b : Mask 4,
      (if supportedTwo a b then (1 : ℝ) else 0) *
      (if supportedTwo a' b then (1 : ℝ) else 0)) ≤ 12 := by
  have h (u v : N → Bool) :
      (∑ b : Mask 4, (if supportedTwo u b then (1 : ℝ) else 0) *
        (if supportedTwo v b then (1 : ℝ) else 0)) =
      (overlap allowedTwo (labelEquiv e u) (labelEquiv e v) : ℝ) := by
    rw [← scalar_rowGram]
    simp only [scalarMatrix,allowedTwo,weight_label,supportedTwo]
    rfl
  simp_rw [h]
  rw [(labelEquiv e).sum_comp (fun v : Mask 2 =>
    (overlap allowedTwo (labelEquiv e a) v : ℝ))]
  exact_mod_cast two_rowGram (labelEquiv e a)

theorem three_gram (e : N ≃ Fin 1) (a : N → Bool) :
    (∑ a' : N → Bool, ∑ b : Mask 4,
      (if supportedThree a b then (1 : ℝ) else 0) *
      (if supportedThree a' b then (1 : ℝ) else 0)) = 16 := by
  have h (u v : N → Bool) :
      (∑ b : Mask 4, (if supportedThree u b then (1 : ℝ) else 0) *
        (if supportedThree v b then (1 : ℝ) else 0)) =
      (overlap allowedThree (labelEquiv e u) (labelEquiv e v) : ℝ) := by
    rw [← scalar_rowGram]
    simp only [scalarMatrix,allowedThree,weight_label,supportedThree]
    rfl
  simp_rw [h]
  rw [(labelEquiv e).sum_comp (fun v : Mask 1 =>
    (overlap allowedThree (labelEquiv e a) v : ℝ))]
  exact_mod_cast three_rowGram (labelEquiv e a)

end AES8.PaperActivityInputCountTransport
