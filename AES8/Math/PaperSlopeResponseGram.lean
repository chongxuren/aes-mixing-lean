import AES8.Math.PaperSlopeClassGram

/-! Explicit join from arbitrary actual normalized line responses to the scalar
class Gram. The only geometric data are nonzero slopes and their equality
classes; no physical graph realization or Gram bound is an assumption. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopeResponseGram
open PaperSlopeCoincidences PaperSymbolicSlopeTable PaperSlopeCoincidenceMatrix
open PaperSlopeOutputFrame PaperSlopeLineGram PaperSlopeClassGram
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def responseGram (a : Fin 6 → Fin 20 → F) (u : Interior → ℝ) : ℝ :=
  ∑ p : Fin 6, ∑ k : Fin 20, ∑ l : Fin 20,
    u (inputIndex p k)*u (inputIndex p l)*(256/255 : ℝ)^2 *
      (1/16 : ℝ)^outputDistance p k l *
      ∑ y : F × F, response (a p k) y * response (a p l) y

theorem scaled_response_inner (hq : Fintype.card F = 256) (a b : F)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (256 : ℝ)^2 * (∑ y : F × F, response a y * response b y) =
      (255/256 : ℝ)*(if a=b then 1 else 0)-1/256 := by
  have h := scaled_inner a b ha hb
  rw [hq] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem responseGram_eq (hq : Fintype.card F = 256)
    (a : Fin 6 → Fin 20 → F) (ha : ∀ p k, a p k ≠ 0)
    (hclass : ∀ p k l, a p k = a p l ↔ slopeClass (pairType p) k = slopeClass (pairType p) l)
    (u : Interior → ℝ) :
    (256 : ℝ)^2 * responseGram a u = scaledGram u := by
  unfold responseGram scaledGram
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  have h := scaled_response_inner hq (a p k) (a p l) (ha p k) (ha p l)
  simp only [hclass p k l] at h
  calc
    _ = u (inputIndex p k)*u (inputIndex p l)*(256/255 : ℝ)^2 *
        (1/16 : ℝ)^outputDistance p k l *
        ((256 : ℝ)^2 * ∑ y : F × F, response (a p k) y * response (a p l) y) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by rw [h]

theorem responseGram_le (hq : Fintype.card F = 256)
    (a : Fin 6 → Fin 20 → F) (ha : ∀ p k, a p k ≠ 0)
    (hclass : ∀ p k l, a p k = a p l ↔ slopeClass (pairType p) k = slopeClass (pairType p) l)
    (u : Interior → ℝ) :
    (256 : ℝ)^2 * responseGram a u ≤ (256/255 : ℝ) *
      (∑ A : Interior, ∑ B : Interior, u A*u B*matrix (1/16) A B) := by
  rw [responseGram_eq hq a ha hclass]
  exact scaledGram_le u

end AES8.PaperSlopeResponseGram
