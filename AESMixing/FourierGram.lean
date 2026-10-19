import AESMixing.ProductFourier

/-! The second Gram moment is unchanged by normalized Fourier conjugation. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {X : Type*} [AddCommGroup X] [Fintype X]

theorem pairingFourier_inner (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (f g : X → ℝ) :
    (∑ y, action (pairingFourier B) f y * action (pairingFourier B) g y) =
      ∑ x, f x * g x := by
  classical
  rw [kernel_bilinear]
  change (∑ x, ∑ z, f x * g z * gram (pairingFourier B) x z) = _
  simp_rw [pairingFourier_gram B hchar, mul_ite, mul_zero]
  simp

theorem fourierConjugate_gram (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (T : X → X → ℝ) (i j : X) :
    gram (fourierConjugate B T) i j = fourierConjugate B (gram T) i j := by
  change (∑ y,
    action (pairingFourier B) (action T (fun x => pairingFourier B x i)) y *
    action (pairingFourier B) (action T (fun x => pairingFourier B x j)) y) = _
  rw [pairingFourier_inner B hchar, kernel_bilinear]
  unfold fourierConjugate kernelCompose
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [pairingFourier_symmetric B a i]
  unfold gram
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

def frobeniusSq (T : X → X → ℝ) : ℝ := ∑ y, ∑ x, T y x^2

theorem fourier_left_frobenius (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (T : X → X → ℝ) :
    frobeniusSq (kernelCompose (pairingFourier B) T) = frobeniusSq T := by
  unfold frobeniusSq
  rw [Finset.sum_comm]
  have he (x : X) : (∑ y, kernelCompose (pairingFourier B) T y x^2) = ∑ y, T y x^2 :=
    pairingFourier_energy B hchar (fun y => T y x)
  simp_rw [he]
  exact Finset.sum_comm

theorem fourier_right_frobenius (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (T : X → X → ℝ) :
    frobeniusSq (kernelCompose T (pairingFourier B)) = frobeniusSq T := by
  unfold frobeniusSq
  apply Finset.sum_congr rfl
  intro y _
  have he (x : X) : kernelCompose T (pairingFourier B) y x = action (pairingFourier B) (T y) x := by
    unfold kernelCompose action
    apply Finset.sum_congr rfl
    intro z _
    rw [pairingFourier_symmetric B z x, mul_comm]
  simp_rw [he]
  exact pairingFourier_energy B hchar (T y)

theorem fourierConjugate_frobenius (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (T : X → X → ℝ) : frobeniusSq (fourierConjugate B T) = frobeniusSq T := by
  unfold fourierConjugate
  rw [fourier_left_frobenius B hchar, fourier_right_frobenius B hchar]

theorem fourierConjugate_gram_moment (B : CharacterPairing X) (hchar : ∀ x : X, x+x = 0)
    (T : X → X → ℝ) :
    (∑ xy : X × X, gram (fourierConjugate B T) xy.1 xy.2^2) =
      ∑ xy : X × X, gram T xy.1 xy.2^2 := by
  simp_rw [fourierConjugate_gram B hchar]
  simp only [Fintype.sum_prod_type]
  exact fourierConjugate_frobenius B hchar (gram T)

end AESMixing
