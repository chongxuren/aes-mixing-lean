import AESPaper.RectangularBounds
import AESPaper.WeightedEncoding

/-!
# Physical word encodings with a proved information set

An encoding uses one common finite source. The supplied physical position
equivalence separates its core and extra coordinates, and the actual core
restriction must be bijective. The full output tuple is reindexed explicitly
before applying the frozen weighted-encoding theorem. Every source amplitude
is real, signed, arbitrary, and unnormalized. No desired energy bound or
independence between core and extra coordinates is assumed.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordEncodingOperator
open AESMixing AESConcrete AESPaper.RectangularFourier
open AESConcrete.WordFourierVariants (variant)
open AESPaper.WeightedEncoding (nu delta nu_nonnegative delta_nonnegative)

section PhysicalEncoding
variable {C K A J : Type*} [Fintype C] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]

/-- The physical tensor columns of one common source; residual flags retain
their separate adjoint and Fourier roles. -/
def encodingKernel (adjoint fourier : K → Bool) (coord : C → K → AES.Word) :
    (K → AES.Word) → C → ℝ :=
  fun y c => ∏ k : K, variant (adjoint k) (fourier k) (y k) (coord c k)

/-- Exact output-coordinate permutation induced by the physical core split. -/
def outputEquiv (idx : A ⊕ J ≃ K) :
    (A ⊕ J → AES.Word) ≃ (K → AES.Word) where
  toFun y := fun k => y (idx.symm k)
  invFun y := fun p => y (idx p)
  left_inv y := by funext p; exact congrArg y (idx.symm_apply_apply p)
  right_inv y := by funext k; exact congrArg y (idx.apply_symm_apply k)

/-- Only an actual bijective core restriction supplies this equivalence. -/
def coreEquiv (coord : C → K → AES.Word) (idx : A ⊕ J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : A => coord c (idx (Sum.inl i)))) :
    C ≃ (A → AES.Word) := Equiv.ofBijective _ he

/-- Exact identification with WeightedEncoding, including arbitrary signed
source amplitudes and every physical extra coordinate. -/
theorem encoding_reindex (adjoint fourier : K → Bool) (coord : C → K → AES.Word)
    (idx : A ⊕ J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : A => coord c (idx (Sum.inl i))))
    (f : C → ℝ) (y : A ⊕ J → AES.Word) :
    rectAction (encodingKernel adjoint fourier coord) f (outputEquiv idx y) =
      WeightedEncoding.encodingResponse
        (fun i => adjoint (idx (Sum.inl i))) (fun i => fourier (idx (Sum.inl i)))
        (fun j => adjoint (idx (Sum.inr j))) (fun j => fourier (idx (Sum.inr j)))
        (coreEquiv coord idx he) (fun c j => coord c (idx (Sum.inr j))) f y := by
  unfold rectAction encodingKernel WeightedEncoding.encodingResponse
    RestrictedResponseEnergy.splitResponse WordColumnGram.tensorResponse
    WordColumnGram.tensorColumn
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  rw [← idx.prod_comp (fun k =>
    variant (adjoint k) (fourier k) ((outputEquiv idx y) k) (coord c k))]
  apply Finset.prod_congr rfl
  intro p _
  cases p with
  | inl i =>
    change variant (adjoint (idx (Sum.inl i))) (fourier (idx (Sum.inl i)))
        (y (idx.symm (idx (Sum.inl i)))) (coord c (idx (Sum.inl i))) =
      variant (adjoint (idx (Sum.inl i))) (fourier (idx (Sum.inl i)))
        (y (Sum.inl i)) (coord c (idx (Sum.inl i)))
    rw [idx.symm_apply_apply]
  | inr j =>
    change variant (adjoint (idx (Sum.inr j))) (fourier (idx (Sum.inr j)))
        (y (idx.symm (idx (Sum.inr j)))) (coord c (idx (Sum.inr j))) =
      variant (adjoint (idx (Sum.inr j))) (fourier (idx (Sum.inr j)))
        (y (Sum.inr j)) (coord c (idx (Sum.inr j)))
    rw [idx.symm_apply_apply]

/-- Counting-energy bound after an exact physical core/extra reindexing. -/
theorem encoding_energy (adjoint fourier : K → Bool) (coord : C → K → AES.Word)
    (idx : A ⊕ J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : A => coord c (idx (Sum.inl i))))
    (f : C → ℝ) :
    (∑ y : K → AES.Word, rectAction (encodingKernel adjoint fourier coord) f y ^ 2) ≤
      nu ^ (2 * Fintype.card A) * delta ^ Fintype.card J * ∑ c : C, f c ^ 2 := by
  have hs :
      (∑ y : K → AES.Word, rectAction (encodingKernel adjoint fourier coord) f y ^ 2) =
      ∑ y : A ⊕ J → AES.Word,
        WeightedEncoding.encodingResponse
          (fun i => adjoint (idx (Sum.inl i))) (fun i => fourier (idx (Sum.inl i)))
          (fun j => adjoint (idx (Sum.inr j))) (fun j => fourier (idx (Sum.inr j)))
          (coreEquiv coord idx he) (fun c j => coord c (idx (Sum.inr j))) f y ^ 2 := by
    rw [← (outputEquiv idx).sum_comp
      (fun y => rectAction (encodingKernel adjoint fourier coord) f y ^ 2)]
    apply Finset.sum_congr rfl
    intro y _
    rw [encoding_reindex adjoint fourier coord idx he]
  rw [hs]
  exact WeightedEncoding.mixed_encoding_energy _ _ _ _
    (coreEquiv coord idx he) (fun c j => coord c (idx (Sum.inr j))) f

/-- Rectangular operator form of the physical weighted-encoding estimate. -/
theorem encoding_energyBound (adjoint fourier : K → Bool)
    (coord : C → K → AES.Word) (idx : A ⊕ J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : A => coord c (idx (Sum.inl i)))) :
    EnergyBound (encodingKernel adjoint fourier coord)
      (nu ^ Fintype.card A * Real.sqrt (delta ^ Fintype.card J)) := by
  intro f
  have hp : (nu ^ Fintype.card A * Real.sqrt (delta ^ Fintype.card J)) ^ 2 =
      nu ^ (2 * Fintype.card A) * delta ^ Fintype.card J := by
    rw [mul_pow, Real.sq_sqrt (pow_nonneg delta_nonnegative _)]
    rw [← pow_mul, Nat.mul_comm]
  rw [hp]
  exact encoding_energy adjoint fourier coord idx he f

theorem encoding_one_energyBound (adjoint fourier : K → Bool)
    (coord : C → K → AES.Word) (idx : A ⊕ J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : A => coord c (idx (Sum.inl i))))
    (hA : Fintype.card A = 1) :
    EnergyBound (encodingKernel adjoint fourier coord)
      (nu * Real.sqrt (delta ^ Fintype.card J)) := by
  simpa only [hA, pow_one] using encoding_energyBound adjoint fourier coord idx he

/-- Two core coordinates and no extra coordinate. -/
theorem encoding_two_energyBound (adjoint fourier : K → Bool)
    (coord : C → K → AES.Word) (idx : A ⊕ J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : A => coord c (idx (Sum.inl i))))
    (hA : Fintype.card A = 2) (hJ : Fintype.card J = 0) :
    EnergyBound (encodingKernel adjoint fourier coord) (nu ^ 2) := by
  simpa only [hA, hJ, pow_zero, Real.sqrt_one, mul_one] using
    encoding_energyBound adjoint fourier coord idx he

/-- A four-coordinate output with an actual two-coordinate information set.
The whole four-coordinate restriction is not assumed to be bijective. -/
theorem encoding_four_two_energyBound (adjoint fourier : K → Bool)
    (coord : C → K → AES.Word) (idx : A ⊕ J ≃ K)
    (he : Function.Bijective (fun c : C => fun i : A => coord c (idx (Sum.inl i))))
    (hA : Fintype.card A = 2) (hJ : Fintype.card J = 2) :
    EnergyBound (encodingKernel adjoint fourier coord) (nu ^ 2 * delta) := by
  simpa only [hA, hJ, Real.sqrt_sq delta_nonnegative] using
    encoding_energyBound adjoint fourier coord idx he

end PhysicalEncoding
end AESPaper.WordEncodingOperator
