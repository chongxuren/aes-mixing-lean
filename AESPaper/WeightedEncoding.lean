import AESPaper.LocalAES
import AESConcrete.RestrictedResponseEnergy
import AESConcrete.FiniteTensorEnergy
import AESMixing.L2Sums

/-!
# Weighted encodings for the actual AES word residual

The source amplitude is arbitrary, signed and unnormalized. Every leg chooses
its own actual adjoint and whole-word Fourier orientation. The core source
coordinates must form an actual equivalence; extra coordinates are arbitrary
functions of that same source. Thus coordinate relabelings belong to the
explicit information-set and extra-coordinate maps, rather than a symmetry
assumption on the AES channel.

This is the weighted-encoding input to v9 Lemma weighted-encodings. The
cardinality-two consequence only needs one two-coordinate information set;
proving that a particular shortened AES code has that information set remains
the caller's task. No complete boundary-transfer estimate is asserted here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WeightedEncoding
open AESMixing AESConcrete
open AESConcrete.WordFourierVariants (variant)

def nu : ℝ := 21 / 131072
def delta : ℝ := 2 / (15 * (2 : ℝ)^32)

theorem nu_nonnegative : 0 ≤ nu := by norm_num [nu]
theorem delta_nonnegative : 0 ≤ delta := by norm_num [delta]

/-- The accepted local operator resource acts on every signed word vector. -/
theorem local_variant_energy (adjoint fourier : Bool) (f : AES.Word → ℝ) :
    (∑ y, action (variant adjoint fourier) f y ^ 2) ≤
      nu ^ 2 * ∑ x, f x ^ 2 := by
  have hnorm : ‖kernelOperator (variant adjoint fourier)‖ ≤ nu := by
    have h := LocalAES.local_operator_norm adjoint fourier
    have hs : Real.sqrt ((2 : ℝ)^32) = 65536 := by
      rw [show (2 : ℝ)^32 = 65536^2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 65536)]
    simpa only [hs, nu, show (2 : ℝ) * 65536 = 131072 by norm_num] using h
  let v : EuclideanSpace ℝ AES.Word := WithLp.toLp 2 f
  have hn : ‖kernelOperator (variant adjoint fourier) v‖ ≤ nu * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm (kernelOperator (variant adjoint fourier)) v).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  have hs := (sq_le_sq₀ (norm_nonneg (kernelOperator (variant adjoint fourier) v))
    (mul_nonneg nu_nonnegative (norm_nonneg v))).mpr hn
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, kernelOperator_apply, v]
    using hs

/-- Distinct orientations are allowed on all tensor coordinates. -/
theorem mixed_coordinate_energy {I : Type*} [Fintype I] [DecidableEq I]
    (adjoint fourier : I → Bool) (f : (I → AES.Word) → ℝ) :
    (∑ y, action (coordinateKernel (fun i => variant (adjoint i) (fourier i)))
      f y ^ 2) ≤ nu ^ (2 * Fintype.card I) * ∑ x, f x ^ 2 := by
  have h := FiniteTensorEnergy.coordinate_energy
    (fun i => variant (adjoint i) (fourier i)) (fun _ : I => nu)
    (fun i => local_variant_energy (adjoint i) (fourier i)) f
  have hp : (∏ _ : I, nu) ^ 2 = nu ^ (2 * Fintype.card I) := by
    simp only [Finset.prod_const, Finset.card_univ]
    rw [← pow_mul, Nat.mul_comm]
  rw [hp] at h
  exact h

section Encoding

variable {C I J : Type*} [Fintype C] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- An actual whole-word encoding, with explicit core and extra labels. -/
def encodingResponse (coreAdjoint coreFourier : I → Bool)
    (extraAdjoint extraFourier : J → Bool)
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (f : C → ℝ) :
    (I ⊕ J → AES.Word) → ℝ :=
  RestrictedResponseEnergy.splitResponse
    (fun i => variant (coreAdjoint i) (coreFourier i))
    (fun j => variant (extraAdjoint j) (extraFourier j)) e rest f

theorem encodingResponse_apply (coreAdjoint coreFourier : I → Bool)
    (extraAdjoint extraFourier : J → Bool)
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (f : C → ℝ)
    (y : I → AES.Word) (z : J → AES.Word) :
    encodingResponse coreAdjoint coreFourier extraAdjoint extraFourier e rest f
      (Sum.elim y z) =
      ∑ c : C, (∏ i : I, variant (coreAdjoint i) (coreFourier i) (y i) (e c i)) *
        (f c * ∏ j : J, variant (extraAdjoint j) (extraFourier j) (z j) (rest c j)) :=
  RestrictedResponseEnergy.splitResponse_apply _ _ e rest f y z

/-- The information-set estimate retains arbitrary signed source amplitudes. -/
theorem mixed_encoding_energy (coreAdjoint coreFourier : I → Bool)
    (extraAdjoint extraFourier : J → Bool)
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (f : C → ℝ) :
    (∑ y, encodingResponse coreAdjoint coreFourier extraAdjoint extraFourier
      e rest f y ^ 2) ≤
      nu ^ (2 * Fintype.card I) * delta ^ Fintype.card J * ∑ c, f c ^ 2 :=
  RestrictedResponseEnergy.split_response_energy _ _ e rest f
    (nu ^ (2 * Fintype.card I)) delta (pow_nonneg nu_nonnegative _)
    delta_nonnegative (mixed_coordinate_energy coreAdjoint coreFourier)
    (fun j a => (LocalAES.local_column_energy (extraAdjoint j) (extraFourier j) a).le)

/-- Counting-measure square-root norm, with no source normalization. -/
theorem mixed_encoding_norm (coreAdjoint coreFourier : I → Bool)
    (extraAdjoint extraFourier : J → Bool)
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (f : C → ℝ) :
    l2 (encodingResponse coreAdjoint coreFourier extraAdjoint extraFourier e rest f) ≤
      (nu ^ Fintype.card I * Real.sqrt (delta ^ Fintype.card J)) * l2 f := by
  apply l2_le_of_energy _ _ _
    (mul_nonneg (pow_nonneg nu_nonnegative _) (Real.sqrt_nonneg _))
  have hp : (nu ^ Fintype.card I)^2 = nu ^ (2 * Fintype.card I) := by
    rw [← pow_mul, Nat.mul_comm]
  simpa only [mul_pow, hp, Real.sq_sqrt (pow_nonneg delta_nonnegative _)] using
    mixed_encoding_energy coreAdjoint coreFourier extraAdjoint extraFourier e rest f

/-- One core coordinate and any number of extra coordinates. -/
theorem cardinality_one_energy (coreAdjoint coreFourier : I → Bool)
    (extraAdjoint extraFourier : J → Bool)
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (f : C → ℝ)
    (hI : Fintype.card I = 1) :
    (∑ y, encodingResponse coreAdjoint coreFourier extraAdjoint extraFourier
      e rest f y ^ 2) ≤ nu ^ 2 * delta ^ Fintype.card J * ∑ c, f c ^ 2 := by
  simpa only [hI, Nat.mul_one] using
    mixed_encoding_energy coreAdjoint coreFourier extraAdjoint extraFourier e rest f

theorem cardinality_one_norm (coreAdjoint coreFourier : I → Bool)
    (extraAdjoint extraFourier : J → Bool)
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (f : C → ℝ)
    (hI : Fintype.card I = 1) :
    l2 (encodingResponse coreAdjoint coreFourier extraAdjoint extraFourier e rest f) ≤
      (nu * Real.sqrt (delta ^ Fintype.card J)) * l2 f := by
  simpa only [hI, pow_one] using
    mixed_encoding_norm coreAdjoint coreFourier extraAdjoint extraFourier e rest f

/-- The weighted [4,2] coefficient, once the two-coordinate information-set
equivalence has been supplied. No additional MDS hypothesis is needed here. -/
theorem four_two_energy (coreAdjoint coreFourier : I → Bool)
    (extraAdjoint extraFourier : J → Bool)
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (f : C → ℝ)
    (hI : Fintype.card I = 2) (hJ : Fintype.card J = 2) :
    (∑ y, encodingResponse coreAdjoint coreFourier extraAdjoint extraFourier
      e rest f y ^ 2) ≤ nu ^ 4 * delta ^ 2 * ∑ c, f c ^ 2 := by
  simpa only [hI, hJ, show 2 * 2 = (4 : ℕ) by decide] using
    mixed_encoding_energy coreAdjoint coreFourier extraAdjoint extraFourier e rest f

theorem four_two_norm (coreAdjoint coreFourier : I → Bool)
    (extraAdjoint extraFourier : J → Bool)
    (e : C ≃ (I → AES.Word)) (rest : C → J → AES.Word) (f : C → ℝ)
    (hI : Fintype.card I = 2) (hJ : Fintype.card J = 2) :
    l2 (encodingResponse coreAdjoint coreFourier extraAdjoint extraFourier e rest f) ≤
      (nu ^ 2 * delta) * l2 f := by
  simpa only [hI, hJ, Real.sqrt_sq delta_nonnegative] using
    mixed_encoding_norm coreAdjoint coreFourier extraAdjoint extraFourier e rest f

end Encoding

/-- A word relabeling gives the actual one-coordinate information set. -/
def singletonInformationSet (a : AES.Word ≃ AES.Word) :
    AES.Word ≃ (Unit → AES.Word) where
  toFun x _ := a x
  invFun y := a.symm (y ())
  left_inv x := a.symm_apply_apply x
  right_inv y := by
    funext u
    cases u
    exact a.apply_symm_apply (y ())

section Line

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Every line leg uses its specified actual bijective word relabeling. -/
def lineResponse (adjoint fourier : Unit ⊕ J → Bool)
    (a : Unit ⊕ J → AES.Word ≃ AES.Word) (f : AES.Word → ℝ) :
    (Unit ⊕ J → AES.Word) → ℝ :=
  encodingResponse (fun i => adjoint (Sum.inl i)) (fun i => fourier (Sum.inl i))
    (fun j => adjoint (Sum.inr j)) (fun j => fourier (Sum.inr j))
    (singletonInformationSet (a (Sum.inl ()))) (fun x j => a (Sum.inr j) x) f

/-- Exact tensor-column formula for the line operator in the manuscript. -/
theorem lineResponse_apply (adjoint fourier : Unit ⊕ J → Bool)
    (a : Unit ⊕ J → AES.Word ≃ AES.Word) (f : AES.Word → ℝ)
    (y : Unit ⊕ J → AES.Word) :
    lineResponse adjoint fourier a f y =
      ∑ x, f x * ∏ i : Unit ⊕ J, variant (adjoint i) (fourier i) (y i) (a i x) := by
  unfold lineResponse encodingResponse RestrictedResponseEnergy.splitResponse
    WordColumnGram.tensorResponse WordColumnGram.tensorColumn
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases i with
  | inl u => cases u; rfl
  | inr j => rfl

theorem line_energy (adjoint fourier : Unit ⊕ J → Bool)
    (a : Unit ⊕ J → AES.Word ≃ AES.Word) (f : AES.Word → ℝ) :
    (∑ y, lineResponse adjoint fourier a f y ^ 2) ≤
      nu ^ 2 * delta ^ Fintype.card J * ∑ x, f x ^ 2 := by
  exact cardinality_one_energy
    (fun i => adjoint (Sum.inl i)) (fun i => fourier (Sum.inl i))
    (fun j => adjoint (Sum.inr j)) (fun j => fourier (Sum.inr j))
    (singletonInformationSet (a (Sum.inl ()))) (fun x j => a (Sum.inr j) x) f (by simp)

theorem line_norm (adjoint fourier : Unit ⊕ J → Bool)
    (a : Unit ⊕ J → AES.Word ≃ AES.Word) (f : AES.Word → ℝ) :
    l2 (lineResponse adjoint fourier a f) ≤
      (nu * Real.sqrt (delta ^ Fintype.card J)) * l2 f := by
  exact cardinality_one_norm
    (fun i => adjoint (Sum.inl i)) (fun i => fourier (Sum.inl i))
    (fun j => adjoint (Sum.inr j)) (fun j => fourier (Sum.inr j))
    (singletonInformationSet (a (Sum.inl ()))) (fun x j => a (Sum.inr j) x) f (by simp)

end Line
end AESPaper.WeightedEncoding
