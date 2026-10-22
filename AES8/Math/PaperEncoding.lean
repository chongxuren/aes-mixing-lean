import AES8.Math.PaperEncodingEnergy
import AES8.Math.PaperKernelBounds
import AES8.Math.FiniteCoordinatePartition
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The paper's information-set encoding operator

Frozen source: paper-merged f902bb94fc826983181b1712d7b57cf9cbe22f4d,
writing/sections/03-gram.tex, Lemma `lem:encoding`.
Real scalars and counting-measure Euclidean norms agree with that section.
Local matrices may be rectangular. Pure tensor columns are represented in the
standard product basis by their literal product coefficients.

Responsibilities are separate: `tensorColumn` specifies the tensor embedding;
`encoder` supplies its actual continuous linear operator; `encoding_energy`
proves its all-input energy estimate; `paper_encoding_norm` is the displayed
uniform-cap, real-power operator norm conclusion. No encoded bound is assumed.
Abstract unequal Hilbert codomains require a separate orthonormal-basis transport;
this module states its finite real matrix scope explicitly.
Constructive proof validation only; no attacks or numerical computations.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperEncoding
open AESMixing PaperKernelBounds

variable {K V W : Type*} [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype W]

/-- The actual chosen-coordinate projection of codewords. -/
def informationProjection (C : Finset (K → V)) (s : Finset K)
    (c : C) (i : s) : V := c.val i.val

/-- Bijectivity is required for the literal physical-coordinate projection. -/
def informationEquiv (C : Finset (K → V)) (s : Finset K)
    (hinfo : Function.Bijective (informationProjection C s)) : C ≃ (s → V) :=
  Equiv.ofBijective (informationProjection C s) hinfo

@[simp] theorem informationEquiv_apply (C : Finset (K → V)) (s : Finset K)
    (hinfo : Function.Bijective (informationProjection C s)) (c : C) (i : s) :
    informationEquiv C s hinfo c i = c.val i.val := rfl

/-- Output coordinates are partitioned without changing or averaging entries. -/
def outputSplit (s : Finset K) :
    (K → W) ≃ (s → W) × (↥(Finset.univ \ s) → W) where
  toFun y := (fun i => y i.val, fun j => y j.val)
  invFun p k := if hk : k ∈ s then p.1 ⟨k, hk⟩ else
    p.2 ⟨k, Finset.mem_sdiff.mpr ⟨Finset.mem_univ k, hk⟩⟩
  left_inv y := by
    funext k
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      simp only [dif_pos i.property]
    · funext j
      simp only [dif_neg (Finset.mem_sdiff.mp j.property).2]

theorem prod_split (s : Finset K) (g : K → ℝ) :
    (∏ k, g k) = (∏ i : s, g i.val) * (∏ j : ↥(Finset.univ \ s), g j.val) := by
  simpa using
    FiniteCoordinatePartition.prod_split s Finset.univ (Finset.subset_univ s) g

/-- Standard-basis coordinates of a pure tensor of local column responses. -/
def tensorColumn (A : K → W → V → ℝ) (x : K → V) :
    EuclideanSpace ℝ (K → W) :=
  WithLp.toLp 2 (fun y => ∏ k, A k (y k) (x k))

/-- Restricting the input columns to the code gives the paper's kernel. -/
def encodingKernel (C : Finset (K → V)) (A : K → W → V → ℝ)
    (y : K → W) (c : C) : ℝ := ∏ k, A k (y k) (c.val k)

/-- Actual Euclidean continuous linear operator of the restricted tensor map. -/
def encoder (C : Finset (K → V)) (A : K → W → V → ℝ) :
    EuclideanSpace ℝ C →L[ℝ] EuclideanSpace ℝ (K → W) :=
  kernelOperator (encodingKernel C A)

/-- This is the literal tensor-column sum from the paper, on each coordinate. -/
@[simp] theorem encoder_apply (C : Finset (K → V)) (A : K → W → V → ℝ)
    (f : EuclideanSpace ℝ C) (y : K → W) :
    encoder C A f y = ∑ c : C, f c * tensorColumn A c.val y := by
  change (∑ c : C, (∏ k, A k (y k) (c.val k)) * f c) = _
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

/-- The coordinate formula is an equality of the actual output vectors. -/
theorem encoder_eq_tensor_sum (C : Finset (K → V)) (A : K → W → V → ℝ)
    (f : EuclideanSpace ℝ C) :
    encoder C A f = ∑ c : C, f c • tensorColumn A c.val := by
  ext y
  simp [encoder_apply]

/-- The split kernel is exactly the original physical-coordinate tensor. -/
theorem encodingKernel_split (C : Finset (K → V)) (s : Finset K)
    (hinfo : Function.Bijective (informationProjection C s))
    (A : K → W → V → ℝ) (y : K → W) (c : C) :
    encodingKernel C A y c = PaperEncodingEnergy.kernel
      (informationEquiv C s hinfo) (fun c j => c.val j.val)
      (fun i : s => A i.val) (fun j : ↥(Finset.univ \ s) => A j.val)
      (outputSplit s y) c := by
  exact prod_split s (fun k => A k (y k) (c.val k))

/-- Uniform local energy and column-energy caps imply the encoded energy cap. -/
theorem encoding_energy (C : Finset (K → V)) (s : Finset K)
    (hinfo : Function.Bijective (informationProjection C s))
    (A : K → W → V → ℝ) (ν δ : ℝ)
    (hA : ∀ k g, (∑ y, action (A k) g y ^ 2) ≤ ν ^ 2 * ∑ x, g x ^ 2)
    (hcol : ∀ k x, (∑ y, A k y x ^ 2) ≤ δ) (f : C → ℝ) :
    (∑ y, action (encodingKernel C A) f y ^ 2) ≤
      (ν ^ s.card) ^ 2 * δ ^ (Fintype.card K - s.card) * ∑ c, f c ^ 2 := by
  have ha (y : K → W) : action (encodingKernel C A) f y =
      action (PaperEncodingEnergy.kernel (informationEquiv C s hinfo)
        (fun c j => c.val j.val) (fun i : s => A i.val)
        (fun j : ↥(Finset.univ \ s) => A j.val)) f (outputSplit s y) := by
    unfold action
    simp_rw [encodingKernel_split C s hinfo A]
  simp_rw [ha]
  rw [(outputSplit s).sum_comp (fun y =>
    action (PaperEncodingEnergy.kernel (informationEquiv C s hinfo)
      (fun c j => c.val j.val) (fun i : s => A i.val)
      (fun j : ↥(Finset.univ \ s) => A j.val)) f y ^ 2)]
  have he := PaperEncodingEnergy.encoding_energy (informationEquiv C s hinfo)
    (fun c j => c.val j.val) (fun i : s => A i.val)
    (fun j : ↥(Finset.univ \ s) => A j.val) (fun _ => ν) δ
    (fun i => hA i.val) (fun j => hcol j.val) f
  have hc : Fintype.card ↥(Finset.univ \ s) = Fintype.card K - s.card := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ s),
      Finset.card_univ]
  rw [hc] at he
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_coe] using he

/-- Turn an actual local operator-norm cap into the local energy premise. -/
theorem local_energy_of_norm (A : W → V → ℝ) (ν : ℝ) (hν : 0 ≤ ν)
    (hA : ‖kernelOperator A‖ ≤ ν) (g : V → ℝ) :
    (∑ y, action A g y ^ 2) ≤ ν ^ 2 * ∑ x, g x ^ 2 := by
  let f : EuclideanSpace ℝ V := WithLp.toLp 2 g
  have hn : ‖kernelOperator A f‖ ≤ ν * ‖f‖ :=
    ((kernelOperator A).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg f))
  have hs := (sq_le_sq₀ (norm_nonneg (kernelOperator A f))
    (mul_nonneg hν (norm_nonneg f))).mpr hn
  simpa only [mul_pow, EuclideanSpace.real_norm_sq_eq, kernelOperator_apply,
    kernelAction, action, f] using hs

/-- Literal input basis vector, normalized in counting measure. -/
def basisVector (x : V) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun z => if z = x then 1 else 0)

@[simp] theorem basis_response_apply (A : W → V → ℝ) (x : V) (y : W) :
    kernelOperator A (basisVector x) y = A y x := by
  simp [kernelOperator_apply, kernelAction, basisVector]

/-- The paper's squared norm of a basis response is exactly column energy. -/
theorem basis_response_energy (A : W → V → ℝ) (x : V) :
    ‖kernelOperator A (basisVector x)‖ ^ 2 = ∑ y, A y x ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [basis_response_apply]

/-- Natural square-root powers and real half-exponents agree, also at zero. -/
theorem sqrt_pow_eq_rpow (δ : ℝ) (hδ : 0 ≤ δ) (r : ℕ) :
    Real.sqrt δ ^ r = δ ^ ((r : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hδ]
  congr 1
  ring

/-- Complete paper endpoint on the actual tensor operator. All local inputs
are actual operator and column norms; the information map is literal projection.
The coefficient is the displayed `ν^m δ^((n-m)/2)`, with real subtraction. -/
theorem paper_encoding_norm (C : Finset (K → V)) (s : Finset K)
    (hinfo : Function.Bijective (informationProjection C s))
    (A : K → W → V → ℝ) (ν δ : ℝ) (hν : 0 ≤ ν) (hδ : 0 ≤ δ)
    (hA : ∀ k, ‖kernelOperator (A k)‖ ≤ ν)
    (hcol : ∀ k x, ‖kernelOperator (A k) (basisVector x)‖ ^ 2 ≤ δ) :
    ‖encoder C A‖ ≤ ν ^ s.card *
      δ ^ (((Fintype.card K : ℝ) - (s.card : ℝ)) / 2) := by
  have he : ∀ f : C → ℝ,
      (∑ y, ‖kernelAction (encodingKernel C A) f y‖ ^ 2) ≤
        ((ν ^ s.card) ^ 2 * δ ^ (Fintype.card K - s.card)) * ∑ c, ‖f c‖ ^ 2 := by
    intro f
    simpa only [Real.norm_eq_abs, sq_abs, kernelAction, action] using
      encoding_energy C s hinfo A ν δ
        (fun k => local_energy_of_norm (A k) ν hν (hA k))
        (fun k x => by simpa only [basis_response_energy] using hcol k x) f
  have hs := operator_norm_sq_le_of_energy (encodingKernel C A)
    ((ν ^ s.card) ^ 2 * δ ^ (Fintype.card K - s.card))
    (mul_nonneg (sq_nonneg _) (pow_nonneg hδ _)) he
  have hsqrt : (Real.sqrt δ ^ (Fintype.card K - s.card)) ^ 2 =
      δ ^ (Fintype.card K - s.card) := by
    rw [← pow_mul, Nat.mul_comm (Fintype.card K - s.card) 2, pow_mul,
      Real.sq_sqrt hδ]
  have hn : ‖encoder C A‖ ≤
      ν ^ s.card * Real.sqrt δ ^ (Fintype.card K - s.card) := by
    apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (pow_nonneg hν _) (pow_nonneg (Real.sqrt_nonneg _) _))).mp
    simpa only [encoder, mul_pow, hsqrt] using hs
  rw [sqrt_pow_eq_rpow δ hδ,
    Nat.cast_sub (Finset.card_le_univ s)] at hn
  exact hn

/-- In the paper's nonempty coordinate/alphabet setting, the cap signs are
consequences of the actual local bounds and need not be extra assumptions. -/
theorem paper_encoding_norm_of_nonempty [Nonempty K] [Nonempty V]
    (C : Finset (K → V)) (s : Finset K)
    (hinfo : Function.Bijective (informationProjection C s))
    (A : K → W → V → ℝ) (ν δ : ℝ)
    (hA : ∀ k, ‖kernelOperator (A k)‖ ≤ ν)
    (hcol : ∀ k x, ‖kernelOperator (A k) (basisVector x)‖ ^ 2 ≤ δ) :
    ‖encoder C A‖ ≤ ν ^ s.card *
      δ ^ (((Fintype.card K : ℝ) - (s.card : ℝ)) / 2) := by
  let k : K := Classical.arbitrary K
  let x : V := Classical.arbitrary V
  exact paper_encoding_norm C s hinfo A ν δ
    ((norm_nonneg _).trans (hA k)) ((sq_nonneg _).trans (hcol k x)) hA hcol

end AES8.PaperEncoding
