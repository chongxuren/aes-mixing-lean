/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.PaperMDSGram
import Mathlib.Algebra.Field.ZMod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.NormNum

/-!
# The Gram-moment proposition on every finite binary vector space

`PaperMDSGram` proves the structural estimate for an explicitly supplied
nondegenerate character pairing. Here a finite `ZMod 2` module supplies that
pairing through a chosen basis, so the paper-facing statements have no pairing
existence or exponent-two proof premise. `basisPairing` also permits any given
finite basis. The real kernels, MDS code, coordinate count and dimension remain
arbitrary. Literal Euclidean squared norms are connected to the coordinate
energy and Gram diagonals by proved identities.

This module supplements the frozen structural module; it does not alter that
module, the manuscript, or predecessor sources. Constructive proof development
only; no attacks or numerical AES assumptions.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperMDSBinary

open AESMixing AESConcrete.MixedCodeMoment AES8.PaperMDSGram

attribute [local instance] Classical.propDecidable

/-- The standard real sign pairing of the one-dimensional binary space. -/
def bitPairing : CharacterPairing (ZMod 2) where
  value x y := if x * y = 0 then 1 else -1
  zero_right x := by simp
  add_right x y z := by
    have hcases (a : ZMod 2) : a = 0 ∨ a = 1 := by
      change (a : Fin 2) = 0 ∨ (a : Fin 2) = 1
      have hlt : (a : Fin 2).val < 2 := (a : Fin 2).isLt
      have hv : (a : Fin 2).val = 0 ∨ (a : Fin 2).val = 1 := by omega
      rcases hv with hv | hv
      · exact Or.inl (Fin.ext hv)
      · exact Or.inr (Fin.ext hv)
    have hone : (1 : ZMod 2) + 1 = 0 := ZModModule.add_self 1
    rcases hcases x with rfl | rfl <;>
      rcases hcases y with rfl | rfl <;>
      rcases hcases z with rfl | rfl <;>
      simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, hone] <;>
      norm_num
  symmetric x y := by rw [mul_comm]
  nondegenerate x hx := by
    refine ⟨1, ?_⟩
    norm_num [hx]

/-- Pull a character pairing back along an actual additive equivalence. The
nondegeneracy witness is transported by its inverse, rather than assumed. -/
def pairingComapEquiv {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (e : X ≃+ Y) (B : CharacterPairing Y) : CharacterPairing X where
  value x y := B.value (e x) (e y)
  zero_right x := by rw [map_zero, B.zero_right]
  add_right x y z := by rw [map_add, B.add_right]
  symmetric x y := B.symmetric (e x) (e y)
  nondegenerate x hx := by
    have hex : e x ≠ 0 := by
      intro h
      apply hx
      apply e.injective
      simpa only [map_zero] using h
    obtain ⟨y, hy⟩ := B.nondegenerate (e x) hex
    refine ⟨e.symm y, ?_⟩
    simpa only [e.apply_symm_apply] using hy

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The standard binary dot-product sign pairing in any specified finite
basis. The product pairing's nondegeneracy is already proved in AESMixing. -/
def basisPairing {I : Type*} [Fintype I] [DecidableEq I]
    (b : Module.Basis I (ZMod 2) V) : CharacterPairing V :=
  pairingComapEquiv b.equivFun.toAddEquiv (bitPairing.product I)

/-- A finite binary vector space has a character pairing without an existence
premise: choose its finite basis and pull back the coordinate sign pairing.
`Module.Finite` follows from the existing `Fintype V` instance. -/
def binaryPairing (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] :
    CharacterPairing V :=
  basisPairing (Module.finBasis (ZMod 2) V)

/-- The exponent-two law follows from the binary scalar action. -/
theorem binary_add_self (x : V) : x + x = 0 := ZModModule.add_self x

variable {K : Type*} [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

/-- The arbitrary mixed-map trace statement on a finite binary vector space.
Only the Fourier-oriented column cap is conditional on the high-dimensional
branch; the pairing and exponent-two law are constructed here. -/
theorem paper_mixed_binary_mds_gram_bound_trace
    (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < Fintype.card K) (hMDS : IsMDS C k)
    (τ δ : ℝ)
    (hmoment : ∀ i, Matrix.trace ((Matrix.transpose (Matrix.of (T i)) * Matrix.of (T i)) ^ 2) ≤ τ ^ 2)
    (hdiag : ∀ i a, gram (T i) a a ≤ δ)
    (hfourier : Fintype.card K < 2 * k →
      ∀ i a, gram (fourierConjugate (binaryPairing V) (T i)) a a ≤ δ) :
    (∑ y : K → V, action (coordinateKernel T) (unitSubgroupIndicator C) y ^ 2) ≤
      (τ ^ 2 / (Fintype.card V : ℝ)) ^ min k (Fintype.card K - k) *
        δ ^ (Fintype.card K - 2 * min k (Fintype.card K - k)) :=
  paper_mixed_mds_gram_bound_trace (binaryPairing V) binary_add_self
    T C k hk0 hkn hMDS τ δ hmoment hdiag hfourier

/-- The homogeneous trace statement, with the moment parameter defined by the
paper's square root. No character-pairing or exponent-two premise remains. -/
theorem paper_binary_mds_gram_bound
    (T : V → V → ℝ) (C : AddSubgroup (K → V)) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < Fintype.card K) (hMDS : IsMDS C k)
    (δ : ℝ) (hdiag : ∀ a, gram T a a ≤ δ)
    (hfourier : Fintype.card K < 2 * k →
      ∀ a, gram (fourierConjugate (binaryPairing V) T) a a ≤ δ) :
    let τ := Real.sqrt (Matrix.trace ((Matrix.transpose (Matrix.of T) * Matrix.of T) ^ 2))
    (∑ y : K → V,
      action (coordinateKernel (fun _ : K => T)) (unitSubgroupIndicator C) y ^ 2) ≤
      (τ ^ 2 / (Fintype.card V : ℝ)) ^ min k (Fintype.card K - k) *
        δ ^ (Fintype.card K - 2 * min k (Fintype.card K - k)) :=
  paper_mds_gram_bound (binaryPairing V) binary_add_self
    T C k hk0 hkn hMDS δ hdiag hfourier

/-- The Gram diagonal is literally the Euclidean squared norm of a column. -/
theorem gram_diagonal_eq_column_norm_sq (T : V → V → ℝ) (a : V) :
    gram T a a = ‖(WithLp.toLp 2 (fun z => T z a) : EuclideanSpace ℝ V)‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [gram, pow_two]

/-- Proposition 2's mixed-map clause with literal squared Euclidean norms for
both column hypotheses and the output. -/
theorem paper_mixed_binary_mds_norm_bound
    (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < Fintype.card K) (hMDS : IsMDS C k)
    (τ δ : ℝ)
    (hmoment : ∀ i, Matrix.trace ((Matrix.transpose (Matrix.of (T i)) * Matrix.of (T i)) ^ 2) ≤ τ ^ 2)
    (hcolumn : ∀ i a,
      ‖(WithLp.toLp 2 (fun z => T i z a) : EuclideanSpace ℝ V)‖ ^ 2 ≤ δ)
    (hfourier : Fintype.card K < 2 * k → ∀ i a,
      ‖(WithLp.toLp 2 (fun z => fourierConjugate (binaryPairing V) (T i) z a) :
        EuclideanSpace ℝ V)‖ ^ 2 ≤ δ) :
    ‖(WithLp.toLp 2 (action (coordinateKernel T) (unitSubgroupIndicator C)) :
      EuclideanSpace ℝ (K → V))‖ ^ 2 ≤
      (τ ^ 2 / (Fintype.card V : ℝ)) ^ min k (Fintype.card K - k) *
        δ ^ (Fintype.card K - 2 * min k (Fintype.card K - k)) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply paper_mixed_binary_mds_gram_bound_trace T C k hk0 hkn hMDS τ δ hmoment
  · intro i a
    rw [gram_diagonal_eq_column_norm_sq]
    exact hcolumn i a
  · intro h i a
    rw [gram_diagonal_eq_column_norm_sq]
    exact hfourier h i a

/-- The homogeneous proposition exactly in squared-norm form, with its second
Gram moment expressed as a trace. -/
theorem paper_binary_mds_norm_bound
    (T : V → V → ℝ) (C : AddSubgroup (K → V)) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < Fintype.card K) (hMDS : IsMDS C k)
    (δ : ℝ)
    (hcolumn : ∀ a,
      ‖(WithLp.toLp 2 (fun z => T z a) : EuclideanSpace ℝ V)‖ ^ 2 ≤ δ)
    (hfourier : Fintype.card K < 2 * k → ∀ a,
      ‖(WithLp.toLp 2 (fun z => fourierConjugate (binaryPairing V) T z a) :
        EuclideanSpace ℝ V)‖ ^ 2 ≤ δ) :
    let τ := Real.sqrt (Matrix.trace ((Matrix.transpose (Matrix.of T) * Matrix.of T) ^ 2))
    ‖(WithLp.toLp 2
      (action (coordinateKernel (fun _ : K => T)) (unitSubgroupIndicator C)) :
      EuclideanSpace ℝ (K → V))‖ ^ 2 ≤
      (τ ^ 2 / (Fintype.card V : ℝ)) ^ min k (Fintype.card K - k) *
        δ ^ (Fintype.card K - 2 * min k (Fintype.card K - k)) := by
  dsimp only
  rw [EuclideanSpace.real_norm_sq_eq]
  apply paper_binary_mds_gram_bound T C k hk0 hkn hMDS δ
  · intro a
    rw [gram_diagonal_eq_column_norm_sq]
    exact hcolumn a
  · intro h a
    rw [gram_diagonal_eq_column_norm_sq]
    exact hfourier h a

end AES8.PaperMDSBinary
