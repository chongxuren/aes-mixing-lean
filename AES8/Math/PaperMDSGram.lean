/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESConcrete.MixedCodeMoment
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Set

/-!
# Generic MDS packaging for the paper's Gram-moment estimate

The target is Proposition 2 (`prop:codes`) in `writing/sections/03-gram.tex`.
`IsMDS C k` says that restriction to every set of `k` physical coordinates is
bijective. The two disjoint information sets used by Cauchy--Schwarz are derived
from cardinality, rather than imposed as separate analytic hypotheses.

All coordinates and local real kernels are arbitrary. The dual branch uses an
abstract nondegenerate `CharacterPairing` on an exponent-two finite abelian
group, including the finite binary vector spaces in the paper. This module
contains no AES numerical instantiation. Constructive proof development only;
no attacks, manuscript edits, or predecessor edits.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperMDSGram

open AESMixing AESConcrete.MixedCodeMoment

attribute [local instance] Classical.propDecidable

variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The additive MDS property: each `k`-coordinate restriction is bijective.
The coordinate predicate describes a physical subset, with no ordering chosen. -/
def IsMDS (C : AddSubgroup (K → V)) (k : ℕ) : Prop :=
  ∀ p : K → Prop, Nat.card {i : K // p i} = k →
    Function.Bijective (subgroupRestriction C p)

/-- A bijective restriction to a coordinate set is also bijective when that
set is enumerated by any injective ordered list of length `k`. -/
theorem restriction_bijective_of_embedding (C : AddSubgroup (K → V)) (k : ℕ)
    (hMDS : IsMDS C k) (f : Fin k ↪ K) :
    Function.Bijective (fun c : C => fun i : Fin k => c.val (f i)) := by
  let e : Fin k ≃ Set.range (f : Fin k → K) := Equiv.ofInjective f f.injective
  have hcard : Nat.card (Set.range (f : Fin k → K)) = k := by
    calc
      _ = Nat.card (Fin k) := Nat.card_congr e.symm
      _ = k := by simp
  have hr := hMDS (fun x => x ∈ Set.range (f : Fin k → K)) hcard
  constructor
  · intro c d h
    apply hr.injective
    funext x
    obtain ⟨i, rfl⟩ := e.surjective x
    exact congrFun h i
  · intro v
    obtain ⟨c, hc⟩ := hr.surjective (fun x => v (e.symm x))
    refine ⟨c, ?_⟩
    funext i
    have hi := congrFun hc (e i)
    change c.val (f i) = v (e.symm (e i)) at hi
    simpa using hi

/-- Complementary information sets give the full dual MDS property. -/
theorem annihilator_isMDS (B : CharacterPairing V) (C : AddSubgroup (K → V))
    (k : ℕ) (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k) :
    IsMDS ((B.product K).annihilator C) (Fintype.card K - k) := by
  intro p hp
  have hp' : Fintype.card {i : K // p i} = Fintype.card K - k := by
    simpa only [Nat.card_eq_fintype_card] using hp
  have hcomp : Nat.card {i : K // ¬ p i} = k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, hp']
    omega
  have hd := dual_restriction_bijective B C (fun i => ¬ p i)
    (hMDS (fun i => ¬ p i) hcomp)
  have hpnot : (fun i : K => ¬ ¬ p i) = p := by
    funext i
    exact propext not_not
  rw [hpnot] at hd
  exact hd

/-- A coordinate split exists whenever two blocks of `k` coordinates fit.
This equivalence chooses both disjoint information sets and their remainder. -/
def coordinateSplit (k : ℕ) (hfit : 2 * k ≤ Fintype.card K) :
    CodePosition (Fin k) (Fin (Fintype.card K - 2 * k)) ≃ K :=
  Fintype.equivOfCardEq (by
    simp only [CodePosition, Fintype.card_sum, Fintype.card_fin]
    omega)

theorem split_restrictions_bijective {R : Type*}
    (C : AddSubgroup (K → V)) (k : ℕ) (hMDS : IsMDS C k)
    (idx : CodePosition (Fin k) R ≃ K) :
    Function.Bijective (fun c : C => fun i : Fin k => c.val (idx (Sum.inl i))) ∧
    Function.Bijective (fun c : C => fun i : Fin k =>
      c.val (idx (Sum.inr (Sum.inl i)))) := by
  constructor
  · exact restriction_bijective_of_embedding C k hMDS
      ⟨fun i => idx (Sum.inl i), fun i j h => Sum.inl.inj (idx.injective h)⟩
  · exact restriction_bijective_of_embedding C k hMDS
      ⟨fun i => idx (Sum.inr (Sum.inl i)),
        fun i j h => Sum.inl.inj (Sum.inr.inj (idx.injective h))⟩

/-- Mixed-map low-dimensional estimate with both information sets constructed
from the MDS property and `2k ≤ n`. -/
theorem mds_mixed_energy_low (T : K → V → V → ℝ) (C : AddSubgroup (K → V))
    (k : ℕ) (hfit : 2 * k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (s δ : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (hmoment : ∀ i, (∑ ab : V × V, gram (T i) ab.1 ab.2 ^ 2) ≤ s)
    (hdiag : ∀ i a, gram (T i) a a ≤ δ) :
    (∑ y : K → V, action (coordinateKernel T) (unitSubgroupIndicator C) y ^ 2) ≤
      (s / (Fintype.card V : ℝ)) ^ k * δ ^ (Fintype.card K - 2 * k) := by
  let idx := coordinateSplit (K := K) k hfit
  obtain ⟨he, hf⟩ := split_restrictions_bijective C k hMDS idx
  simpa only [Fintype.card_fin] using
    subgroup_energy_le T C idx he hf s δ hs hδ hmoment hdiag

/-- The high-dimensional branch constructs information sets on the actual
annihilator. Its local second moments come from Fourier invariance. -/
theorem mds_mixed_energy_dual (B : CharacterPairing V) (hchar : ∀ x : V, x + x = 0)
    (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hfit : 2 * (Fintype.card K - k) ≤ Fintype.card K)
    (hMDS : IsMDS C k) (s δ : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (hmoment : ∀ i, (∑ ab : V × V, gram (T i) ab.1 ab.2 ^ 2) ≤ s)
    (hdiag : ∀ i a, gram (fourierConjugate B (T i)) a a ≤ δ) :
    (∑ y : K → V, action (coordinateKernel T) (unitSubgroupIndicator C) y ^ 2) ≤
      (s / (Fintype.card V : ℝ)) ^ (Fintype.card K - k) *
        δ ^ (Fintype.card K - 2 * (Fintype.card K - k)) := by
  let idx := coordinateSplit (K := K) (Fintype.card K - k) hfit
  have hdual := annihilator_isMDS B C k hk hMDS
  obtain ⟨he, hf⟩ := split_restrictions_bijective
    ((B.product K).annihilator C) (Fintype.card K - k) hdual idx
  simpa only [Fintype.card_fin] using
    subgroup_energy_dual_le B hchar T C idx he hf s δ hs hδ hmoment hdiag

/-- Generic min-dimension formula. Fourier-oriented diagonal bounds are
required only in the high-dimensional branch `n < 2k`. -/
theorem mds_mixed_energy_min (B : CharacterPairing V) (hchar : ∀ x : V, x + x = 0)
    (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) (k : ℕ)
    (hk : k ≤ Fintype.card K) (hMDS : IsMDS C k)
    (s δ : ℝ) (hs : 0 ≤ s) (hδ : 0 ≤ δ)
    (hmoment : ∀ i, (∑ ab : V × V, gram (T i) ab.1 ab.2 ^ 2) ≤ s)
    (hdiag : ∀ i a, gram (T i) a a ≤ δ)
    (hfourier : Fintype.card K < 2 * k →
      ∀ i a, gram (fourierConjugate B (T i)) a a ≤ δ) :
    (∑ y : K → V, action (coordinateKernel T) (unitSubgroupIndicator C) y ^ 2) ≤
      (s / (Fintype.card V : ℝ)) ^ min k (Fintype.card K - k) *
        δ ^ (Fintype.card K - 2 * min k (Fintype.card K - k)) := by
  by_cases hlow : 2 * k ≤ Fintype.card K
  · have hmin : min k (Fintype.card K - k) = k := Nat.min_eq_left (by omega)
    simpa only [hmin] using mds_mixed_energy_low T C k hlow hMDS s δ hs hδ hmoment hdiag
  · have hhigh : Fintype.card K < 2 * k := by omega
    have hfit : 2 * (Fintype.card K - k) ≤ Fintype.card K := by omega
    have hmin : min k (Fintype.card K - k) = Fintype.card K - k :=
      Nat.min_eq_right (by omega)
    simpa only [hmin] using
      mds_mixed_energy_dual B hchar T C k hk hfit hMDS s δ hs hδ hmoment
        (hfourier hhigh)

/-- Proposition 2 (`prop:codes`), in its arbitrary mixed-map form. `τ²` bounds
the second Gram moment of each leg. Nonnegativity of `δ` is derived from the
stated diagonal bound; it is not an extra premise. -/
theorem paper_mixed_mds_gram_bound
    (B : CharacterPairing V) (hchar : ∀ x : V, x + x = 0)
    (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < Fintype.card K) (hMDS : IsMDS C k)
    (τ δ : ℝ)
    (hmoment : ∀ i, (∑ ab : V × V, gram (T i) ab.1 ab.2 ^ 2) ≤ τ ^ 2)
    (hdiag : ∀ i a, gram (T i) a a ≤ δ)
    (hfourier : Fintype.card K < 2 * k →
      ∀ i a, gram (fourierConjugate B (T i)) a a ≤ δ) :
    (∑ y : K → V, action (coordinateKernel T) (unitSubgroupIndicator C) y ^ 2) ≤
      (τ ^ 2 / (Fintype.card V : ℝ)) ^ min k (Fintype.card K - k) *
        δ ^ (Fintype.card K - 2 * min k (Fintype.card K - k)) := by
  have hK : Nonempty K := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨i⟩ := hK
  have hδ : 0 ≤ δ := (gram_diagonal_nonneg (T i) (0 : V)).trans (hdiag i 0)
  exact mds_mixed_energy_min B hchar T C k (Nat.le_of_lt hkn) hMDS
    (τ ^ 2) δ (sq_nonneg τ) hδ hmoment hdiag hfourier

/-- The entrywise Gram definition is the matrix `Tᵀ T` over real scalars.
`Matrix.of` keeps multiplication at the matrix instances rather than the
pointwise function instances; the pinned mathlib has no `Matrix.mul` constant. -/
theorem gram_matrix_eq_transpose_mul (T : V → V → ℝ) :
    Matrix.of (gram T) = Matrix.transpose (Matrix.of T) * Matrix.of T := by
  funext a b
  rfl

/-- The finite sum of squared Gram entries is exactly the paper's second Gram
moment `Tr((Tᵀ T)²)`. Symmetry, rather than an extra matrix premise, supplies
the reversed entry in the trace expansion. -/
theorem gram_second_moment_eq_trace (T : V → V → ℝ) :
    (∑ ab : V × V, gram T ab.1 ab.2 ^ 2) =
      Matrix.trace ((Matrix.transpose (Matrix.of T) * Matrix.of T) ^ 2) := by
  rw [← gram_matrix_eq_transpose_mul]
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply, Matrix.of_apply,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [gram_symmetric T b a]

/-- The same mixed-map proposition with its moment premise written literally
as the manuscript's trace of the square of `Tᵀ T`. -/
theorem paper_mixed_mds_gram_bound_trace
    (B : CharacterPairing V) (hchar : ∀ x : V, x + x = 0)
    (T : K → V → V → ℝ) (C : AddSubgroup (K → V)) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < Fintype.card K) (hMDS : IsMDS C k)
    (τ δ : ℝ)
    (hmoment : ∀ i, Matrix.trace ((Matrix.transpose (Matrix.of (T i)) * Matrix.of (T i)) ^ 2) ≤ τ ^ 2)
    (hdiag : ∀ i a, gram (T i) a a ≤ δ)
    (hfourier : Fintype.card K < 2 * k →
      ∀ i a, gram (fourierConjugate B (T i)) a a ≤ δ) :
    (∑ y : K → V, action (coordinateKernel T) (unitSubgroupIndicator C) y ^ 2) ≤
      (τ ^ 2 / (Fintype.card V : ℝ)) ^ min k (Fintype.card K - k) *
        δ ^ (Fintype.card K - 2 * min k (Fintype.card K - k)) := by
  apply paper_mixed_mds_gram_bound B hchar T C k hk0 hkn hMDS τ δ _ hdiag hfourier
  intro i
  rw [gram_second_moment_eq_trace]
  exact hmoment i

/-- Homogeneous Proposition 2, with `τ` defined as the square root of the
second Gram moment, exactly as in its first sentence. -/
theorem paper_mds_gram_bound
    (B : CharacterPairing V) (hchar : ∀ x : V, x + x = 0)
    (T : V → V → ℝ) (C : AddSubgroup (K → V)) (k : ℕ)
    (hk0 : 0 < k) (hkn : k < Fintype.card K) (hMDS : IsMDS C k)
    (δ : ℝ) (hdiag : ∀ a, gram T a a ≤ δ)
    (hfourier : Fintype.card K < 2 * k →
      ∀ a, gram (fourierConjugate B T) a a ≤ δ) :
    let τ := Real.sqrt (Matrix.trace ((Matrix.transpose (Matrix.of T) * Matrix.of T) ^ 2))
    (∑ y : K → V,
      action (coordinateKernel (fun _ : K => T)) (unitSubgroupIndicator C) y ^ 2) ≤
      (τ ^ 2 / (Fintype.card V : ℝ)) ^ min k (Fintype.card K - k) *
        δ ^ (Fintype.card K - 2 * min k (Fintype.card K - k)) := by
  dsimp only
  have htrace : 0 ≤ Matrix.trace ((Matrix.transpose (Matrix.of T) * Matrix.of T) ^ 2) := by
    rw [← gram_second_moment_eq_trace]
    exact Finset.sum_nonneg (fun ab _ => sq_nonneg _)
  apply paper_mixed_mds_gram_bound_trace B hchar (fun _ : K => T) C k hk0 hkn hMDS
    (Real.sqrt (Matrix.trace ((Matrix.transpose (Matrix.of T) * Matrix.of T) ^ 2))) δ _
    (fun _ => hdiag) (fun h _ => hfourier h)
  intro _
  exact (Real.sq_sqrt htrace).symm.le

end AES8.PaperMDSGram
