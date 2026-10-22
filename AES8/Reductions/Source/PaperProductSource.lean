import AES8.Reductions.Support.PaperFixedSupportBlockLift
import AESConcrete.WordColumnBounds

/-! Fixed-support source lengths for products of pointed channel columns.
The product hypothesis is used only at the fixed initial input. No later
signed joint distribution is assumed to factor. All norms use counting measure. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperProductSource
open AESMixing PaperSupportProjection PaperFixedSupportBlockLift
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

def source (K : V → V → ℝ) (a : Fin n → V) (x : Fin n → V) : ℝ :=
  ∏ k, K (x k) (a k)

theorem average_column (z : V) (K : V → V → ℝ)
    (hK : PointedBistochastic K z) (a : V) :
    wordAverage z (fun x => K x a) = fun x => activityMatrix z x a := by
  funext x
  by_cases hx : x = z <;> by_cases ha : a = z <;>
    simp [wordAverage, nonzeroMean, hK.column_sum, hK.zero_row,
      activityMatrix, hx, ha]

theorem residual_column (z : V) (K : V → V → ℝ)
    (hK : PointedBistochastic K z) (a : V) :
    action (residualProjection z) (fun x => K x a) =
      fun x => residualMatrix K z x a := by
  rw [residualProjection_action]
  unfold wordResidual
  rw [average_column z K hK a]
  rfl

theorem constant_column (z : V) (K : V → V → ℝ)
    (hK : PointedBistochastic K z) (a : V) (ha : a ≠ z) :
    action (constantMatrix z) (fun x => K x a) =
      fun x => activityMatrix z x a := by
  rw [constantMatrix_action, average_column z K hK a]
  funext x
  simp [zeroPart, hK.zero_row, ha]

theorem raw_source (z : V) (K : V → V → ℝ) (a : Fin n → V)
    (p : Label n) (x : Fin n → V) :
    raw z p (source K a) x =
      ∏ k, action (supportPiece z (p.1 k) (p.2 k)) (fun v => K v (a k)) (x k) := by
  unfold raw source action supportProduct
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun k v =>
    supportPiece z (p.1 k) (p.2 k) (x k) v * K v (a k))).symm

theorem raw_source_energy (z : V) (K : V → V → ℝ) (a : Fin n → V)
    (p : Label n) :
    (∑ x, raw z p (source K a) x ^ 2) =
      ∏ k, ∑ v, action (supportPiece z (p.1 k) (p.2 k))
        (fun y => K y (a k)) v ^ 2 := by
  simp_rw [raw_source, ← Finset.prod_pow]
  exact (Fintype.prod_sum (fun k v =>
    action (supportPiece z (p.1 k) (p.2 k)) (fun y => K y (a k)) v ^ 2)).symm

theorem product_counts (p : Label n) (hp : Valid p) (E c : ℝ) :
    (∏ k, if p.1 k = true then E else if p.2 k = true then 1 else c) =
      E ^ residualCount p.1 * c ^ (supportCount p.2 - residualCount p.1) := by
  have hsub : (Finset.univ.filter fun k => p.1 k = true) ⊆
      (Finset.univ.filter fun k => p.2 k = false) := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp k (Finset.mem_filter.mp hk).2⟩
  have hset : ((Finset.univ.filter fun k => ¬ p.1 k = true).filter
      fun k => ¬ p.2 k = true) =
      (Finset.univ.filter fun k => p.2 k = false) \
        (Finset.univ.filter fun k => p.1 k = true) := by
    ext k
    cases h₁ : p.1 k <;> cases h₂ : p.2 k <;> simp [h₁, h₂]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_ite,
    Finset.prod_const_one, one_mul, Finset.prod_const, hset,
    Finset.card_sdiff_of_subset hsub]
  rfl

theorem raw_source_energy_le (z : V) (hq : 1 < Fintype.card V)
    (K : V → V → ℝ) (hK : PointedBistochastic K z) (a : Fin n → V)
    (p : Label n) (hp : Valid p) (hs : ∀ k, a k = z ↔ p.2 k = true)
    (E : ℝ) (hE : 0 ≤ E)
    (hcol : ∀ b, b ≠ z → (∑ v, residualMatrix K z v b ^ 2) ≤ E) :
    (∑ x, raw z p (source K a) x ^ 2) ≤
      E ^ residualCount p.1 *
        (1 / (Fintype.card V - 1 : ℝ)) ^ (supportCount p.2 - residualCount p.1) := by
  rw [raw_source_energy, ← product_counts p hp]
  apply Finset.prod_le_prod
  · intro k _
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · intro k _
    cases hr : p.1 k with
    | false =>
      cases ht : p.2 k with
      | false =>
        have ha : a k ≠ z := by simpa [ht] using hs k
        simp only [hr, ht, Bool.false_eq_true, if_false, supportPiece]
        rw [constant_column z K hK _ ha, AESConcrete.activity_column_energy_exact z hq _ ha]
      | true =>
        have ha := (hs k).mpr ht
        simp only [hr, ht, Bool.false_eq_true, if_false, if_true, supportPiece]
        rw [zeroMatrix_action]
        simp [zeroPart, ha, hK.zero_column]
    | true =>
      have ht := hp k hr
      have ha : a k ≠ z := by simpa [ht] using hs k
      simp only [hr, ht, if_true, Bool.false_eq_true, if_false, supportPiece]
      rw [residual_column z K hK]
      exact hcol _ ha

theorem fixed_source_energy_le (z : V) (hq : 1 < Fintype.card V)
    (K : V → V → ℝ) (hK : PointedBistochastic K z) (a : Fin n → V)
    (j : ℕ) (s : Fin n → Bool) (hs : ∀ k, a k = z ↔ s k = true)
    (E : ℝ) (hE : 0 ≤ E)
    (hcol : ∀ b, b ≠ z → (∑ v, residualMatrix K z v b ^ 2) ≤ E) :
    (∑ x, fixedComponent z (source K a) j s x ^ 2) ≤
      (Fintype.card (FixedLabel j s) : ℝ) * E ^ j *
        (1 / (Fintype.card V - 1 : ℝ)) ^ (supportCount s - j) := by
  unfold fixedComponent
  rw [orthogonal_family_energy _ (fun r u h => raw_orthogonal z hq _ _
    (fun he => h (Subtype.ext (Prod.mk.inj he).1)) _ _)]
  calc
    _ ≤ ∑ _r : FixedLabel j s, E ^ j *
        (1 / (Fintype.card V - 1 : ℝ)) ^ (supportCount s - j) := by
      apply Finset.sum_le_sum
      intro r _
      simpa only [r.property.2] using
        raw_source_energy_le z hq K hK a (r.val,s) r.property.1 hs E hE hcol
    _ = _ := by simp [mul_assoc]

theorem four_word_norm_le (z : V) (hq : 1 < Fintype.card V)
    (K : V → V → ℝ) (hK : PointedBistochastic K z) (a : Fin 4 → V)
    (j : Fin 5) (s : Fin 4 → Bool) (hs : ∀ k, a k = z ↔ s k = true)
    (E : ℝ) (hE : 0 ≤ E)
    (hcol : ∀ b, b ≠ z → (∑ v, residualMatrix K z v b ^ 2) ≤ E) :
    l2 (fixedComponent z (source K a) j.val s) ≤
      Real.sqrt ((Nat.choose (supportCount s) j.val : ℝ) * E ^ j.val *
        (1 / (Fintype.card V - 1 : ℝ)) ^ (supportCount s - j.val)) := by
  apply Real.sqrt_le_sqrt
  simpa only [PaperFixedSupportBlockLift.four_word_count] using
    fixed_source_energy_le z hq K hK a j.val s hs E hE hcol

end AES8.PaperProductSource
