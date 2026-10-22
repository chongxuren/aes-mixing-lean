import AES8.Math.PaperRestrictedDiffusionMass
import AES8.Math.PaperSourceMajorization

/-!
# Exact zero-set probabilities and the source quadratic

The source law is the actual normalized product law on original active input
coordinates. Exact zero sets partition this law. The full zero event vanishes
by MDS and nonzero active support, and every nonempty proper event receives
the simple cap proved in `lem:marginals`. These identities connect the paper's
symbolic affine majorization to actual probabilities without renormalization.
Numerical evaluation of the resulting all-caps expression is separate.
-/

noncomputable section
open scoped BigOperators
namespace AES8.PaperSourceZeroEvents
open PaperRestrictedDiffusion PaperMDSGram PaperRestrictedSource
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

def exactZeroSet (L : (I → V) →+ (I → V)) (x : I → V) : Finset I :=
  Finset.univ.filter (fun i => L x i = 0)

@[simp] theorem mem_exactZeroSet (L : (I → V) →+ (I → V)) (x : I → V) (i : I) :
    i ∈ exactZeroSet L x ↔ L x i = 0 := by simp [exactZeroSet]

def exactMass (L : (I → V) →+ (I → V)) (active : Finset I)
    (mu : I → V → ℝ) (zeros : Finset I) : ℝ :=
  ∑ x : I → V, if exactZeroSet L x = zeros then originalLaw active mu x else 0

theorem exactMass_nonneg (L : (I → V) →+ (I → V)) (active zeros : Finset I)
    (mu : I → V → ℝ) (hmu : ∀ i ∈ active, ∀ x, 0 ≤ mu i x) :
    0 ≤ exactMass L active mu zeros := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact originalLaw_nonneg active mu hmu x
  · exact le_rfl

/-- The unique exact zero set gives an actual probability partition. -/
theorem exactMass_sum_one (L : (I → V) →+ (I → V)) (active : Finset I)
    (mu : I → V → ℝ) (hmass : ∀ i ∈ active, (∑ x, mu i x) = 1) :
    (∑ zeros : Finset I, exactMass L active mu zeros) = 1 := by
  unfold exactMass
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact originalLaw_mass_one active mu hmass

/-- Exact events are specified-zero events with the extra restriction retained. -/
theorem exactMass_eq_eventMass (L : (I → V) →+ (I → V)) (active zeros : Finset I)
    (mu : I → V → ℝ) :
    exactMass L active mu zeros =
      eventMass L active zeros mu (fun x => exactZeroSet L x = zeros) := by
  rw [eventMass_eq_originalLaw]
  apply Finset.sum_congr rfl
  intro x _
  have he : (∀ i ∈ zeros, L x i = 0) ∧ exactZeroSet L x = zeros ↔
      exactZeroSet L x = zeros := by
    constructor
    · exact And.right
    · intro hx
      refine ⟨?_, hx⟩
      intro i hi
      exact (mem_exactZeroSet L x i).mp (hx.symm ▸ hi)
  simp only [he]

/-- Full zero output is impossible; this uses the actual MDS diffusion. -/
theorem exactMass_univ_eq_zero (L : (I → V) →+ (I → V))
    (hMDS : IsMDS (graph L) (Fintype.card I)) (active : Finset I)
    (mu : I → V → ℝ) (hzero : ∃ i ∈ active, mu i 0 = 0) :
    exactMass L active mu Finset.univ = 0 := by
  rw [exactMass_eq_eventMass]
  exact actual_event_mass_eq_zero L hMDS active Finset.univ
    (by simpa using Finset.card_le_univ active) mu hzero _

/-- The simple event cap also covers impossible nonempty zero sets. -/
theorem exactMass_le_cap (L : (I → V) →+ (I → V))
    (hMDS : IsMDS (graph L) (Fintype.card I)) (active zeros : Finset I)
    (hz : 0 < zeros.card) (mu : I → V → ℝ) (p rho : ℝ)
    (hrho : 0 ≤ rho) (hrhop : rho ≤ p)
    (hmu : ∀ i ∈ active, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ active, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ active, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ active, (∑ x, mu i x ^ 2) ≤ rho)
    (hzero : ∃ i ∈ active, mu i 0 = 0) :
    exactMass L active mu zeros ≤ p^(zeros.card-1) * rho := by
  rw [exactMass_eq_eventMass]
  by_cases hsmall : zeros.card < active.card
  · simpa only [mul_comm] using actual_event_mass_le_simple L hMDS active zeros hz hsmall
      mu (fun x => exactZeroSet L x = zeros) p rho hrho hrhop hmu hmass hpoint hcollision
  · rw [actual_event_mass_eq_zero L hMDS active zeros (by omega) mu hzero]
    exact mul_nonneg (pow_nonneg (hrho.trans hrhop) _) hrho

/-- The nonempty proper zero sets, used in Section 11. -/
abbrev ProperZeros (I : Type*) [Fintype I] [DecidableEq I] :=
  {z : Finset I // z ≠ ∅ ∧ z ≠ Finset.univ}

/-- Remove the impossible full set and keep the empty event as complement. -/
theorem sum_proper_with_empty (F : Finset I → ℝ) (hfull : F Finset.univ = 0) :
    (∑ z : Finset I, F z) = F ∅ + ∑ z : ProperZeros I, F z.val := by
  have hs : (∑ z : ProperZeros I, F z.val) =
      ∑ z : Finset I, if z ≠ ∅ ∧ z ≠ Finset.univ then F z else 0 :=
    sum_subtype_eq_restriction _ F
  have he (z : Finset I) : F z = (if z = ∅ then F ∅ else 0) +
      (if z ≠ ∅ ∧ z ≠ Finset.univ then F z else 0) := by
    by_cases h0 : z = ∅
    · simp [h0]
    · by_cases hu : z = Finset.univ
      · subst z
        simp [h0, hfull]
      · simp [h0, hu]
  calc
    _ = ∑ z : Finset I, ((if z = ∅ then F ∅ else 0) +
        (if z ≠ ∅ ∧ z ≠ Finset.univ then F z else 0)) :=
      Finset.sum_congr rfl (fun z _ => he z)
    _ = _ := by rw [Finset.sum_add_distrib, ← hs]; simp

/-- The complete symbolic source-activity bound on actual probabilities.
The local laws, MDS property and two scalar base inequalities are the only
premises; no intermediate zero-event or quadratic bound is assumed. -/
theorem actual_source_collision_le (L : (I → V) →+ (I → V))
    (hMDS : IsMDS (graph L) (Fintype.card I)) (active : Finset I)
    (mu : I → V → ℝ) (Q p rho : ℝ) (hQ : 0 ≤ Q)
    (hrho : 0 ≤ rho) (hrhop : rho ≤ p)
    (hmu : ∀ i ∈ active, ∀ x, 0 ≤ mu i x)
    (hmass : ∀ i ∈ active, (∑ x, mu i x) = 1)
    (hpoint : ∀ i ∈ active, ∀ x, mu i x ≤ p)
    (hcollision : ∀ i ∈ active, (∑ x, mu i x ^ 2) ≤ rho)
    (hzero : ∃ i ∈ active, mu i 0 = 0)
    (hbase : 2 < Q*rho) (hgrowth : 1 ≤ Q*p) :
    (∑ z : Finset I, Q^z.card * exactMass L active mu z ^ 2) ≤
      PaperSourceMajorization.quadratic
        (fun z : ProperZeros I => Q^z.val.card)
        (fun z : ProperZeros I => p^(z.val.card-1) * rho) := by
  have hfull := exactMass_univ_eq_zero L hMDS active mu hzero
  have hm : exactMass L active mu ∅ +
      (∑ z : ProperZeros I, exactMass L active mu z.val) = 1 := by
    rw [← sum_proper_with_empty _ hfull]
    exact exactMass_sum_one L active mu hmass
  have hw : (∑ z : Finset I, Q^z.card * exactMass L active mu z ^ 2) =
      exactMass L active mu ∅ ^ 2 + ∑ z : ProperZeros I,
        Q^z.val.card * exactMass L active mu z.val ^ 2 := by
    have he := sum_proper_with_empty
      (fun z : Finset I => Q^z.card * exactMass L active mu z ^ 2)
      (by rw [hfull]; simp)
    simpa only [Finset.card_empty, pow_zero, one_mul] using he
  rw [hw]
  apply PaperSourceMajorization.collision_with_complement _ _ _ _ hm
  · intro z
    exact pow_nonneg hQ _
  · intro z
    exact exactMass_nonneg L active z.val mu hmu
  · intro z
    exact exactMass_le_cap L hMDS active z.val (Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr z.property.1)) mu p rho hrho hrhop hmu hmass
      hpoint hcollision hzero
  · intro z
    exact (PaperSourceMajorization.weighted_geometric_cap_gt_two Q p rho z.val.card
      (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr z.property.1)) hbase hgrowth).le

end AES8.PaperSourceZeroEvents
