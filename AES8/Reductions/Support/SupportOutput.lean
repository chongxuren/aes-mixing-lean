/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Historical.Output
import AES8.Model.SupportProfile
import AESPaper.RareActivity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset

/-!
# Support-sensitive conversion of the actual fourteen-component profile

All norms use counting measure. The support counts below use a union of
coordinate subspaces, so they do not enumerate AES words or states. The
orthogonal all-active residual components are added before Cauchy--Schwarz.
The all-active activity coordinate is removed by the zero-mass argument.

Constructive proof work only. This module supplies no initialization or
recurrence bound, and makes no cryptanalytic experiment.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
-- The naming linter unfolds concrete AES finite-set terms beyond its limit.
-- This disables only that linter; all declarations remain kernel checked.
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.SupportOutput
open AESMixing AESMixing.AES
open AESPaper.RareActivity

/-- The paper's output functional on unscaled physical profile lengths. -/
def psi (v : AES8.Profile) : ℝ :=
  2 * (v 0 / 2 ^ (47 : ℕ) + 5 * v 1 / 2 ^ (33 : ℕ) +
      v 2 / 2 ^ (15 : ℕ)) +
    v 4 / 2 ^ (47 : ℕ) +
    5 * (v 5 + v 8) / 2 ^ (33 : ℕ) +
    (v 6 + v 9 + v 11) / 2 ^ (15 : ℕ) +
    Real.sqrt ((v 7) ^ 2 + (v 10) ^ 2 + (v 12) ^ 2 + (v 13) ^ 2)

theorem psi_physical (z : AES8.Profile) : psi (AES8.physical z) = AES8.Phi z := by
  rfl

theorem psi_scale (a : ℝ) (v : AES8.Profile) (ha : 0 ≤ a) :
    psi (AES8.scale a v) = a * psi v := by
  have he : (a * v 7) ^ 2 + (a * v 10) ^ 2 + (a * v 12) ^ 2 +
      (a * v 13) ^ 2 = a ^ 2 *
        ((v 7) ^ 2 + (v 10) ^ 2 + (v 12) ^ 2 + (v 13) ^ 2) := by ring
  unfold psi AES8.scale
  rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  ring

/-- A relaxed support cell permits arbitrary words at the marked positions. -/
def relaxedCell (m : Finset (Fin 4)) : Finset WordState :=
  Fintype.piFinset (fun i => if i ∈ m then Finset.univ else {0})

theorem relaxedCell_card (m : Finset (Fin 4)) :
    (relaxedCell m).card = (Fintype.card Word) ^ m.card := by
  classical
  unfold relaxedCell
  rw [Fintype.card_piFinset]
  calc
    (∏ i : Fin 4, (if i ∈ m then (Finset.univ : Finset Word) else {0}).card) =
        ∏ i : Fin 4, if i ∈ m then Fintype.card Word else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ m <;> simp [hi]
    _ = (Fintype.card Word) ^ m.card := by
      rw [Finset.prod_ite_mem_eq]
      simp

/-- Exactly `t` active words, without any residual-degree condition. -/
def activeCell (t : ℕ) : Finset WordState :=
  Finset.univ.filter (fun x => SupportProfile.activeCount x = t)

@[simp] theorem mem_activeCell (t : ℕ) (x : WordState) :
    x ∈ activeCell t ↔ SupportProfile.activeCount x = t := by
  simp [activeCell]

/-- A union bound over the small set of coordinate masks. The relaxed cells
may overlap; this only enlarges the required cardinality upper bound. -/
theorem activeCell_card_le (t : ℕ) :
    (activeCell t).card ≤ Nat.choose 4 t * (Fintype.card Word) ^ t := by
  let masks := (Finset.univ : Finset (Fin 4)).powersetCard t
  have hsub : activeCell t ⊆ masks.biUnion relaxedCell := by
    intro x hx
    rw [mem_activeCell] at hx
    let m : Finset (Fin 4) := Finset.univ.filter (fun i => x i ≠ 0)
    have hm : m.card = t := by simpa only [SupportProfile.activeCount, m] using hx
    apply Finset.mem_biUnion.mpr
    refine ⟨m, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hm⟩, ?_⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hi : i ∈ m
    · simp [hi]
    · have hz : x i = 0 := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)
      simp [hi, hz]
  calc
    (activeCell t).card ≤ (masks.biUnion relaxedCell).card := Finset.card_le_card hsub
    _ ≤ ∑ m ∈ masks, (relaxedCell m).card := Finset.card_biUnion_le
    _ = Nat.choose 4 t * (Fintype.card Word) ^ t := by
      calc
        (∑ m ∈ masks, (relaxedCell m).card) =
            ∑ _m ∈ masks, (Fintype.card Word) ^ t := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [relaxedCell_card, (Finset.mem_powersetCard.mp hm).2]
        _ = _ := by simp [masks]

/-- The factors `q² γ_t`, using `q = 2^32`. -/
def supportFactor (t : ℕ) : ℝ :=
  if t = 1 then 2 ^ (17 : ℕ) else
  if t = 2 then 5 * 2 ^ (31 : ℕ) else
  if t = 3 then 2 ^ (49 : ℕ) else 2 ^ (64 : ℕ)

theorem supportFactor_nonneg (t : ℕ) : 0 ≤ supportFactor t := by
  unfold supportFactor
  split_ifs <;> positivity

theorem activeCell_card_le_real (t : ℕ) :
    ((activeCell t).card : ℝ) ≤ (Nat.choose 4 t : ℝ) * ((2 : ℝ) ^ (32 : ℕ)) ^ t := by
  have hn : (activeCell t).card ≤ Nat.choose 4 t * (2 ^ 32) ^ t := by
    calc
      _ ≤ Nat.choose 4 t * (Fintype.card Word) ^ t := activeCell_card_le t
      _ = _ := by rw [word_card]
  exact_mod_cast hn

theorem activeCell_card_one :
    ((activeCell 1).card : ℝ) ≤ (supportFactor 1) ^ 2 := by
  exact (activeCell_card_le_real 1).trans (by norm_num [supportFactor])

theorem activeCell_card_two :
    ((activeCell 2).card : ℝ) ≤ (supportFactor 2) ^ 2 := by
  exact (activeCell_card_le_real 2).trans (by norm_num [supportFactor, Nat.choose])

theorem activeCell_card_three :
    ((activeCell 3).card : ℝ) ≤ (supportFactor 3) ^ 2 := by
  exact (activeCell_card_le_real 3).trans (by norm_num [supportFactor])

section FiniteNorm
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Cauchy--Schwarz for a function supported on a specified finite cell. -/
theorem l1_le_of_supported_card (s : Finset V) (f : V → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hs : ∀ x, x ∉ s → f x = 0)
    (hcard : (s.card : ℝ) ≤ c ^ 2) : l1 f ≤ c * l2 f := by
  have he : (∑ x ∈ s, |f x|) = l1 f := by
    unfold l1
    apply Finset.sum_subset (Finset.subset_univ s)
    intro x _ hx
    simp [hs x hx]
  have h := restricted_l1_sq s f
  rw [he] at h
  apply (sq_le_sq₀ (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (mul_nonneg hc (l2_nonneg f))).mp
  rw [mul_pow]
  exact h.trans (mul_le_mul_of_nonneg_right hcard (sq_nonneg _))

theorem l1_sum_le {I : Type*} [Fintype I] (g : I → V → ℝ) :
    l1 (fun x => ∑ i, g i x) ≤ ∑ i, l1 (g i) := by
  unfold l1
  calc
    (∑ x, |∑ i, g i x|) ≤ ∑ x, ∑ i, |g i x| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := Finset.sum_comm

/-- Cancellation works also for an empty cell; no arbitrary representative of
the large cell is needed in the public interface. -/
theorem constant_cell_cancellation_pairwise (s : Finset V) (f : V → ℝ)
    (hconst : ∀ x ∈ s, ∀ y ∈ s, f x = f y) (hzero : (∑ x, f x) = 0) :
    l1 f ≤ 2 * ∑ x ∈ sᶜ, |f x| := by
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    exact constant_cell_cancellation s f (f x) (fun y hy => hconst y hy x hx) hzero
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    simp only [Finset.compl_empty]
    unfold l1
    have hn : 0 ≤ ∑ x, |f x| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith

/-- Orthogonal terms are summed before converting the resulting Euclidean norm. -/
theorem orthogonal_sum_l2 {I : Type*} [Fintype I] (g : I → V → ℝ)
    (horth : ∀ i j, i ≠ j → (∑ x, g i x * g j x) = 0) :
    l2 (fun x => ∑ i, g i x) = Real.sqrt (∑ i, (l2 (g i)) ^ 2) := by
  change Real.sqrt (∑ x, (∑ i, g i x) ^ 2) = _
  rw [orthogonal_family_energy g horth]
  simp_rw [l2_sq]

end FiniteNorm

/-- Genuine support-sensitive bound for every actual profile component at one,
two, or three active words. -/
theorem component_l1 (f : WordState → ℝ) (c : Fin 14)
    (ht : SupportProfile.supportSize c = 1 ∨
      SupportProfile.supportSize c = 2 ∨ SupportProfile.supportSize c = 3) :
    l1 (SupportProfile.component f c) ≤
      supportFactor (SupportProfile.supportSize c) * SupportProfile.profile f c := by
  apply l1_le_of_supported_card (activeCell (SupportProfile.supportSize c))
    (SupportProfile.component f c) _ (supportFactor_nonneg _) ?_ ?_
  · intro x hx
    apply SupportProfile.component_supported f c x
    rw [mem_activeCell] at hx
    exact hx
  · rcases ht with h | h | h
    · rw [h]
      exact activeCell_card_one
    · rw [h]
      exact activeCell_card_two
    · rw [h]
      exact activeCell_card_three

theorem allActive_of_count_four (x : WordState) (hx : SupportProfile.activeCount x = 4) :
    ∀ i, x i ≠ 0 := by
  have he : (Finset.univ.filter (fun i : Fin 4 => x i ≠ 0)) = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa only [SupportProfile.activeCount, Fintype.card_fin] using hx)
  intro i
  have hi : i ∈ Finset.univ.filter (fun i : Fin 4 => x i ≠ 0) := by rw [he]; simp
  exact (Finset.mem_filter.mp hi).2

theorem mem_activeCell_four_iff (x : WordState) :
    x ∈ activeCell 4 ↔ ∀ i, x i ≠ 0 := by
  rw [mem_activeCell]
  constructor
  · intro hx
    exact allActive_of_count_four x hx
  · intro hx
    simp [SupportProfile.activeCount, hx]

/-- Zero mass and constancy on the all-active cell remove the fourth activity
length; only the three outside support components are charged, twice. -/
theorem activity_l1 (f : WordState → ℝ) (hz : f 0 = 0)
    (hsum : (∑ x, f x) = 0) :
    l1 (SupportProfile.activity f) ≤
      2 * (l1 (SupportProfile.component f 0) +
        l1 (SupportProfile.component f 1) + l1 (SupportProfile.component f 2)) := by
  have hconst : ∀ x ∈ activeCell 4, ∀ y ∈ activeCell 4,
      SupportProfile.activity f x = SupportProfile.activity f y := by
    intro x hx y hy
    rw [mem_activeCell] at hx hy
    exact SupportProfile.activity_allActive f x y
      (allActive_of_count_four x hx) (allActive_of_count_four y hy)
  have hc := constant_cell_cancellation_pairwise (activeCell 4)
    (SupportProfile.activity f) hconst
    (SupportProfile.activity_sum f hsum)
  have hout : (∑ x ∈ (activeCell 4)ᶜ, |SupportProfile.activity f x|) ≤
      l1 (SupportProfile.component f 0) + l1 (SupportProfile.component f 1) +
        l1 (SupportProfile.component f 2) := by
    calc
      _ ≤ ∑ x ∈ (activeCell 4)ᶜ,
          (|SupportProfile.component f 0 x| + |SupportProfile.component f 1 x| +
            |SupportProfile.component f 2 x|) := by
        apply Finset.sum_le_sum
        intro x hx
        have hx4 : SupportProfile.activeCount x ≠ 4 := by
          rw [Finset.mem_compl, mem_activeCell] at hx
          exact hx
        have hc3 : SupportProfile.component f 3 x = 0 :=
          SupportProfile.component_supported f 3 x (by simpa [SupportProfile.supportSize] using hx4)
        have hd := SupportProfile.activity_decomposition f hz x
        simp only [Fin.sum_univ_four] at hd
        have hi0 : Fin.castAdd 10 (0 : Fin 4) = (0 : Fin 14) := by decide
        have hi1 : Fin.castAdd 10 (1 : Fin 4) = (1 : Fin 14) := by decide
        have hi2 : Fin.castAdd 10 (2 : Fin 4) = (2 : Fin 14) := by decide
        have hi3 : Fin.castAdd 10 (3 : Fin 4) = (3 : Fin 14) := by decide
        have hd' : SupportProfile.activity f x = SupportProfile.component f 0 x +
            (SupportProfile.component f 1 x + (SupportProfile.component f 2 x +
              SupportProfile.component f 3 x)) := by
          simpa only [hi0, hi1, hi2, hi3, add_assoc] using hd
        rw [hd', hc3, add_zero]
        have h01 := abs_add_le (SupportProfile.component f 0 x)
          (SupportProfile.component f 1 x + SupportProfile.component f 2 x)
        have h12 := abs_add_le (SupportProfile.component f 1 x) (SupportProfile.component f 2 x)
        linarith
      _ ≤ ∑ x : WordState,
          (|SupportProfile.component f 0 x| + |SupportProfile.component f 1 x| +
            |SupportProfile.component f 2 x|) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => add_nonneg
            (add_nonneg (abs_nonneg (SupportProfile.component f 0 x))
              (abs_nonneg (SupportProfile.component f 1 x)))
            (abs_nonneg (SupportProfile.component f 2 x)))
      _ = _ := by simp only [l1, Finset.sum_add_distrib]
  linarith

def residualIndex : Fin 4 → Fin 14 := ![7, 10, 12, 13]
def partialIndex : Fin 6 → Fin 14 := ![4, 5, 6, 8, 9, 11]

theorem residualIndex_injective : Function.Injective residualIndex := by decide

/-- The four all-active positive residual degrees are combined in Euclidean
norm before the common `q²` Cauchy--Schwarz factor is paid. -/
theorem residual_l1 (f : WordState → ℝ) :
    l1 (fun x => ∑ i : Fin 4, SupportProfile.component f (residualIndex i) x) ≤
      (2 : ℝ) ^ (64 : ℕ) *
        Real.sqrt ((SupportProfile.profile f 7) ^ 2 + (SupportProfile.profile f 10) ^ 2 +
          (SupportProfile.profile f 12) ^ 2 + (SupportProfile.profile f 13) ^ 2) := by
  have hcard : (Fintype.card WordState : ℝ) ≤ ((2 : ℝ) ^ (64 : ℕ)) ^ 2 := by
    change (Fintype.card (Fin 4 → Word) : ℝ) ≤ _
    rw [Fintype.card_fun, Fintype.card_fin, word_card]
    norm_num
  have horth (i j : Fin 4) (hij : i ≠ j) :
      (∑ x, SupportProfile.component f (residualIndex i) x *
        SupportProfile.component f (residualIndex j) x) = 0 :=
    SupportProfile.component_orthogonal f f _ _ (fun he => hij (residualIndex_injective he))
  have h := l1_le_of_card
    (fun x => ∑ i : Fin 4, SupportProfile.component f (residualIndex i) x)
    ((2 : ℝ) ^ (64 : ℕ)) (by positivity) hcard
  rw [orthogonal_sum_l2 _ horth] at h
  simpa [Fin.sum_univ_four, residualIndex, SupportProfile.profile, add_assoc] using h

/-- The support-sensitive output inequality for the actual orthogonal
projection profile. Its assumptions are precisely zero extension and zero
total mass, rather than an assumed bound on the output distance. -/
theorem support_sensitive_tv (f : WordState → ℝ) (hz : f 0 = 0)
    (hsum : (∑ x, f x) = 0) :
    (∑ x, |f x|) / 2 ≤
      (2 : ℝ) ^ (63 : ℕ) * psi (SupportProfile.profile f) := by
  have ha := activity_l1 f hz hsum
  have hr := residual_l1 f
  have h0 := component_l1 f 0 (by decide)
  have h1 := component_l1 f 1 (by decide)
  have h2 := component_l1 f 2 (by decide)
  have h4 := component_l1 f 4 (by decide)
  have h5 := component_l1 f 5 (by decide)
  have h6 := component_l1 f 6 (by decide)
  have h8 := component_l1 f 8 (by decide)
  have h9 := component_l1 f 9 (by decide)
  have h11 := component_l1 f 11 (by decide)
  have hp := l1_sum_le (fun i : Fin 6 => SupportProfile.component f (partialIndex i))
  have hd (x : WordState) : f x = SupportProfile.activity f x +
      (∑ i : Fin 6, SupportProfile.component f (partialIndex i) x) +
      (∑ i : Fin 4, SupportProfile.component f (residualIndex i) x) := by
    rw [← SupportProfile.component_decomposition f hz x,
      SupportProfile.activity_decomposition f hz x]
    simp [Fin.sum_univ_succ, partialIndex, residualIndex]
    ring
  have htri : l1 f ≤ l1 (SupportProfile.activity f) +
      l1 (fun x => ∑ i : Fin 6, SupportProfile.component f (partialIndex i) x) +
      l1 (fun x => ∑ i : Fin 4, SupportProfile.component f (residualIndex i) x) := by
    unfold l1
    calc
      (∑ x, |f x|) ≤ ∑ x, (|SupportProfile.activity f x| +
          |∑ i : Fin 6, SupportProfile.component f (partialIndex i) x| +
          |∑ i : Fin 4, SupportProfile.component f (residualIndex i) x|) := by
        apply Finset.sum_le_sum
        intro x _
        rw [hd]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hpsum : (∑ i : Fin 6, l1 (SupportProfile.component f (partialIndex i))) =
      l1 (SupportProfile.component f 4) + l1 (SupportProfile.component f 5) +
      l1 (SupportProfile.component f 6) + l1 (SupportProfile.component f 8) +
      l1 (SupportProfile.component f 9) + l1 (SupportProfile.component f 11) := by
    simp [Fin.sum_univ_succ, partialIndex, add_assoc]
  rw [hpsum] at hp
  change l1 (SupportProfile.component f 0) ≤ (2 : ℝ) ^ (17 : ℕ) * SupportProfile.profile f 0 at h0
  change l1 (SupportProfile.component f 1) ≤ (5 * (2 : ℝ) ^ (31 : ℕ)) * SupportProfile.profile f 1 at h1
  change l1 (SupportProfile.component f 2) ≤ (2 : ℝ) ^ (49 : ℕ) * SupportProfile.profile f 2 at h2
  change l1 (SupportProfile.component f 4) ≤ (2 : ℝ) ^ (17 : ℕ) * SupportProfile.profile f 4 at h4
  change l1 (SupportProfile.component f 5) ≤ (5 * (2 : ℝ) ^ (31 : ℕ)) * SupportProfile.profile f 5 at h5
  change l1 (SupportProfile.component f 6) ≤ (2 : ℝ) ^ (49 : ℕ) * SupportProfile.profile f 6 at h6
  change l1 (SupportProfile.component f 8) ≤ (5 * (2 : ℝ) ^ (31 : ℕ)) * SupportProfile.profile f 8 at h8
  change l1 (SupportProfile.component f 9) ≤ (2 : ℝ) ^ (49 : ℕ) * SupportProfile.profile f 9 at h9
  change l1 (SupportProfile.component f 11) ≤ (2 : ℝ) ^ (49 : ℕ) * SupportProfile.profile f 11 at h11
  unfold psi
  change l1 f / 2 ≤ _
  linarith only [htri, ha, hp, hr, h0, h1, h2, h4, h5, h6, h8, h9, h11]

end AES8.SupportOutput
