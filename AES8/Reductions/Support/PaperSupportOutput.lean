/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AESPaper.RareActivity
import AESMixing.ProductProjection
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset

/-!
# General support-sensitive output conversion

The binomial support sizes and the norm argument of `lem:general-output` are
generic in the word count and finite alphabet. This module separates that
argument from construction of the paper's orthogonal component projections.
Its decomposition theorem takes only exact decomposition, support, centering,
constancy and orthogonality laws; it takes no distance estimate as a premise.
The current AES component construction is in the separate four-word module.
Constructive mathematics only; no manuscript/vendor edits or attacks.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AES8.PaperSupportOutput
open AESMixing AESPaper.RareActivity

section Counting
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

def activeMask (z : V) (x : Fin n → V) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ z)

def activeCount (z : V) (x : Fin n → V) : ℕ := (activeMask z x).card

def activeCell (z : V) (t : ℕ) : Finset (Fin n → V) :=
  Finset.univ.filter (fun x => activeCount z x = t)

@[simp] theorem mem_activeCell (z : V) (t : ℕ) (x : Fin n → V) :
    x ∈ activeCell z t ↔ activeCount z x = t := by simp [activeCell]

/-- An exact activity pattern permits nonzero alphabet symbols only at the
marked positions, rather than using a relaxed full-alphabet cell. -/
def patternCell (z : V) (m : Finset (Fin n)) : Finset (Fin n → V) :=
  Fintype.piFinset (fun i => if i ∈ m then Finset.univ.erase z else {z})

theorem patternCell_card (z : V) (m : Finset (Fin n)) :
    (patternCell z m).card = (Fintype.card V - 1) ^ m.card := by
  unfold patternCell
  rw [Fintype.card_piFinset]
  calc
    (∏ i : Fin n, (if i ∈ m then (Finset.univ : Finset V).erase z else {z}).card) =
        ∏ i : Fin n, if i ∈ m then Fintype.card V - 1 else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ m <;> simp [hi]
    _ = (Fintype.card V - 1) ^ m.card := by
      rw [Finset.prod_ite_mem_eq]
      simp

theorem activeMask_eq_of_mem_patternCell (z : V) (m : Finset (Fin n))
    (x : Fin n → V) (hx : x ∈ patternCell z m) : activeMask z x = m := by
  have hcoord := Fintype.mem_piFinset.mp hx
  ext i
  by_cases hi : i ∈ m
  · have hxi : x i ≠ z := by simpa [hi] using hcoord i
    simp [activeMask, hi, hxi]
  · have hxi : x i = z := by simpa [hi] using hcoord i
    simp [activeMask, hi, hxi]

theorem mem_patternCell_activeMask (z : V) (x : Fin n → V) :
    x ∈ patternCell z (activeMask z x) := by
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases hi : x i = z <;> simp [activeMask, hi]

/-- The exact binomial support cardinality in the paper, for every word count
and every finite alphabet with distinguished zero symbol. -/
theorem activeCell_card (z : V) (t : ℕ) :
    (activeCell (n := n) z t).card =
      Nat.choose n t * (Fintype.card V - 1) ^ t := by
  let masks := (Finset.univ : Finset (Fin n)).powersetCard t
  have he : activeCell (n := n) z t = masks.biUnion (patternCell z) := by
    ext x
    constructor
    · intro hx
      have ht : (activeMask z x).card = t := (mem_activeCell z t x).mp hx
      exact Finset.mem_biUnion.mpr ⟨activeMask z x,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ht⟩,
        mem_patternCell_activeMask z x⟩
    · intro hx
      obtain ⟨m, hm, hx⟩ := Finset.mem_biUnion.mp hx
      apply (mem_activeCell z t x).mpr
      unfold activeCount
      rw [activeMask_eq_of_mem_patternCell z m x hx]
      exact (Finset.mem_powersetCard.mp hm).2
  have hdis : (masks : Set (Finset (Fin n))).PairwiseDisjoint (patternCell z) := by
    intro m _ k _ hmk
    apply Finset.disjoint_left.mpr
    intro x hxm hxk
    exact hmk ((activeMask_eq_of_mem_patternCell z m x hxm).symm.trans
      (activeMask_eq_of_mem_patternCell z k x hxk))
  rw [he, Finset.card_biUnion hdis]
  calc
    (∑ m ∈ masks, (patternCell z m).card) =
        ∑ _m ∈ masks, (Fintype.card V - 1) ^ t := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [patternCell_card, (Finset.mem_powersetCard.mp hm).2]
    _ = _ := by simp [masks]

end Counting

section FiniteNorm
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem l1_le_of_supported_card (s : Finset X) (f : X → ℝ) (c : ℝ)
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

theorem l1_sum_le {I : Type*} [Fintype I] (g : I → X → ℝ) :
    l1 (fun x => ∑ i, g i x) ≤ ∑ i, l1 (g i) := by
  unfold l1
  calc
    (∑ x, |∑ i, g i x|) ≤ ∑ x, ∑ i, |g i x| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := Finset.sum_comm

theorem constant_cell_cancellation_pairwise (s : Finset X) (f : X → ℝ)
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

theorem orthogonal_sum_l2 {I : Type*} [Fintype I] (g : I → X → ℝ)
    (horth : ∀ i j, i ≠ j → (∑ x, g i x * g j x) = 0) :
    l2 (fun x => ∑ i, g i x) = Real.sqrt (∑ i, (l2 (g i)) ^ 2) := by
  change Real.sqrt (∑ x, (∑ i, g i x) ^ 2) = _
  rw [orthogonal_family_energy g horth]
  simp_rw [l2_sq]

end FiniteNorm

/-- Coordinates are indexed by residual degree and active word count. -/
abbrev Profile := ℕ → ℕ → ℝ

/-- `sqrt(q^n)` is the paper's `q^(n/2)`, using real square roots so all
word counts, including odd counts, have an exact algebraic representation. -/
def ambientRadius (n q : ℕ) : ℝ := Real.sqrt ((q : ℝ) ^ n)

def supportRadius (n q t : ℕ) : ℝ :=
  Real.sqrt ((Nat.choose n t : ℝ) * ((q - 1 : ℕ) : ℝ) ^ t)

def supportWeight (n q t : ℕ) : ℝ := supportRadius n q t / ambientRadius n q

/-- Exact binomial weights, without AES-specific rounding. `Fin (n-1)`
enumerates activity sizes `1,...,n-1`; `Fin t` enumerates degrees `1,...,t`. -/
def psi (n q : ℕ) (p : Profile) : ℝ :=
  2 * (∑ t : Fin (n - 1), supportWeight n q (t.val + 1) * p 0 (t.val + 1)) +
    (∑ t : Fin (n - 1), supportWeight n q (t.val + 1) *
      ∑ i : Fin (t.val + 1), p (i.val + 1) (t.val + 1)) +
    Real.sqrt (∑ i : Fin n, (p (i.val + 1) n) ^ 2)

def rawOutput (n q : ℕ) (p : Profile) : ℝ :=
  2 * (∑ t : Fin (n - 1), supportRadius n q (t.val + 1) * p 0 (t.val + 1)) +
    (∑ t : Fin (n - 1), supportRadius n q (t.val + 1) *
      ∑ i : Fin (t.val + 1), p (i.val + 1) (t.val + 1)) +
    ambientRadius n q * Real.sqrt (∑ i : Fin n, (p (i.val + 1) n) ^ 2)

theorem ambientRadius_pos (n q : ℕ) (hq : 0 < q) : 0 < ambientRadius n q := by
  exact Real.sqrt_pos.mpr (pow_pos (Nat.cast_pos.mpr hq) n)

theorem radius_mul_weight (n q t : ℕ) (hq : 0 < q) :
    ambientRadius n q * supportWeight n q t = supportRadius n q t := by
  unfold supportWeight
  field_simp [(ambientRadius_pos n q hq).ne']

theorem psi_normalization (n q : ℕ) (hq : 0 < q) (p : Profile) :
    ambientRadius n q * psi n q p = rawOutput n q p := by
  have hscale (v : Fin (n - 1) → ℝ) :
      ambientRadius n q * (∑ t : Fin (n - 1), supportWeight n q (t.val + 1) * v t) =
        ∑ t : Fin (n - 1), supportRadius n q (t.val + 1) * v t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [← mul_assoc, radius_mul_weight n q _ hq]
  unfold psi rawOutput
  calc
    _ = 2 * (ambientRadius n q *
          (∑ t : Fin (n - 1), supportWeight n q (t.val + 1) * p 0 (t.val + 1))) +
        (ambientRadius n q * (∑ t : Fin (n - 1), supportWeight n q (t.val + 1) *
          ∑ i : Fin (t.val + 1), p (i.val + 1) (t.val + 1))) +
        ambientRadius n q * Real.sqrt (∑ i : Fin n, (p (i.val + 1) n) ^ 2) := by ring
    _ = _ := by rw [hscale, hscale]

theorem supportWeight_nonneg (n q t : ℕ) : 0 ≤ supportWeight n q t :=
  div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem psi_mono (n q : ℕ) {p r : Profile}
    (hp : ∀ i t, 0 ≤ p i t) (hpr : ∀ i t, p i t ≤ r i t) :
    psi n q p ≤ psi n q r := by
  apply add_le_add
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
      apply Finset.sum_le_sum
      intro t _
      exact mul_le_mul_of_nonneg_left (hpr _ _) (supportWeight_nonneg _ _ _)
    · apply Finset.sum_le_sum
      intro t _
      apply mul_le_mul_of_nonneg_left _ (supportWeight_nonneg _ _ _)
      exact Finset.sum_le_sum (fun i _ => hpr _ _)
  · apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_sq₀ (hp _ _) ((hp _ _).trans (hpr _ _))).mpr (hpr _ _)

theorem psi_scale (n q : ℕ) (a : ℝ) (p : Profile) (ha : 0 ≤ a) :
    psi n q (fun i t => a * p i t) = a * psi n q p := by
  have hlinear (v : Fin (n - 1) → ℝ) :
      (∑ t : Fin (n - 1), supportWeight n q (t.val + 1) * (a * v t)) =
        a * ∑ t : Fin (n - 1), supportWeight n q (t.val + 1) * v t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hinner (t : Fin (n - 1)) :
      (∑ i : Fin (t.val + 1), a * p (i.val + 1) (t.val + 1)) =
        a * ∑ i : Fin (t.val + 1), p (i.val + 1) (t.val + 1) := by
    rw [Finset.mul_sum]
  have hsquare : (∑ i : Fin n, (a * p (i.val + 1) n) ^ 2) =
      a ^ 2 * ∑ i : Fin n, (p (i.val + 1) n) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold psi
  simp_rw [hinner]
  rw [hlinear, hlinear, hsquare, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
  ring

section Decomposition
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

def componentProfile (component : ℕ → ℕ → (Fin n → V) → ℝ) : Profile :=
  fun i t => l2 (component i t)

theorem component_l1 (z : V) (component : ℕ → ℕ → (Fin n → V) → ℝ)
    (hsupport : ∀ i t x, activeCount z x ≠ t → component i t x = 0)
    (i t : ℕ) :
    l1 (component i t) ≤ supportRadius n (Fintype.card V) t * componentProfile component i t := by
  apply l1_le_of_supported_card (activeCell z t) (component i t) _
    (Real.sqrt_nonneg _) ?_ ?_
  · intro x hx
    exact hsupport i t x (by simpa only [mem_activeCell] using hx)
  · rw [Real.sq_sqrt (by positivity)]
    exact_mod_cast (activeCell_card (n := n) z t).le

/-- The support-sensitive bound derived from the exact component laws. This
is the generic analytic half of Lemma 3; constructing those laws for arbitrary
word-count tensor projections is a separate algebraic bridge. -/
theorem decomposition_l1_bound
    (z : V) (f activity : (Fin n → V) → ℝ)
    (component : ℕ → ℕ → (Fin n → V) → ℝ)
    (hsplit : ∀ x, f x = activity x +
      (∑ t : Fin (n - 1), ∑ i : Fin (t.val + 1), component (i.val + 1) (t.val + 1) x) +
      ∑ i : Fin n, component (i.val + 1) n x)
    (hactivity_sum : (∑ x, activity x) = 0)
    (hactivity_const : ∀ x ∈ activeCell z n, ∀ y ∈ activeCell z n, activity x = activity y)
    (hactivity_outside : ∀ x, x ∉ activeCell z n →
      activity x = ∑ t : Fin (n - 1), component 0 (t.val + 1) x)
    (hsupport : ∀ i t x, activeCount z x ≠ t → component i t x = 0)
    (horthogonal : ∀ i j : Fin n, i ≠ j →
      (∑ x, component (i.val + 1) n x * component (j.val + 1) n x) = 0) :
    l1 f ≤ rawOutput n (Fintype.card V) (componentProfile component) := by
  have ha := constant_cell_cancellation_pairwise (activeCell z n) activity
    hactivity_const hactivity_sum
  have hout : (∑ x ∈ (activeCell z n)ᶜ, |activity x|) ≤
      ∑ t : Fin (n - 1), l1 (component 0 (t.val + 1)) := by
    calc
      _ ≤ ∑ x ∈ (activeCell z n)ᶜ, ∑ t : Fin (n - 1), |component 0 (t.val + 1) x| := by
        apply Finset.sum_le_sum
        intro x hx
        rw [hactivity_outside x (Finset.mem_compl.mp hx)]
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : Fin n → V, ∑ t : Fin (n - 1), |component 0 (t.val + 1) x| :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      _ = _ := Finset.sum_comm
  have hact : l1 activity ≤ 2 *
      ∑ t : Fin (n - 1), supportRadius n (Fintype.card V) (t.val + 1) *
        componentProfile component 0 (t.val + 1) := by
    have hc : (∑ t : Fin (n - 1), l1 (component 0 (t.val + 1))) ≤
        ∑ t : Fin (n - 1), supportRadius n (Fintype.card V) (t.val + 1) *
          componentProfile component 0 (t.val + 1) :=
      Finset.sum_le_sum (fun t _ => component_l1 z component hsupport 0 (t.val + 1))
    linarith
  have hpart : l1 (fun x => ∑ t : Fin (n - 1),
      ∑ i : Fin (t.val + 1), component (i.val + 1) (t.val + 1) x) ≤
      ∑ t : Fin (n - 1), supportRadius n (Fintype.card V) (t.val + 1) *
        ∑ i : Fin (t.val + 1), componentProfile component (i.val + 1) (t.val + 1) := by
    calc
      _ ≤ ∑ t : Fin (n - 1), l1 (fun x =>
          ∑ i : Fin (t.val + 1), component (i.val + 1) (t.val + 1) x) := l1_sum_le _
      _ ≤ ∑ t : Fin (n - 1), ∑ i : Fin (t.val + 1),
          l1 (component (i.val + 1) (t.val + 1)) :=
        Finset.sum_le_sum (fun t _ => l1_sum_le _)
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t _
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun i _ => component_l1 z component hsupport _ _)
  have hfull : l1 (fun x => ∑ i : Fin n, component (i.val + 1) n x) ≤
      ambientRadius n (Fintype.card V) *
        Real.sqrt (∑ i : Fin n, (componentProfile component (i.val + 1) n) ^ 2) := by
    have hcard : (Fintype.card (Fin n → V) : ℝ) ≤ (ambientRadius n (Fintype.card V)) ^ 2 := by
      rw [ambientRadius, Real.sq_sqrt (by positivity)]
      rw [Fintype.card_fun, Fintype.card_fin]
      norm_cast
    have h := l1_le_of_card (fun x => ∑ i : Fin n, component (i.val + 1) n x)
      (ambientRadius n (Fintype.card V)) (Real.sqrt_nonneg _) hcard
    rw [orthogonal_sum_l2 _ horthogonal] at h
    exact h
  have htri : l1 f ≤ l1 activity +
      l1 (fun x => ∑ t : Fin (n - 1), ∑ i : Fin (t.val + 1),
        component (i.val + 1) (t.val + 1) x) +
      l1 (fun x => ∑ i : Fin n, component (i.val + 1) n x) := by
    unfold l1
    calc
      (∑ x, |f x|) ≤ ∑ x, (|activity x| +
          |∑ t : Fin (n - 1), ∑ i : Fin (t.val + 1), component (i.val + 1) (t.val + 1) x| +
          |∑ i : Fin n, component (i.val + 1) n x|) := by
        apply Finset.sum_le_sum
        intro x _
        rw [hsplit]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by simp only [Finset.sum_add_distrib]
  exact htri.trans (add_le_add (add_le_add hact hpart) hfull)

/-- The paper's `1/2 l1 <= q^(n/2)/2 psi` with exact binomial weights. The
algebraic component-law interface is deliberately visible in the preceding
theorem, so it cannot be mistaken for a completed generic projection bridge. -/
theorem support_sensitive_distance
    (z : V) (f activity : (Fin n → V) → ℝ)
    (component : ℕ → ℕ → (Fin n → V) → ℝ)
    (hsplit : ∀ x, f x = activity x +
      (∑ t : Fin (n - 1), ∑ i : Fin (t.val + 1), component (i.val + 1) (t.val + 1) x) +
      ∑ i : Fin n, component (i.val + 1) n x)
    (hactivity_sum : (∑ x, activity x) = 0)
    (hactivity_const : ∀ x ∈ activeCell z n, ∀ y ∈ activeCell z n, activity x = activity y)
    (hactivity_outside : ∀ x, x ∉ activeCell z n →
      activity x = ∑ t : Fin (n - 1), component 0 (t.val + 1) x)
    (hsupport : ∀ i t x, activeCount z x ≠ t → component i t x = 0)
    (horthogonal : ∀ i j : Fin n, i ≠ j →
      (∑ x, component (i.val + 1) n x * component (j.val + 1) n x) = 0) :
    l1 f / 2 ≤ ambientRadius n (Fintype.card V) / 2 *
      psi n (Fintype.card V) (componentProfile component) := by
  have hq : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨z⟩
  have h := decomposition_l1_bound z f activity component hsplit hactivity_sum
    hactivity_const hactivity_outside hsupport horthogonal
  rw [← psi_normalization n (Fintype.card V) hq] at h
  linarith

end Decomposition
end AES8.PaperSupportOutput
