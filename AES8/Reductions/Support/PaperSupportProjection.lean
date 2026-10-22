/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.PaperSupportOutput
import AESMixing.SupportOrthogonality
import AESMixing.GroupedEnergy

/-!
# The paper's tensor projections for arbitrary word count

The two Boolean masks mark residual factors and zero factors.  At an unmarked,
nonzero position `supportPiece` is exactly the constant-nonzero projection.
Thus grouping these tensors by their two counts is the paper's projection,
including its zero tensors for overlapping masks. No component laws are assumed.
Constructive proof work only; no numerical estimates or manuscript edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace AES8.PaperSupportProjection
open AESMixing
open AES8.PaperSupportOutput (activeCount activeMask activeCell)

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

abbrev Label (n : ℕ) := (Fin n → Bool) × (Fin n → Bool)

def residualCount (m : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun k => m k = true)).card

def supportCount (m : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun k => m k = false)).card

def Valid (p : Label n) : Prop := ∀ k, p.1 k = true → p.2 k = false

instance (p : Label n) : Decidable (Valid p) := inferInstanceAs
  (Decidable (∀ k, p.1 k = true → p.2 k = false))

def raw (z : V) (p : Label n) (f : (Fin n → V) → ℝ) : (Fin n → V) → ℝ :=
  action (supportProduct z p.1 p.2) f

/-- Exactly the sum of tensors with `i` residual, `t-i` constant-nonzero,
and `n-t` zero factors; invalid overlapping masks contribute zero. -/
def component (z : V) (f : (Fin n → V) → ℝ) (i t : ℕ) (x : Fin n → V) : ℝ :=
  ∑ p : Label n, if residualCount p.1 = i ∧ supportCount p.2 = t then raw z p f x else 0

def activity (z : V) (f : (Fin n → V) → ℝ) : (Fin n → V) → ℝ :=
  action (productProjection z (fun _ : Fin n => false)) f

def profile (z : V) (f : (Fin n → V) → ℝ) : AES8.PaperSupportOutput.Profile :=
  AES8.PaperSupportOutput.componentProfile (component z f)

theorem residualCount_le (m : Fin n → Bool) : residualCount m ≤ n := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

theorem supportCount_le (m : Fin n → Bool) : supportCount m ≤ n := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

theorem valid_degree_le_support (p : Label n) (hp : Valid p) :
    residualCount p.1 ≤ supportCount p.2 := by
  apply Finset.card_le_card
  intro k hk
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hp k (Finset.mem_filter.mp hk).2⟩

theorem raw_invalid (z : V) (p : Label n) (hp : ¬ Valid p)
    (f : (Fin n → V) → ℝ) : raw z p f = 0 := by
  unfold Valid at hp
  push Not at hp
  obtain ⟨k, hk, hi⟩ := hp
  have hi' : p.2 k = true := by cases he : p.2 k <;> simp_all
  funext y
  unfold raw action
  apply Finset.sum_eq_zero
  intro x _
  have hz : supportProduct z p.1 p.2 y x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [supportPiece, hk, hi'])
  rw [hz, zero_mul]

theorem raw_orthogonal (z : V) (hq : 1 < Fintype.card V)
    (p q : Label n) (hpq : p ≠ q) (f g : (Fin n → V) → ℝ) :
    (∑ x, raw z p f x * raw z q g x) = 0 := by
  apply supportProduct_mixed_orthogonal z hq
  exact fun h => hpq (Prod.ext h.1 h.2)

theorem raw_decomposition (z : V) (f : (Fin n → V) → ℝ) (x : Fin n → V) :
    (∑ p : Label n, raw z p f x) = f x := by
  rw [Fintype.sum_prod_type]
  have hs (m : Fin n → Bool) : (∑ a : Fin n → Bool, raw z (m,a) f x) =
      action (productProjection z m) f x :=
    congrFun (supportProduct_decomposition z m f) x
  simp_rw [hs]
  exact congrFun (productProjection_decomposition z f) x

private theorem supportPiece_row_zero (z : V) (marked inactive : Bool) (y x : V)
    (h : inactive ≠ decide (y = z)) : supportPiece z marked inactive y x = 0 := by
  cases marked <;> cases inactive <;> by_cases hy : y = z <;>
    simp_all [supportPiece, constantMatrix, zeroMatrix, activityMatrix, identityKernel,
      residualProjection_zero_row]

theorem raw_supported (z : V) (p : Label n) (f : (Fin n → V) → ℝ)
    (x : Fin n → V) (hx : activeCount z x ≠ supportCount p.2) : raw z p f x = 0 := by
  have hm : ∃ k, p.2 k ≠ decide (x k = z) := by
    by_contra h
    push Not at h
    apply hx
    unfold activeCount activeMask supportCount
    congr 1
    ext k
    simp [h k]
  obtain ⟨k, hk⟩ := hm
  unfold raw action
  apply Finset.sum_eq_zero
  intro y _
  have hz : supportProduct z p.1 p.2 x y = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) (supportPiece_row_zero z _ _ _ _ hk)
  rw [hz, zero_mul]

theorem component_supported (z : V) (f : (Fin n → V) → ℝ) (i t : ℕ)
    (x : Fin n → V) (hx : activeCount z x ≠ t) : component z f i t x = 0 := by
  unfold component
  apply Finset.sum_eq_zero
  intro p _
  split_ifs with hp
  · exact raw_supported z p f x (by simpa [hp.2] using hx)
  · rfl

theorem component_above_triangle (z : V) (f : (Fin n → V) → ℝ)
    (i t : ℕ) (hit : t < i) : component z f i t = 0 := by
  funext x
  unfold component
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : Valid p
  · have hle := valid_degree_le_support p hp
    split_ifs with h
    · omega
    · rfl
  · simp [raw_invalid z p hp f]

theorem component_orthogonal (z : V) (hq : 1 < Fintype.card V)
    (f : (Fin n → V) → ℝ) (i t j u : ℕ) (h : (i,t) ≠ (j,u)) :
    (∑ x, component z f i t x * component z f j u x) = 0 := by
  let group : Label n → ℕ × ℕ := fun p => (residualCount p.1, supportCount p.2)
  have he (a b : ℕ) : component z f a b = groupedFamily group (fun p => raw z p f) (a,b) := by
    funext x
    simp only [component, groupedFamily, group, Prod.mk.injEq]
  rw [he, he]
  exact groupedFamily_orthogonal group (fun p => raw z p f)
    (fun p q hpq => raw_orthogonal z hq p q hpq f f) _ _ h

theorem sum_fin_select {a : ℕ} (ha : a ≤ n) (v : ℝ) :
    (∑ k : Fin (n + 1), if a = k.val then v else 0) = v := by
  let k : Fin (n + 1) := ⟨a, Nat.lt_succ_of_le ha⟩
  rw [Finset.sum_eq_single k]
  · simp [k]
  · intro b _ hbk
    have hab : a ≠ b.val := fun h => hbk (Fin.ext h.symm)
    simp [hab]
  · simp

theorem component_decomposition_full (z : V) (f : (Fin n → V) → ℝ)
    (x : Fin n → V) :
    (∑ t : Fin (n + 1), ∑ i : Fin (n + 1), component z f i.val t.val x) = f x := by
  unfold component
  have he :
      (∑ t : Fin (n + 1), ∑ i : Fin (n + 1), ∑ p : Label n,
        if residualCount p.1 = i.val ∧ supportCount p.2 = t.val then raw z p f x else 0) =
      ∑ p : Label n, ∑ i : Fin (n + 1), ∑ t : Fin (n + 1),
        if residualCount p.1 = i.val ∧ supportCount p.2 = t.val then raw z p f x else 0 := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (n + 1))))
      (t := (Finset.univ : Finset (Label n)))]
  rw [he]
  have hs (p : Label n) :
      (∑ i : Fin (n + 1), ∑ t : Fin (n + 1),
        if residualCount p.1 = i.val ∧ supportCount p.2 = t.val then raw z p f x else 0) =
      raw z p f x := by
    simp_rw [ite_and]
    have ht (i : Fin (n + 1)) :
        (∑ t : Fin (n + 1), if residualCount p.1 = i.val then
          (if supportCount p.2 = t.val then raw z p f x else 0) else 0) =
        if residualCount p.1 = i.val then raw z p f x else 0 := by
      split_ifs with hi
      · exact sum_fin_select (supportCount_le p.2) _
      · simp
    simp_rw [ht]
    exact sum_fin_select (residualCount_le p.1) _
  simp_rw [hs]
  exact raw_decomposition z f x

end AES8.PaperSupportProjection
