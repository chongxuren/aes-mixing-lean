/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Support.PaperSupportProjection

/-! The generic tensor/profile bridge to the paper's support-sensitive bound.
The only analytic premises in the final theorem are zero extension and centering;
support, activity cancellation and orthogonality are derived from the tensors. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace AES8.PaperSupportProjection
open AESMixing
open AESPaper.RareActivity (l1)
open AES8.PaperSupportOutput (activeCount activeMask activeCell)

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

theorem residualCount_zero_iff (m : Fin n → Bool) :
    residualCount m = 0 ↔ m = fun _ => false := by
  constructor
  · intro h
    have he : Finset.univ.filter (fun k => m k = true) = ∅ := Finset.card_eq_zero.mp h
    funext k
    have hk : m k ≠ true := by
      intro hm
      have hm' : k ∈ Finset.univ.filter (fun k => m k = true) := by simp [hm]
      rw [he] at hm'
      simpa using hm'
    cases hm : m k <;> simp_all
  · rintro rfl
    simp [residualCount]

theorem activeCount_le (z : V) (x : Fin n → V) : activeCount z x ≤ n := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)

theorem activeCount_zero_iff (z : V) (x : Fin n → V) :
    activeCount z x = 0 ↔ x = fun _ => z := by
  constructor
  · intro h
    have he : Finset.univ.filter (fun k => x k ≠ z) = ∅ := Finset.card_eq_zero.mp h
    funext k
    by_contra hk
    have hm : k ∈ Finset.univ.filter (fun k => x k ≠ z) := by simp [hk]
    rw [he] at hm
    simpa using hm
  · rintro rfl
    simp [activeCount, activeMask]

theorem activity_sum (z : V) (hq : 1 < Fintype.card V)
    (f : (Fin n → V) → ℝ) (hf : (∑ x, f x) = 0) :
    (∑ x, activity z f x) = 0 := by
  exact ((coordinateKernel_pointed _ _
    (fun _ : Fin n => activityMatrix_pointed z hq)).action_sum f).trans hf

theorem activity_zero (z : V) (hq : 1 < Fintype.card V)
    (f : (Fin n → V) → ℝ) (hf : f (fun _ => z) = 0) :
    activity z f (fun _ => z) = 0 := by
  exact ((coordinateKernel_pointed _ _
    (fun _ : Fin n => activityMatrix_pointed z hq)).action_zero f).trans hf

theorem activity_allActive (z : V) (f : (Fin n → V) → ℝ)
    (x y : Fin n → V) (hx : ∀ i, x i ≠ z) (hy : ∀ i, y i ≠ z) :
    activity z f x = activity z f y := by
  unfold activity action
  apply Finset.sum_congr rfl
  intro w _
  apply congrArg (fun a : ℝ => a * f w)
  apply Finset.prod_congr rfl
  intro i _
  simp [degreePiece, activityMatrix, hx i, hy i]

theorem allActive_of_count (z : V) (x : Fin n → V) (hx : activeCount z x = n) :
    ∀ i, x i ≠ z := by
  have he : activeMask z x = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa only [activeCount, Fintype.card_fin] using hx)
  intro i
  have hi : i ∈ activeMask z x := by rw [he]; simp
  exact (Finset.mem_filter.mp hi).2

theorem activity_const (z : V) (f : (Fin n → V) → ℝ) :
    ∀ x ∈ activeCell z n, ∀ y ∈ activeCell z n, activity z f x = activity z f y := by
  intro x hx y hy
  apply activity_allActive z f x y
  · exact allActive_of_count z x ((AES8.PaperSupportOutput.mem_activeCell z n x).mp hx)
  · exact allActive_of_count z y ((AES8.PaperSupportOutput.mem_activeCell z n y).mp hy)

theorem activity_decomposition_full (z : V) (f : (Fin n → V) → ℝ) (x : Fin n → V) :
    (∑ t : Fin (n + 1), component z f 0 t.val x) = activity z f x := by
  unfold component
  rw [Finset.sum_comm]
  have hs (p : Label n) :
      (∑ t : Fin (n + 1),
        if residualCount p.1 = 0 ∧ supportCount p.2 = t.val then raw z p f x else 0) =
      if p.1 = (fun _ => false) then raw z p f x else 0 := by
    simp_rw [ite_and]
    by_cases hp : residualCount p.1 = 0
    · simp only [hp, if_true]
      rw [sum_fin_select (supportCount_le p.2)]
      simp [(residualCount_zero_iff p.1).mp hp]
    · have hm : p.1 ≠ (fun _ => false) := fun h => hp ((residualCount_zero_iff p.1).mpr h)
      simp [hp, hm]
  simp_rw [hs]
  rw [Fintype.sum_prod_type]
  change (∑ m : Fin n → Bool, ∑ a : Fin n → Bool,
    if m = (fun _ => false) then raw z (m,a) f x else 0) = activity z f x
  rw [Finset.sum_eq_single (fun _ : Fin n => false)]
  · simp only [if_true]
    exact congrFun (supportProduct_decomposition z (fun _ : Fin n => false) f) x
  · intro m _ hm
    simp only [hm, if_false, Finset.sum_const_zero]
  · simp

/-- Padding a finite initial sum with a zero tail does not change it. -/
theorem sum_fin_truncate (g : ℕ → ℝ) {m k : ℕ} (hkm : k ≤ m)
    (hz : ∀ i, k ≤ i → i < m → g i = 0) :
    (∑ i : Fin m, g i.val) = ∑ i : Fin k, g i.val := by
  induction m generalizing k with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    rfl
  | succ m ih =>
    by_cases hk : k = m + 1
    · subst k
      rfl
    · have hkm' : k ≤ m := by omega
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih hkm' (fun i hi him => hz i hi (by omega)), hz m hkm' (by omega), add_zero]

theorem component_zero_support (z : V) (f : (Fin n → V) → ℝ)
    (hf : f (fun _ => z) = 0) (i : ℕ) : component z f i 0 = 0 := by
  by_cases hi : i = 0
  · subst i
    funext x
    by_cases hx : x = fun _ => z
    · subst x
      have hd := component_decomposition_full z f (fun _ => z)
      rw [Fin.sum_univ_succ] at hd
      simp only [Fin.val_zero, Fin.val_succ] at hd
      have ht : (∑ t : Fin n, ∑ i : Fin (n + 1),
          component z f i.val (t.val + 1) (fun _ => z)) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        apply Finset.sum_eq_zero
        intro i _
        apply component_supported
        simp [activeCount, activeMask]
      rw [ht, add_zero, Fin.sum_univ_succ] at hd
      simp only [Fin.val_zero, Fin.val_succ] at hd
      have hi : (∑ i : Fin n, component z f (i.val + 1) 0 (fun _ => z)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact congrFun (component_above_triangle z f _ _ (by simp)) _
      rw [hi, add_zero, hf] at hd
      exact hd
    · exact component_supported z f 0 0 x (fun h => hx ((activeCount_zero_iff z x).mp h))
  · exact component_above_triangle z f i 0 (by omega)

theorem activity_decomposition (z : V) (f : (Fin n → V) → ℝ)
    (hf : f (fun _ => z) = 0) (x : Fin n → V) :
    activity z f x = ∑ t : Fin n, component z f 0 (t.val + 1) x := by
  have h := activity_decomposition_full z f x
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.val_zero, Fin.val_succ] at h
  rw [congrFun (component_zero_support z f hf 0) x] at h
  simpa only [Pi.zero_apply, zero_add] using h.symm

theorem activity_outside (hn : 1 ≤ n) (z : V) (f : (Fin n → V) → ℝ)
    (hf : f (fun _ => z) = 0) (x : Fin n → V) (hx : x ∉ activeCell z n) :
    activity z f x = ∑ t : Fin (n - 1), component z f 0 (t.val + 1) x := by
  rw [activity_decomposition z f hf]
  apply sum_fin_truncate (fun t => component z f 0 (t + 1) x) (m := n) (k := n - 1) (by omega)
  intro i hi hin
  have he : i + 1 = n := by omega
  rw [he]
  exact component_supported z f 0 n x
    (by simpa only [AES8.PaperSupportOutput.mem_activeCell] using hx)

theorem residual_decomposition (z : V) (f : (Fin n → V) → ℝ)
    (hf : f (fun _ => z) = 0) (x : Fin n → V) :
    f x = activity z f x +
      ∑ t : Fin n, ∑ i : Fin (t.val + 1), component z f (i.val + 1) (t.val + 1) x := by
  have hd := component_decomposition_full z f x
  have hz : (∑ i : Fin (n + 1), component z f i.val 0 x) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact congrFun (component_zero_support z f hf i.val) x
  rw [Fin.sum_univ_succ] at hd
  simp only [Fin.val_zero, Fin.val_succ] at hd
  rw [hz, zero_add] at hd
  have hi (t : Fin n) :
      (∑ i : Fin (n + 1), component z f i.val (t.val + 1) x) =
      component z f 0 (t.val + 1) x +
        ∑ i : Fin (t.val + 1), component z f (i.val + 1) (t.val + 1) x := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    congr 1
    apply sum_fin_truncate (fun i => component z f (i + 1) (t.val + 1) x)
      (m := n) (k := t.val + 1) (by omega)
    intro i hi _
    exact congrFun (component_above_triangle z f _ _ (by omega)) x
  simp_rw [hi] at hd
  rw [Finset.sum_add_distrib, ← activity_decomposition z f hf] at hd
  exact hd.symm

theorem component_split (hn : 1 ≤ n) (z : V) (f : (Fin n → V) → ℝ)
    (hf : f (fun _ => z) = 0) (x : Fin n → V) :
    f x = activity z f x +
      (∑ t : Fin (n - 1), ∑ i : Fin (t.val + 1), component z f (i.val + 1) (t.val + 1) x) +
      ∑ i : Fin n, component z f (i.val + 1) n x := by
  have hn' : n = (n - 1) + 1 := by omega
  have hs (g : ℕ → ℝ) : (∑ t : Fin n, g t.val) =
      (∑ t : Fin (n - 1), g t.val) + g (n - 1) := by
    conv_lhs => rw [hn']
    rw [Fin.sum_univ_castSucc]
    rfl
  rw [residual_decomposition z f hf,
    hs (fun t => ∑ i : Fin (t + 1), component z f (i.val + 1) (t + 1) x)]
  have hlast : n - 1 + 1 = n := by omega
  have he : (∑ i : Fin (n - 1 + 1), component z f (i.val + 1) (n - 1 + 1) x) =
      ∑ i : Fin n, component z f (i.val + 1) n x :=
    congrArg (fun t => ∑ i : Fin t, component z f (i.val + 1) t x) hlast
  rw [he]
  exact (add_assoc _ _ _).symm

/-- The paper's Lemma 3 for the actual arbitrary-word tensor profile.
No decomposition, support or orthogonality assumptions remain in the interface. -/
theorem support_sensitive_distance (hn : 1 ≤ n) (z : V)
    (hq : 1 < Fintype.card V) (f : (Fin n → V) → ℝ)
    (hf : f (fun _ => z) = 0) (hcenter : (∑ x, f x) = 0) :
    l1 f / 2 ≤ AES8.PaperSupportOutput.ambientRadius n (Fintype.card V) / 2 *
      AES8.PaperSupportOutput.psi n (Fintype.card V) (profile z f) := by
  apply AES8.PaperSupportOutput.support_sensitive_distance z f (activity z f) (component z f)
  · exact component_split hn z f hf
  · exact activity_sum z hq f hcenter
  · exact activity_const z f
  · exact fun x hx => activity_outside hn z f hf x hx
  · exact component_supported z f
  · intro i j hij
    apply component_orthogonal z hq f _ _ _ _
    intro he
    apply hij
    apply Fin.ext
    have hv := congrArg (fun p : ℕ × ℕ => p.1) he
    omega

abbrev NonzeroState (z : V) (n : ℕ) := {x : Fin n → V // x ≠ fun _ => z}

def zeroExtend (z : V) (f : NonzeroState z n → ℝ) (x : Fin n → V) : ℝ :=
  if hx : x ≠ (fun _ => z) then f ⟨x,hx⟩ else 0

@[simp] theorem zeroExtend_zero (z : V) (f : NonzeroState z n → ℝ) :
    zeroExtend z f (fun _ => z) = 0 := by simp [zeroExtend]

theorem zeroExtend_sum (z : V) (f : NonzeroState z n → ℝ) :
    (∑ x, zeroExtend z f x) = ∑ x, f x := by
  apply Finset.sum_congr_set {x : Fin n → V | x ≠ fun _ => z}
  · intro x hx
    change x ≠ (fun _ => z) at hx
    simp [zeroExtend, hx]
  · intro x hx
    change ¬(x ≠ (fun _ => z)) at hx
    have he : x = (fun _ => z) := not_not.mp hx
    subst x
    simp [zeroExtend]

theorem zeroExtend_l1 (z : V) (f : NonzeroState z n → ℝ) :
    l1 (zeroExtend z f) = l1 f := by
  unfold l1
  apply Finset.sum_congr_set {x : Fin n → V | x ≠ fun _ => z}
  · intro x hx
    change x ≠ (fun _ => z) at hx
    simp [zeroExtend, hx]
  · intro x hx
    change ¬(x ≠ (fun _ => z)) at hx
    have he : x = (fun _ => z) := not_not.mp hx
    subst x
    simp [zeroExtend]

theorem component_at_zero (z : V) (f : (Fin n → V) → ℝ)
    (hf : f (fun _ => z) = 0) (i t : ℕ) : component z f i t (fun _ => z) = 0 := by
  by_cases ht : t = 0
  · subst t
    exact congrFun (component_zero_support z f hf i) _
  · apply component_supported
    have hz : activeCount z (fun _ : Fin n => z) = 0 := by simp [activeCount, activeMask]
    rw [hz]
    exact Ne.symm ht

/-- Norms of the paper's projections restricted to its stated nonzero domain. -/
def nonzeroProfile (z : V) (f : NonzeroState z n → ℝ) : AES8.PaperSupportOutput.Profile :=
  fun i t => l2 (fun x : NonzeroState z n => component z (zeroExtend z f) i t x.val)

theorem profile_zeroExtend (z : V) (f : NonzeroState z n → ℝ) :
    profile z (zeroExtend z f) = nonzeroProfile z f := by
  funext i t
  unfold profile AES8.PaperSupportOutput.componentProfile nonzeroProfile l2
  congr 1
  apply Finset.sum_congr_set {x : Fin n → V | x ≠ fun _ => z}
  · intro x _
    rfl
  · intro x hx
    have he : x = (fun _ => z) := by simpa using hx
    subst x
    rw [component_at_zero z _ (zeroExtend_zero z f), zero_pow (by decide)]

/-- Lemma 3 with exactly the paper's domain: any centered real function on
the nonzero tuples of an arbitrary finite pointed alphabet with `q > 1`. -/
theorem support_sensitive_distance_nonzero (hn : 1 ≤ n) (z : V)
    (hq : 1 < Fintype.card V) (f : NonzeroState z n → ℝ)
    (hcenter : (∑ x, f x) = 0) :
    l1 f / 2 ≤ AES8.PaperSupportOutput.ambientRadius n (Fintype.card V) / 2 *
      AES8.PaperSupportOutput.psi n (Fintype.card V) (nonzeroProfile z f) := by
  have h := support_sensitive_distance hn z hq (zeroExtend z f) (zeroExtend_zero z f)
    ((zeroExtend_sum z f).trans hcenter)
  simpa only [zeroExtend_l1, profile_zeroExtend] using h

end AES8.PaperSupportProjection
