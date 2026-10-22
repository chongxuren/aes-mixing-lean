import AES8.Reductions.Source.PaperProductSource

/-! Exact fixed-support identities for the initial product source.
These identities connect the fixed-source bound to grouped profile coordinates;
they introduce no extra support multiplicity or conditioning of a probability law. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperProductSourceSupport
open AESMixing PaperSupportProjection PaperFixedSupportBlockLift PaperProductSource
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

theorem piece_wrong_support (z : V) (K : V → V → ℝ)
    (hK : PointedBistochastic K z) (a : V) (r s : Bool)
    (hs : ¬ (a = z ↔ s = true)) :
    action (supportPiece z r s) (fun x => K x a) = 0 := by
  cases r <;> cases s
  · have ha : a = z := by simpa using hs
    rw [show supportPiece z false false = constantMatrix z by rfl,
      constantMatrix_action, average_column z K hK]
    funext x
    by_cases hx : x = z <;> simp [activityMatrix, zeroPart, ha, hx, hK.zero_column]
  · have ha : a ≠ z := by simpa using hs
    rw [show supportPiece z false true = zeroMatrix z by rfl, zeroMatrix_action]
    funext x
    simp [zeroPart, hK.zero_row, ha]
  · have ha : a = z := by simpa using hs
    rw [show supportPiece z true false = residualProjection z by rfl,
      residual_column z K hK]
    funext x
    rw [ha, AESConcrete.pointed_residual_zero_column hK]
    rfl
  · exact zero_kernel_action _

theorem raw_wrong_support (z : V) (K : V → V → ℝ)
    (hK : PointedBistochastic K z) (a : Fin n → V) (s : Fin n → Bool)
    (hs : ∀ k, a k = z ↔ s k = true) (p : Label n) (hp : p.2 ≠ s) :
    raw z p (source K a) = 0 := by
  have hex : ∃ k, p.2 k ≠ s k := by
    by_contra h
    push Not at h
    exact hp (funext h)
  obtain ⟨k,hk⟩ := hex
  have hw : ¬ (a k = z ↔ p.2 k = true) := by
    intro he
    have heq : p.2 k = s k := by
      cases h₁ : p.2 k <;> cases h₂ : s k <;> simp_all
    exact hk heq
  funext x
  rw [raw_source]
  exact Finset.prod_eq_zero (Finset.mem_univ k)
    (congrFun (piece_wrong_support z K hK (a k) (p.1 k) (p.2 k) hw) (x k))

theorem fixedComponent_sum (z : V) (f : (Fin n → V) → ℝ) (j : ℕ)
    (s : Fin n → Bool) (x : Fin n → V) :
    fixedComponent z f j s x =
      ∑ r : Fin n → Bool, if residualCount r = j then raw z (r,s) f x else 0 := by
  classical
  symm
  calc
    _ = ∑ r : Fin n → Bool, if Valid (r,s) ∧ residualCount r = j
        then raw z (r,s) f x else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hv : Valid (r,s)
      · simp [hv]
      · simp [hv, raw_invalid z (r,s) hv f]
    _ = _ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) _

theorem component_eq_fixed (z : V) (K : V → V → ℝ)
    (hK : PointedBistochastic K z) (a : Fin n → V) (s : Fin n → Bool)
    (hs : ∀ k, a k = z ↔ s k = true) (j t : ℕ) :
    component z (source K a) j t =
      if supportCount s = t then fixedComponent z (source K a) j s else 0 := by
  classical
  funext x
  unfold component
  rw [Fintype.sum_prod_type]
  have hinner (r : Fin n → Bool) :
      (∑ b : Fin n → Bool,
        if residualCount r = j ∧ supportCount b = t then raw z (r,b) (source K a) x
        else 0) =
      if residualCount r = j ∧ supportCount s = t then raw z (r,s) (source K a) x
      else 0 := by
    apply Finset.sum_eq_single s
    · intro b _ hb
      simp [raw_wrong_support z K hK a s hs (r,b) hb]
    · simp
  simp_rw [hinner]
  by_cases ht : supportCount s = t
  · simp only [ht, and_true, if_true]
    exact (fixedComponent_sum z (source K a) j s x).symm
  · simp [ht]

theorem fixed_decomposition (z : V) (K : V → V → ℝ)
    (hK : PointedBistochastic K z) (a : Fin n → V) (s : Fin n → Bool)
    (hs : ∀ k, a k = z ↔ s k = true) :
    (fun x => ∑ j : Fin (n+1), fixedComponent z (source K a) j.val s x) =
      source K a := by
  funext x
  simp_rw [fixedComponent_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_fin_select (residualCount_le _) _]
  have h := raw_decomposition z (source K a) x
  rw [Fintype.sum_prod_type] at h
  have hinner (r : Fin n → Bool) :
      (∑ b : Fin n → Bool, raw z (r,b) (source K a) x) =
        raw z (r,s) (source K a) x := by
    apply Finset.sum_eq_single s
    · intro b _ hb
      exact congrFun (raw_wrong_support z K hK a s hs (r,b) hb) x
    · simp
  simpa only [hinner] using h

end AES8.PaperProductSourceSupport
