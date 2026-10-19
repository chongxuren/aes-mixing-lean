import AESPaper.Profile
import AESPaper.WordCells

/-!
Activity-sensitive total variation for the actual five-component profile.
The complement count uses the full state space (including zero); its slightly
weaker coefficient still yields exactly the normalization used in v9.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
namespace AESPaper.ProfileTV
open AESMixing AESMixing.AES AESPaper.ProfileSpace

-- The naming linter unfolds the concrete all-active Finset until it reaches
-- its recursion limit. This local setting affects only that linter, not Lean's kernel.
set_option linter.constructorNameAsVariable false in
theorem activity_l1 (f : ProfileSpace.State) (hf : Centered f) :
    RareActivity.l1 (fun x => component 0 f x) ≤ (2:ℝ)^50 * profile f 0 := by
  -- Project the conjunction while the vector is a variable: reducing a
  -- concrete kernel-operator application here over-expands its coercions.
  have centered_sum (v : ProfileSpace.State) (hv : Centered v) :
      (∑ x, v x) = 0 := hv.2
  have hzero : (∑ x, component 0 f x) = 0 :=
    centered_sum (component 0 f) (component_centered 0 f hf)
  have hs : WordCells.allActive.Nonempty := by
    apply Finset.card_pos.mp
    rw [WordCells.allActive_card]
    norm_num
  obtain ⟨x0, hx0⟩ := hs
  simp only [WordCells.mem_allActive] at hx0
  have hx0' : ∀ i : Fin 4, x0 i ≠ (0 : AES.Word) := by
    exact hx0
  have hconstant : ∀ x ∈ WordCells.allActive,
      component 0 f x = component 0 f x0 := by
    intro x hx
    simp only [WordCells.mem_allActive] at hx
    apply activity_constant_on_allActive f x x0
    · exact hx
    · exact hx0'
  have h := WordCells.activity_l1 (fun x => component 0 f x) (component 0 f x0)
    hconstant hzero
  rw [l2_eq_norm (component 0 f)] at h
  simpa only [profile] using h

theorem component_l1 (f : ProfileSpace.State) (hf : Centered f) :
    RareActivity.l1 (fun x => f x) ≤
      (2:ℝ)^50 * profile f 0 + (2:ℝ)^64 *
        Real.sqrt (∑ i : Fin 4, profile f i.succ ^ 2) := by
  have he : (fun x => f x) =
      (fun x => component 0 f x) + (fun x => (f-component 0 f) x) := by
    funext x
    simp
  have hr := WordCells.ordinary_l1 (fun x => (f-component 0 f) x)
  rw [l2_eq_norm, residual_norm] at hr
  calc
    _ = RareActivity.l1 ((fun x => component 0 f x) +
        (fun x => (f-component 0 f) x)) := congrArg RareActivity.l1 he
    _ ≤ _ := (RareActivity.l1_add _ _).trans (add_le_add (activity_l1 f hf) hr)

theorem weighted_tv (f : ProfileSpace.State) (hf : Centered f) :
    RareActivity.l1 (fun x => f x) / 2 ≤ (2:ℝ)^63 *
      (profile f 0 / 16384 + Real.sqrt (∑ i : Fin 4, profile f i.succ ^ 2)) := by
  have h := component_l1 f hf
  norm_num at h ⊢
  linarith

theorem normalized_tv (f : ProfileSpace.State) (hf : Centered f) :
    RareActivity.l1 (fun x => f x) / 2 ≤ (1/(2:ℝ)^17) *
      AESPaper.score (normalizedProfile f) := by
  rw [score_normalization]
  have h := weighted_tv f hf
  norm_num at h ⊢
  linarith

end AESPaper.ProfileTV
