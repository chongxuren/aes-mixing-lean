import AESMixing.DegreeKernel
import AESMixing.MDSProjection

/-! Unnormalized support indicators and their concrete diffusion responses.
Coordinates are the four byte positions, rather than an assumed small Gram
matrix. The unnormalized basis removes square roots from certificates. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES

variable {V : Type*} [Fintype V] [Zero V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem extend_restrict (mask : Fin 16) (x : Fin 4 → V) :
    extendCoordinates mask (restrictCoordinates mask x) = maskProjection mask x := by
  funext i
  by_cases h : maskBit mask i = true <;>
    simp [extendCoordinates, restrictCoordinates, maskProjection, h]

omit [Fintype V] [DecidableEq V] in
theorem extendCoordinates_injective (mask : Fin 16) :
    Function.Injective (extendCoordinates (V := V) mask) := by
  intro x y h
  have hh := congrArg (restrictCoordinates mask) h
  simpa only [restrict_extend] using hh

def activityColumn (mask : Fin 16) (x : Fin 4 → V) : ℝ :=
  if maskProjection mask x = x then 1 else 0

theorem activityColumn_as_sum (mask : Fin 16) (x : Fin 4 → V) :
    activityColumn mask x = ∑ u : MaskCoordinates mask → V,
      identityKernel x (extendCoordinates mask u) := by
  by_cases hx : maskProjection mask x = x
  · rw [activityColumn, if_pos hx]
    symm
    rw [Finset.sum_eq_single (restrictCoordinates mask x)]
    · simp [identityKernel, extend_restrict, hx]
    · intro u _ hu
      have hxu : x ≠ extendCoordinates mask u := by
        intro he
        have hh := congrArg (restrictCoordinates mask) he
        rw [restrict_extend] at hh
        exact hu hh.symm
      simp [identityKernel, hxu]
    · simp
  · rw [activityColumn, if_neg hx]
    symm
    apply Finset.sum_eq_zero
    intro u _
    have hxu : x ≠ extendCoordinates mask u := by
      intro he
      subst x
      exact hx (extend_supported mask u)
    simp [identityKernel, hxu]

theorem action_activityColumn {Y : Type*} (K : Y → (Fin 4 → V) → ℝ)
    (mask : Fin 16) (y : Y) :
    action K (activityColumn mask) y =
      ∑ u : MaskCoordinates mask → V, K y (extendCoordinates mask u) := by
  unfold action
  simp_rw [activityColumn_as_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp [identityKernel]

def diffusedActivityColumn (L : (Fin 4 → V) ≃ (Fin 4 → V))
    (mask : Fin 16) (y : Fin 4 → V) : ℝ := activityColumn mask (L.symm y)

theorem action_diffusedActivityColumn (K : (Fin 4 → V) → (Fin 4 → V) → ℝ)
    (L : (Fin 4 → V) ≃ (Fin 4 → V)) (mask : Fin 16) (y : Fin 4 → V) :
    action K (diffusedActivityColumn L mask) y =
      responseColumn K (fun u : MaskCoordinates mask → V => L (extendCoordinates mask u)) y := by
  unfold action diffusedActivityColumn responseColumn
  rw [← L.sum_comp]
  simp only [L.symm_apply_apply]
  exact action_activityColumn (fun y x => K y (L x)) mask y

theorem degree_diffusedActivityColumn (L : (Fin 4 → V) ≃ (Fin 4 → V))
    (j : Fin 5) (mask : Fin 16) :
    degreeComponent 0 j (diffusedActivityColumn L mask) =
      responseColumn (degreeKernel 0 j)
        (fun u : MaskCoordinates mask → V => L (extendCoordinates mask u)) := by
  rw [← degreeKernel_action]
  funext y
  exact action_diffusedActivityColumn _ L mask y

theorem activity_degree_gram (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) ≃ (Fin 4 → V)) (j : Fin 5) (a b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn L a) y *
      degreeComponent 0 j (diffusedActivityColumn L b) y) =
      ∑ p : Fin 4 → Bool, if degreeIndex p = j then
        ∑ m : Fin 4 → Fin 5, (∏ i, atomCoefficient (Fintype.card V) (p i) (m i)) *
          Fintype.card {x : (MaskCoordinates a → V) × (MaskCoordinates b → V) // ∀ i,
            atomCondition (m i) (L (extendCoordinates a x.1) i)
              (L (extendCoordinates b x.2) i)} else 0 := by
  simp_rw [degree_diffusedActivityColumn]
  simpa only [← Nat.card_eq_fintype_card] using
    degree_response_constraint_count hn j
      (fun u : MaskCoordinates a → V => L (extendCoordinates a u))
      (fun u : MaskCoordinates b → V => L (extendCoordinates b u))

def byteDiffusionEquiv : (Fin 4 → BinaryWord 8) ≃ (Fin 4 → BinaryWord 8) :=
  Equiv.ofBijective (columnMatrix mixEntry)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨mixColumn_injective, rfl⟩)

/-- The exact constraint-sum formula for actual AES MixColumns. It provides
the semantic side of the numerical Gram certificate, for every support pair
and every residual degree. It makes no numerical norm assumption. -/
theorem byte_activity_degree_gram (j : Fin 5) (a b : Fin 16) :
    (∑ y, degreeComponent 0 j (diffusedActivityColumn byteDiffusionEquiv a) y *
      degreeComponent 0 j (diffusedActivityColumn byteDiffusionEquiv b) y) =
      ∑ p : Fin 4 → Bool, if degreeIndex p = j then
        ∑ m : Fin 4 → Fin 5, (∏ i, atomCoefficient 256 (p i) (m i)) *
          Fintype.card {x : (MaskCoordinates a → BinaryWord 8) ×
              (MaskCoordinates b → BinaryWord 8) // ∀ i,
            atomCondition (m i) (columnMatrix mixEntry (extendCoordinates a x.1) i)
              (columnMatrix mixEntry (extendCoordinates b x.2) i)} else 0 := by
  have hn : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  have h := activity_degree_gram hn byteDiffusionEquiv j a b
  norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat] at h
  simpa only [byteDiffusionEquiv, Equiv.ofBijective_apply,
    ← Nat.card_eq_fintype_card] using h

end AESMixing
