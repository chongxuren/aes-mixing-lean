/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Source.Startup
import AES8.Recurrence.SupportEvolution
import AES8.Reductions.Support.TransferZeros

/-!
# Exact support reduction for the actual one-source initialization

An inactive projection coordinate selects input zero at that coordinate.
Therefore it annihilates any joint input supported on states whose every
coordinate is nonzero. The actual one-source four-round law has precisely
that support. Its positive-degree components agree with those of the actual
error because the stationary reference has only residual degree zero.

This module proves support identities only: every positive-degree
component below active support four is zero, including coordinate 11, so
the actual initial high part is the sum of components 12 and 13. It asserts
no quantitative cap or first-high inequality. Constructive proof work only;
no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.OneSourceSupport
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (error)
open AESPaper.ManySourceBounds (activeSourceCount)
open AES8.SupportProfile (component profile)

section GenericInput
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]

/-- An inactive support piece has no column at a non-distinguished input. -/
theorem supportPiece_inactive_column_zero (z : V) (marked : Bool) (y x : V)
    (hx : x ≠ z) : supportPiece z marked true y x = 0 := by
  cases marked <;> simp [supportPiece, zeroMatrix, identityKernel, hx]

/-- Keep this alphabet-generic to avoid expanding concrete AES finite types. -/
theorem supportProduct_inactive_input_zero (z : V) (marked inactive : I → Bool)
    (k : I) (hk : inactive k = true) (y x : I → V) (hx : x k ≠ z) :
    supportProduct z marked inactive y x = 0 := by
  unfold supportProduct
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  rw [hk]
  exact supportPiece_inactive_column_zero z (marked k) (y k) (x k) hx

/-- A single inactive input selector annihilates a joint function vanishing
when that input coordinate is distinguished. No product-law premise occurs. -/
theorem supportProduct_action_eq_zero_of_inactive
    (z : V) (marked inactive : I → Bool) (k : I) (hk : inactive k = true)
    (f : (I → V) → ℝ) (hf : ∀ x, x k = z → f x = 0) :
    action (supportProduct z marked inactive) f = 0 := by
  funext y
  unfold action
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x k = z
  · rw [hf x hx, mul_zero]
  · rw [supportProduct_inactive_input_zero z marked inactive k hk y x hx, zero_mul]

end GenericInput

section ConcreteComponents

/-- An all-active joint input has no component with active support below four.
This statement is independent of residual degree and of the AES law. -/
theorem component_eq_zero_of_all_active (f : WordState → ℝ)
    (hf : ∀ x : WordState, ∀ k : Fin 4, x k = 0 → f x = 0)
    (c : Fin 14) (hc : SupportProfile.supportSize c < 4) : component f c = 0 := by
  funext y
  rw [SupportProfile.component_eq_support_residual]
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : maskSize p.1 = SupportProfile.residualDegree c ∧
      4 - maskSize p.2 = SupportProfile.supportSize c
  · rw [if_pos hp]
    have hm : 0 < maskSize p.2 := by omega
    change 0 < (Finset.univ.filter (fun i : Fin 4 => maskBit p.2 i)).card at hm
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hm
    have hk' : maskBit p.2 k = true := (Finset.mem_filter.mp hk).2
    have hz : SupportProfile.raw p f = 0 :=
      supportProduct_action_eq_zero_of_inactive (0 : AES.Word)
        (maskBit p.1) (maskBit p.2) k hk' f (fun x hx => hf x k hx)
    exact congrFun hz y
  · rw [if_neg hp]

theorem raw_sub (p : SupportProfile.Label) (f g : WordState → ℝ) :
    SupportProfile.raw p (f - g) = SupportProfile.raw p f - SupportProfile.raw p g :=
  action_sub _ f g

/-- The source-only reference removal is applied before support reasoning. -/
theorem component_sub (f g : WordState → ℝ) (c : Fin 14) :
    component (f - g) c = component f c - component g c := by
  funext y
  change (∑ p : SupportProfile.Label, if SupportProfile.coord p = c.succ then
      SupportProfile.raw p (f - g) y else 0) =
    (∑ p : SupportProfile.Label, if SupportProfile.coord p = c.succ then
      SupportProfile.raw p f y else 0) -
    ∑ p : SupportProfile.Label, if SupportProfile.coord p = c.succ then
      SupportProfile.raw p g y else 0
  simp_rw [raw_sub, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : SupportProfile.coord p = c.succ <;>
    simp only [hp, if_true, if_false, sub_self]

/-- The full-state stationary reference may occupy several activity supports,
but its positive residual-degree support components are all zero. -/
theorem uniform_component_eq_zero (c : Fin 14)
    (hc : 0 < SupportProfile.residualDegree c) :
    component (uniformExcept (0 : WordState)) c = 0 := by
  apply TransferZeros.component_eq_zero_of_degree_eq_zero
  apply AESPaper.OneSourceEnergies.uniform_positive_degree
  intro h0
  have hv := congrArg Fin.val h0
  change SupportProfile.residualDegree c = 0 at hv
  omega

end ConcreteComponents

section ActualOneSource

/-- The one-source law itself is all-active, before removing its reference. -/
theorem law_component_eq_zero (k : Fin 4) (a : AES.Word) (ha : a ≠ 0)
    (c : Fin 14) (hc : SupportProfile.supportSize c < 4) :
    component (AESPaper.OneSourceLaw.law k a) c = 0 :=
  component_eq_zero_of_all_active _
    (fun x i hx => AESPaper.OneSourceLaw.law_zero_of_coordinate_zero k a ha x i hx) c hc

/-- Positive-degree components of the error are exactly those of the law.
The statement deliberately does not assert that the whole error is all-active. -/
theorem actual_component_eq_law (b : AES.State) (k : Fin 4) (a : AES.Word)
    (hsource : AESPaper.StartingWord.sourceInput b =
      AESPaper.BoundarySourceCoordinates.singleWord k a)
    (c : Fin 14) (hc : 0 < SupportProfile.residualDegree c) :
    component (error 1 b) c = component (AESPaper.OneSourceLaw.law k a) c := by
  change component
    (AESPaper.GroupedLaw.groupedLaw 1 b - uniformExcept (0 : WordState)) c = _
  rw [AESPaper.OneSourceLaw.groupedLaw_one_eq_law b k a hsource, component_sub,
    uniform_component_eq_zero c hc, sub_zero]

/-- The exact one-source component reduction, stated with the source-count
interface used by the universal initializer. -/
theorem actual_component_eq_zero (a : AES.State) (ha : activeSourceCount a = 1)
    (c : Fin 14) (hr : 0 < SupportProfile.residualDegree c)
    (hs : SupportProfile.supportSize c < 4) : component (error 1 a) c = 0 := by
  obtain ⟨k, w, hw, hsource⟩ := AESPaper.UniversalInitialization.one_active_source a ha
  rw [actual_component_eq_law a k w hsource c hr]
  exact law_component_eq_zero k w hw c hs

/-- Input coordinate eleven has residual degree three and active support three. -/
theorem actual_component_eleven_eq_zero (a : AES.State)
    (ha : activeSourceCount a = 1) : component (error 1 a) (11 : Fin 14) = 0 :=
  actual_component_eq_zero a ha (11 : Fin 14) (by decide) (by decide)

theorem actual_profile_eleven_eq_zero (a : AES.State)
    (ha : activeSourceCount a = 1) : profile (error 1 a) (11 : Fin 14) = 0 := by
  unfold profile
  rw [actual_component_eleven_eq_zero a ha]
  exact l2_zero

/-- The complete actual high part retains precisely the two surviving components.
This is an algebraic identity, not a quantitative first-high estimate. -/
theorem actual_highPart_eq_two (a : AES.State) (ha : activeSourceCount a = 1) :
    SupportEvolution.highPart (error 1 a) =
      component (error 1 a) (12 : Fin 14) + component (error 1 a) (13 : Fin 14) := by
  funext x
  simp only [SupportEvolution.highPart, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, Pi.add_apply]
  change component (error 1 a) (11 : Fin 14) x +
      (component (error 1 a) (12 : Fin 14) x + component (error 1 a) (13 : Fin 14) x) =
    component (error 1 a) (12 : Fin 14) x + component (error 1 a) (13 : Fin 14) x
  rw [actual_component_eleven_eq_zero a ha, Pi.zero_apply, zero_add]

end ActualOneSource
end AES8.OneSourceSupport
