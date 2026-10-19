import AESPaper.ResponseCoordinateTransport
import AESPaper.ResponseScalarBounds

/-!
# Restricted whole-word response for arbitrary disjoint marked masks

Finite coordinate selection and exact reindexing remove every auxiliary
information-set witness from the actual response theorem. The count d=w-k
is the active source dimension after prescribing k zeros; min(d,j) counts
residual outputs paid for by operator contraction. Additional source events
remain unnormalized. The impossible-event case is included for positive w.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
namespace AESPaper.UniversalRestrictedResponse
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESPaper.StartingWord (q sourceInput)
open AESPaper.WordDamping (nu)
open AESPaper.WordRestrictedResponse (residual delta)
open AESPaper.ManySourceBounds (activeSourceCount activeSourceMask)

/-- Actual residual action on the joint-event marginal, in counting measure. -/
def responseEnergy (b : AES.State) (r out : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] : ℝ :=
  ∑ y, action (coordinateKernel (fun _ : MaskCoordinates out => residual))
    (ActualRestrictedSource.markedMarginal b r out event) y ^ 2

theorem responseEnergy_nonnegative (b : AES.State) (r out : Fin 16)
    (event : AES.WordState → Prop) [DecidablePred event] :
    0 ≤ responseEnergy b r out event := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Selection of free inputs and a marked core is proved inside the two branches. -/
theorem energy_le_with_inactive_mask (b : AES.State) (r z out : Fin 16)
    (hr : MaskDisjoint r out) (hshort : maskSize r + maskSize z ≤ 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : AES.WordState → Prop) [DecidablePred event] :
    responseEnergy b r out event ≤
      (20/q)^(2 * maskSize r) * (6/(5*q))^(min (4-maskSize r-maskSize z) (maskSize out)) *
      nu^(2 * min (4-maskSize r-maskSize z) (maskSize out)) *
      delta^(maskSize out-min (4-maskSize r-maskSize z) (maskSize out)) := by
  let d : Fin 5 := ⟨4-maskSize r-maskSize z, by omega⟩
  by_cases hl : maskSize out ≤ d.val
  · obtain ⟨s,u,hsu,hzu,hs,hu,ho⟩ :=
      ResponseMaskSelection.low_input_choices r z out hshort hl
    have h := ActualRestrictedWordResponse.actual_low_energy b r z s u out
      hsu hzu hs hr ho ha event
    have hm : min (4-maskSize r-maskSize z) (maskSize out) = maskSize out :=
      Nat.min_eq_right hl
    change responseEnergy b r out event ≤ _ at h
    calc
      _ ≤ nu^(2 * maskSize out) * (20/q)^(2 * maskSize r) * (6/(5*q))^maskSize out := h
      _ = _ := by simp only [hm, Nat.sub_self, pow_zero, mul_one]; ring
  · have hj : d.val ≤ maskSize out := by omega
    obtain ⟨s,u,hsu,hzu,hsum,hu⟩ := ResponseMaskSelection.input_choices
      z d d (by dsimp [d]; omega) le_rfl
    obtain ⟨core,extra,hd,he,hc,hx⟩ := ResponseMaskSelection.output_choices out d.val hj
    subst out
    have hs : maskSize r + maskSize z + maskSize s + maskSize u = 4 := by
      dsimp [d] at hsum
      omega
    have hcore : maskSize r + maskSize z + maskSize core = 4 := by
      dsimp [d] at hc
      omega
    have h := ResponseCoordinateTransport.actual_high_union_energy b r z s u core extra
      hsu hzu hs hd hr hcore ha event
    have hm : min (4-maskSize r-maskSize z) (maskSize (maskUnion core extra)) = maskSize core := by
      rw [Nat.min_eq_left hj]
      exact hc.symm
    have hextra : maskSize (maskUnion core extra)-maskSize core = maskSize extra := by
      rw [maskUnion_size core extra hd]
      omega
    change responseEnergy b r (maskUnion core extra) event ≤ _ at h
    calc
      _ ≤ nu^(2 * maskSize core) * delta^maskSize extra *
          ((20/q)^(2 * maskSize r) * (6/(5*q))^maskSize core) := h
      _ = _ := by simp only [hm, hextra]; ring

/-- The inactive mask is generated from the actual fixed source. -/
theorem energy_le_of_zero_count (b : AES.State) (r out : Fin 16)
    (hr : MaskDisjoint r out) (hk : maskSize r ≤ activeSourceCount b)
    (event : AES.WordState → Prop) [DecidablePred event] :
    responseEnergy b r out event ≤
      (20/q)^(2 * maskSize r) * (6/(5*q))^(min (activeSourceCount b-maskSize r) (maskSize out)) *
      nu^(2 * min (activeSourceCount b-maskSize r) (maskSize out)) *
      delta^(maskSize out-min (activeSourceCount b-maskSize r) (maskSize out)) := by
  obtain ⟨z,ha,hz⟩ := RestrictedSourceSections.inactive_mask_exists b
  have hw := residualDegree_le (activeSourceMask b)
  change activeSourceCount b ≤ 4 at hw
  have hshort : maskSize r + maskSize z ≤ 4 := by omega
  have hd : 4-maskSize r-maskSize z = activeSourceCount b-maskSize r := by omega
  have h := energy_le_with_inactive_mask b r z out hr hshort ha event
  simpa only [hd] using h

/-- Universal min(d,j) bound, including impossible zero events. No auxiliary
mask witnesses, probabilistic estimates, or response inequalities are premises. -/
theorem energy_le (b : AES.State) (hb : 0 < activeSourceCount b) (r out : Fin 16)
    (hr : MaskDisjoint r out) (event : AES.WordState → Prop) [DecidablePred event] :
    responseEnergy b r out event ≤
      (20/q)^(2 * maskSize r) * (6/(5*q))^(min (activeSourceCount b-maskSize r) (maskSize out)) *
      nu^(2 * min (activeSourceCount b-maskSize r) (maskSize out)) *
      delta^(maskSize out-min (activeSourceCount b-maskSize r) (maskSize out)) := by
  by_cases hk : maskSize r ≤ activeSourceCount b
  · exact energy_le_of_zero_count b r out hr hk event
  · have hzero := ActualRestrictedWordResponse.actual_response_eq_zero b hb r out (by omega) event
    unfold responseEnergy
    rw [hzero]
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]
    have hnu := WordDamping.nu_nonnegative
    have hdelta := WordRestrictedResponse.delta_nonnegative
    have hp : 0 ≤ 20/q := by norm_num [q]
    have hrho : 0 ≤ 6/(5*q) := by norm_num [q]
    positivity

/-- Rounded squared estimate in the manuscript's whole-word constants. -/
theorem rounded_energy_le (b : AES.State) (hb : 0 < activeSourceCount b) (r out : Fin 16)
    (hr : MaskDisjoint r out) (event : AES.WordState → Prop) [DecidablePred event] :
    responseEnergy b r out event ≤
      (6/5 : ℝ)^4 * 20^(2 * maskSize r) *
        nu^(2 * min (activeSourceCount b-maskSize r) (maskSize out)) /
        q^(2 * maskSize r + maskSize out) := by
  apply (energy_le b hb r out hr event).trans
  exact ResponseScalarBounds.squared_bound (maskSize r) (maskSize out)
    (min (activeSourceCount b-maskSize r) (maskSize out)) (Nat.min_le_right _ _)
    ((Nat.min_le_right _ _).trans (ResponseMaskSelection.maskSize_le_four out))

/-- Counting-measure L2 norm, with an exact square-root denominator. -/
theorem response_norm_le (b : AES.State) (hb : 0 < activeSourceCount b) (r out : Fin 16)
    (hr : MaskDisjoint r out) (event : AES.WordState → Prop) [DecidablePred event] :
    Real.sqrt (responseEnergy b r out event) ≤
      (6/5 : ℝ)^2 * 20^maskSize r *
        nu^(min (activeSourceCount b-maskSize r) (maskSize out)) /
        (q^maskSize r * Real.sqrt (q^maskSize out)) :=
  ResponseScalarBounds.sqrt_bound_of_energy (responseEnergy b r out event)
    (maskSize r) (maskSize out) (min (activeSourceCount b-maskSize r) (maskSize out))
    (Nat.min_le_right _ _) ((Nat.min_le_right _ _).trans (ResponseMaskSelection.maskSize_le_four out))
    (responseEnergy_nonnegative b r out event) (energy_le b hb r out hr event)

end AESPaper.UniversalRestrictedResponse
