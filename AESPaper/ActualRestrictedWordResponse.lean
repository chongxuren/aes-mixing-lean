import AESPaper.ActualRestrictedSource
import AESPaper.WordRestrictedResponse

/-!
# Actual restricted-word responses with explicit information-set witnesses

These bounds compose the actual shortened source with the actual whole-word
residual. The low branch uses nonnegative marginal energy before applying R;
the high branch uses a bijective core output and arbitrary dependent extra
outputs. Masks are explicit witnesses, not assumptions on output independence.
Uniform mask selection and conversion to the paper's single min(d,j) formula
remain separate assembly obligations. No normalization, attacks, manuscript
edits, or full-initialization claim occurs.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
open scoped BigOperators
namespace AESPaper.ActualRestrictedWordResponse
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESPaper.StartingWord (q sourceInput)
open AESPaper.WordDamping (nu)
open AESPaper.RestrictedSourceSections
open AESPaper.WordRestrictedResponse (residual delta)

/-- Fewer observed residual coordinates than free source symbols. -/
theorem shortened_low_energy (b : AES.State) (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : Source r z → Prop) [DecidablePred event] :
    (∑ y, WordColumnGram.tensorResponse
      (fun _ : MaskCoordinates out => residual) (outputCoordinates r z out)
      (density b r z event) y ^ 2) ≤
      nu^(2 * maskSize out) * (20/q)^(2 * maskSize r) * (6/(5*q))^maskSize out := by
  rw [ActualRestrictedResponse.tensorResponse_eq_action_marginal]
  have hm := marginal_energy_le b r z s u out hsu hzu hsize hr hobs ha event
  have ht := WordRestrictedResponse.residual_coordinate_energy
    (RestrictedMarginalEnergy.marginal (outputCoordinates r z out) (density b r z event))
  rw [maskCoordinates_card] at ht
  calc
    _ ≤ nu^(2 * maskSize out) * ∑ y,
        RestrictedMarginalEnergy.marginal (outputCoordinates r z out) (density b r z event) y ^ 2 := ht
    _ ≤ nu^(2 * maskSize out) *
        ((20/q)^(2 * maskSize r) * (6/(5*q))^maskSize out) :=
      mul_le_mul_of_nonneg_left hm (pow_nonneg WordDamping.nu_nonnegative _)
    _ = _ := by ring

/-- Actual marked outputs supply a bijective core, never an arbitrary presumed
labeling. Additional response coordinates may depend on the same source. -/
theorem shortened_high_energy {J : Type*} [Fintype J] [DecidableEq J]
    (b : AES.State) (r z s u core : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r core)
    (hcore : maskSize r + maskSize z + maskSize core = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : Source r z → Prop) [DecidablePred event]
    (rest : Source r z → J → AES.Word) :
    (∑ y, WordColumnGram.tensorResponse
      (fun _ : MaskCoordinates core ⊕ J => residual)
      (fun c => Sum.elim (outputCoordinates r z core c) (rest c))
      (density b r z event) y ^ 2) ≤
      nu^(2 * maskSize core) * delta^Fintype.card J *
        ((20/q)^(2 * maskSize r) * (6/(5*q))^maskSize core) := by
  let e : Source r z ≃ (MaskCoordinates core → AES.Word) := Equiv.ofBijective
    (outputCoordinates r z core) (output_projection_bijective r z core hr hcore)
  have hc : maskSize s + maskSize u = maskSize core := by omega
  have he := density_energy_le b r z s u hsu hzu hsize ha event
  rw [hc] at he
  have h := WordRestrictedResponse.split_response_energy_of_source_bound e rest
    (density b r z event) _ he
  rw [maskCoordinates_card] at h
  have hT : Sum.elim (fun _ : MaskCoordinates core => WordRestrictedResponse.residual)
      (fun _ : J => WordRestrictedResponse.residual) =
      (fun _ : MaskCoordinates core ⊕ J => WordRestrictedResponse.residual) := by
    funext i
    cases i <;> rfl
  have he (c : Source r z) : e c = outputCoordinates r z core c := rfl
  simp only [RestrictedResponseEnergy.splitResponse, hT, he] at h
  exact h

/-- The low-observation bound for the actual joint-event marginal h_D. -/
theorem actual_low_energy (b : AES.State) (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : AES.WordState → Prop) [DecidablePred event] :
    (∑ y, action (coordinateKernel (fun _ : MaskCoordinates out => residual))
      (ActualRestrictedSource.markedMarginal b r out event) y ^ 2) ≤
      nu^(2 * maskSize out) * (20/q)^(2 * maskSize r) * (6/(5*q))^maskSize out := by
  have h := shortened_low_energy b r z s u out hsu hzu hsize hr hobs ha
    (fun c => event c.val)
  rw [ActualRestrictedResponse.tensorResponse_eq_action_marginal,
    ActualRestrictedSource.shortened_output_marginal_eq_actual b r z out ha event] at h
  exact h

/-- Exact transport of any marked boundary coordinates, including a core and
extra coordinates, with an arbitrary further event on the source tuple. -/
theorem actual_response_identity {I : Type*} [Fintype I] [DecidableEq I]
    (b : AES.State) (r z : Fin 16)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : AES.WordState → Prop) [DecidablePred event]
    (coord : AES.WordState → I → AES.Word) :
    WordColumnGram.tensorResponse (fun _ : I => residual)
      (fun c : Source r z => coord (GroupedRecurrence.boundary c.val))
      (density b r z (fun c => event c.val)) =
    action (coordinateKernel (fun _ : I => residual))
      (RestrictedMarginalEnergy.marginal coord
        (ActualRestrictedSource.boundaryRestriction b r event)) := by
  rw [ActualRestrictedResponse.tensorResponse_eq_action_marginal,
    ActualRestrictedSource.shortened_marginal_eq_full b r z ha event
      (fun x => coord (GroupedRecurrence.boundary x)),
    ActualRestrictedSource.full_marginal_eq_boundary b r event coord]

/-- Actual h_D on a core plus dependent extra coordinates. In the paper the
extra map selects the remaining marked outputs. No independence is imposed. -/
theorem actual_high_energy {J : Type*} [Fintype J] [DecidableEq J]
    (b : AES.State) (r z s u core : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r core)
    (hcore : maskSize r + maskSize z + maskSize core = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : AES.WordState → Prop) [DecidablePred event]
    (extra : AES.WordState → J → AES.Word) :
    (∑ y, action (coordinateKernel (fun _ : MaskCoordinates core ⊕ J => residual))
      (RestrictedMarginalEnergy.marginal
        (fun x => Sum.elim (ActualRestrictedSource.markedCoordinates core x) (extra x))
        (ActualRestrictedSource.boundaryRestriction b r event)) y ^ 2) ≤
      nu^(2 * maskSize core) * delta^Fintype.card J *
        ((20/q)^(2 * maskSize r) * (6/(5*q))^maskSize core) := by
  have h := shortened_high_energy b r z s u core hsu hzu hsize hr hcore ha
    (fun c => event c.val) (fun c => extra (GroupedRecurrence.boundary c.val))
  have he := actual_response_identity b r z ha event
    (fun x => Sum.elim (ActualRestrictedSource.markedCoordinates core x) (extra x))
  rw [← he]
  exact h

/-- The impossible-event branch also vanishes after the signed residual. -/
theorem actual_response_eq_zero (b : AES.State)
    (hb : 0 < ManySourceBounds.activeSourceCount b) (r out : Fin 16)
    (hr : ManySourceBounds.activeSourceCount b ≤ maskSize r)
    (event : AES.WordState → Prop) [DecidablePred event] :
    action (coordinateKernel (fun _ : MaskCoordinates out => residual))
      (ActualRestrictedSource.markedMarginal b r out event) = 0 := by
  rw [ActualRestrictedSource.markedMarginal_eq_zero b hb r out hr event]
  funext y
  simp [action]

end AESPaper.ActualRestrictedWordResponse
