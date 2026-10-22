import AESConcrete.TwoOmittedThreeInputGeometry

/-!
# Bare original input events, transported by physical-state identity

Each singleton uses the included raw module's bare cancellation. Each pair is
its Fourier-plane single event; the triple is its ordinary graph-line double
event. The actual proofs are included. No (10,6) weighted-response or physical
theorem is assumed. Every sum keeps the same signed h and the same physical
labels. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedThreeInputEvents
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedThreeInputGeometry
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityCodeScalar (q)
open AESConcrete.UniformGraphScalar (rho kappa)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def inputConditions (z : Fin 16) (x : AES.WordState) : Prop :=
  ∀ i, maskBit z i = true → x i = 0

theorem inputConditions_singleton (i : Fin 4) (x : AES.WordState) :
    inputConditions (singletonMask i) x ↔ x i = 0 := by
  constructor
  · intro hx; exact hx i ((singletonMask_bit _ _).mpr rfl)
  · intro hx j hj; rw [(singletonMask_bit _ _).mp hj]; exact hx

theorem inputConditions_union (z w : Fin 16) (x : AES.WordState) :
    inputConditions (maskUnion z w) x ↔ inputConditions z x ∧ inputConditions w x := by
  constructor
  · intro hx
    constructor
    · intro i hi; apply hx i; rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl hi
    · intro i hi; apply hx i; rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inr hi
  · rintro ⟨hz, hw⟩ i hi
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    exact hi.elim (hz i) (hw i)

def maskRestrictionEquiv (pOut : SelectedSupport 2 4) (z : Fin 16) :
    {x : AES.WordState // inputConditions z x} ≃
      ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 z where
  -- Keep the subtype proof in its own tactic block: the predecessor's
  -- inline constructor/bullet layout was rejected by the parser.
  toFun x := by
    refine ⟨x.val, ?_⟩
    constructor
    · intro i hi
      exact (output_inactive_not pOut i hi).elim
    · exact x.property
  invFun x := ⟨x.val, x.property.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def maskResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (z : Fin 16) (h : (Residual pIn → AES.Word) → ℝ)
    (y : Retained pOut → AES.Word) : ℝ :=
  ∑ c : ShortenedCode wordMixAddEquiv.toAddMonoidHom pOut.val.val.2 z,
    h (residualTuple pIn c.val) * stateKernel pOut y c.val

theorem maskResponse_eq_conditional (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (z : Fin 16)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) :
    maskResponse pOut pIn z h y = ∑ x : AES.WordState,
      if inputConditions z x then h (residualTuple pIn x) * stateKernel pOut y x else 0 := by
  symm
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (inputConditions z),
      h (residualTuple pIn x) * stateKernel pOut y x) =
    ∑ x : {x : AES.WordState // inputConditions z x},
      h (residualTuple pIn x.val) * stateKernel pOut y x.val from
        Finset.sum_subtype _ (by simp) _]
  exact (maskRestrictionEquiv pOut z).sum_comp
    (fun c => h (residualTuple pIn c.val) * stateKernel pOut y c.val)

def singleResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u : SourceUniformPositions pIn) (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.zeroResponse (fun x => h (residualTuple pIn x))
    (stateKernel pOut) (fun x => x u.val.val)

def pairResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u v : SourceUniformPositions pIn) (h : (Residual pIn → AES.Word) → ℝ) :=
  TwoOutputThreeUniformCaps.pairResponse (fun x => h (residualTuple pIn x))
    (stateKernel pOut) (fun x => x u.val.val) (fun x => x v.val.val)

def tripleResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u v w : SourceUniformPositions pIn) (h : (Residual pIn → AES.Word) → ℝ) :=
  TwoOutputThreeUniformCaps.tripleResponse (fun x => h (residualTuple pIn x))
    (stateKernel pOut) (fun x => x u.val.val) (fun x => x v.val.val) (fun x => x w.val.val)

theorem singleResponse_eq_raw (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) :
    singleResponse pOut pIn u h =
      TwoOmittedOutputRawResponse.bareResponse pOut (inputZero pIn u) h := by
  funext y
  change singleResponse pOut pIn u h y = maskResponse pOut pIn (singletonMask u.val.val) h y
  rw [maskResponse_eq_conditional]
  simp only [singleResponse, WeightedResponse.zeroResponse, inputConditions_singleton]

theorem singleResponse_eq_zero (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 1 4) (u : SourceUniformPositions pIn)
    (h : (Residual pIn → AES.Word) → ℝ) : singleResponse pOut pIn u h = 0 := by
  rw [singleResponse_eq_raw, TwoOmittedOutputRawResponse.bareResponse_eq_zero]

theorem pairResponse_eq_raw (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    pairResponse pOut pIn u v h = TwoOmittedOutputRawInputEvents.eventResponse
      pOut (inputZero pIn u)
      (TwoOmittedOutputRawInputEvents.singleMask (remainingUniform pIn u v huv)) h := by
  funext y
  change pairResponse pOut pIn u v h y = maskResponse pOut pIn
    (maskUnion (singletonMask u.val.val) (singletonMask v.val.val)) h y
  rw [maskResponse_eq_conditional]
  simp only [pairResponse, TwoOutputThreeUniformCaps.pairResponse,
    inputConditions_union, inputConditions_singleton]

theorem tripleResponse_eq_raw (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u v w : SourceUniformPositions pIn) (huv : u ≠ v) (huw : u ≠ w)
    (h : (Residual pIn → AES.Word) → ℝ) :
    tripleResponse pOut pIn u v w h = TwoOmittedOutputRawInputEvents.eventResponse
      pOut (inputZero pIn u) (TwoOmittedOutputRawInputEvents.doubleMask
        (remainingUniform pIn u v huv) (remainingUniform pIn u w huw)) h := by
  funext y
  change tripleResponse pOut pIn u v w h y = maskResponse pOut pIn
    (maskUnion (singletonMask u.val.val)
      (maskUnion (singletonMask v.val.val) (singletonMask w.val.val))) h y
  rw [maskResponse_eq_conditional]
  simp only [tripleResponse, TwoOutputThreeUniformCaps.tripleResponse,
    inputConditions_union, inputConditions_singleton]

/--
The raw module supplies actual retained injectivity, invariant-source
translations, two-sided Fourier bounds, and source energy q*sum h².
-/
theorem pairResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u v : SourceUniformPositions pIn) (huv : u ≠ v)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, pairResponse pOut pIn u v h y ^ 2) ≤
      (q * rho ^ 2 * kappa) * ∑ r, h r ^ 2 := by
  rw [pairResponse_eq_raw pOut pIn u v huv]
  exact TwoOmittedOutputRawInputEventEnergy.single_response_energy
    pOut (inputZero pIn u) (remainingUniform pIn u v huv) h

/-- The triple event is retained as a genuine graph line; its source energy
includes h(0)², with no source-zero or vanishing-kernel premise. -/
theorem tripleResponse_energy (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 1 4)
    (u v w : SourceUniformPositions pIn) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h : (Residual pIn → AES.Word) → ℝ) :
    (∑ y, tripleResponse pOut pIn u v w h y ^ 2) ≤
      (rho ^ 2 * kappa) * ∑ r, h r ^ 2 := by
  rw [tripleResponse_eq_raw pOut pIn u v w huv huw]
  exact TwoOmittedOutputRawInputEventEnergy.double_response_energy
    pOut (inputZero pIn u) (remainingUniform pIn u v huv) (remainingUniform pIn u w huw)
    (remainingUniform_ne pIn u v w huv huw hvw) h

end AESConcrete.TwoOmittedThreeInputEvents
