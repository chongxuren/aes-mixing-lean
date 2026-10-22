import AESConcrete.TwoOmittedOneInputEvents
import AESConcrete.TwoOmittedOneInputSource

/-!
# Original event responses and physical-state transports for (10,12)

Input-zero response is bare; both single-output restrictions and their
intersection retain exactly normalizedSource G. Every equivalence is identity
on physical states. No analytic desired-bound premise, centering or source
replacement is present. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputEventResponses
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOneInputGeometry
open AESConcrete.TwoOmittedOneInputEvents
open AESConcrete.TwoOmittedOneInputSource
open AESConcrete.ShortenedLineResponse (singletonMask)
open AESConcrete.WordCrossZero (wordMixAddEquiv)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def eventResponse (pOut : SelectedSupport 2 4) (r z : Fin 16)
    (mu : ShortenedWeightedGeometry.ShortenedCode wordMixAddEquiv.toAddMonoidHom r z → ℝ) :=
  IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0) (eventRetained pOut r z) mu

def inputZeroDomainResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  eventResponse pOut 0 (singletonMask (inputUniform pIn).val) (fun c => psi pIn h c.val)

def omittedValue (pOut : SelectedSupport 2 4) (a : Omitted pOut) (x : AES.WordState) : AES.Word :=
  wordMixAddEquiv x a.val

def singleConditionalResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :=
  WeightedResponse.zeroResponse (normalizedSource pIn h) (stateKernel pOut) (omittedValue pOut a)

def doubleConditionalResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  TripleResponse.intersectionResponse (normalizedSource pIn h) (stateKernel pOut)
    (omittedValue pOut (omittedFirst pOut)) (omittedValue pOut (omittedSecond pOut))

def singleDomainResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :=
  eventResponse pOut (singletonMask a.val) 0 (fun c => normalizedSource pIn h c.val)

def doubleDomainResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  eventResponse pOut (maskComplement pOut.val.val.1) 0 (fun c => normalizedSource pIn h c.val)

theorem inputZeroResponse_eq_domain (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    inputZeroResponse pOut pIn h = inputZeroDomainResponse pOut pIn h := by
  funext y
  unfold inputZeroResponse WeightedResponse.zeroResponse inputZeroDomainResponse
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (fun x : AES.WordState => x (inputUniform pIn).val = 0),
      psi pIn h x * stateKernel pOut y x) =
    ∑ x : {x : AES.WordState // x (inputUniform pIn).val = 0},
      psi pIn h x.val * stateKernel pOut y x.val from Finset.sum_subtype _ (by simp) _]
  exact (inputRestrictionEquiv pIn).sum_comp
    (fun c : InputZero pIn => psi pIn h c.val * stateKernel pOut y c.val)

theorem singleConditionalResponse_eq_domain (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (a : Omitted pOut) (h : (Residual pIn → AES.Word) → ℝ) :
    singleConditionalResponse pOut pIn a h = singleDomainResponse pOut pIn a h := by
  funext y
  unfold singleConditionalResponse WeightedResponse.zeroResponse singleDomainResponse
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (fun x : AES.WordState => omittedValue pOut a x = 0),
      normalizedSource pIn h x * stateKernel pOut y x) =
    ∑ x : {x : AES.WordState // omittedValue pOut a x = 0},
      normalizedSource pIn h x.val * stateKernel pOut y x.val from Finset.sum_subtype _ (by simp) _]
  exact (singleRestrictionEquiv pOut a).sum_comp
    (fun c : SingleZero pOut a => normalizedSource pIn h c.val * stateKernel pOut y c.val)

theorem doubleConditionalResponse_eq_domain (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    doubleConditionalResponse pOut pIn h = doubleDomainResponse pOut pIn h := by
  funext y
  unfold doubleConditionalResponse TripleResponse.intersectionResponse doubleDomainResponse
  rw [← Finset.sum_filter]
  rw [show (∑ x ∈ Finset.univ.filter (fun x : AES.WordState =>
      omittedValue pOut (omittedFirst pOut) x = 0 ∧ omittedValue pOut (omittedSecond pOut) x = 0),
      normalizedSource pIn h x * stateKernel pOut y x) =
    ∑ x : {x : AES.WordState // omittedValue pOut (omittedFirst pOut) x = 0 ∧
      omittedValue pOut (omittedSecond pOut) x = 0},
      normalizedSource pIn h x.val * stateKernel pOut y x.val from Finset.sum_subtype _ (by simp) _]
  exact (doubleRestrictionEquiv pOut).sum_comp
    (fun c : DoubleZero pOut => normalizedSource pIn h c.val * stateKernel pOut y c.val)

end AESConcrete.TwoOmittedOneInputEventResponses
