import AESConcrete.TwoOmittedOneInputEventResponses
import AESConcrete.ActivityMinorContraction
import AESConcrete.ActivityMinor

/-!
# Original actual minor and its exact two-output split

Both original omitted output U factors are charged once. The one original
input U factor stays inside each W term. Reindexing uses actual M, retaining
original masks and signed h. No response bound is assumed by this finite
identity component. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputSplit
open AESMixing
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOneInputGeometry
open AESConcrete.TwoOmittedOneInputSource
open AESConcrete.TwoOmittedOneInputEventResponses
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates)
open AESConcrete.NonzeroUniformGraphCap (nonzeroUniform)
open AESConcrete.WordCrossZero (wordMixAddEquiv)
open AESConcrete.ActivityMinor
open AESConcrete.ActivityMinorContraction (minorResponse minorKernel nonzeroWeight)
open AESConcrete.ActivityCodeScalar (q)

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

theorem counting_prod_instances {X : Type*} (a b : Fintype X) (f : X → ℝ) :
    (letI := a; ∏ x, f x) = (letI := b; ∏ x, f x) := by
  have he : a = b := Subsingleton.elim _ _
  cases he
  rfl

def outputUniformWeight (pOut : SelectedSupport 2 4) (x : AES.WordState) : ℝ :=
  ∏ a : Omitted pOut, nonzeroUniform (x a.val)

theorem outputUniformWeight_eq_two (pOut : SelectedSupport 2 4) (x : AES.WordState) :
    outputUniformWeight pOut x = nonzeroUniform (x (omittedFirst pOut).val) *
      nonzeroUniform (x (omittedSecond pOut).val) := by
  have he := (omittedIndexEquiv pOut).symm.prod_comp
    (fun a : Omitted pOut => nonzeroUniform (x a.val))
  simpa only [Fin.prod_univ_two, omittedFirst, omittedSecond, outputUniformWeight] using he.symm

theorem omittedWeight_product (pOut : SelectedSupport 2 4) (x : AES.WordState) :
    (∏ j : OtherCoordinates pOut.val.val.1,
      nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut) j (x j.val)) =
        outputUniformWeight pOut x := by
  unfold outputUniformWeight
  apply Finset.prod_congr rfl
  intro j _
  simp only [nonzeroWeight, selectedZeros, output_inactive_not pOut j.val,
    Bool.false_eq_true, if_false]

def omittedResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ x : AES.WordState, normalizedSource pIn h x *
    outputUniformWeight pOut (wordMixAddEquiv x) * stateKernel pOut y x

theorem omittedResponse_eq_two (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    omittedResponse pOut pIn h = TripleResponse.weightedResponse
      (normalizedSource pIn h) (stateKernel pOut)
      (omittedValue pOut (omittedFirst pOut)) (omittedValue pOut (omittedSecond pOut)) := by
  funext y
  unfold omittedResponse TripleResponse.weightedResponse
  apply Finset.sum_congr rfl
  intro x _
  rw [outputUniformWeight_eq_two]
  unfold omittedValue
  ring

theorem omittedResponse_eq_split (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :
    omittedResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y -
        singleConditionalResponse pOut pIn (omittedFirst pOut) h y -
        singleConditionalResponse pOut pIn (omittedSecond pOut) h y + doubleConditionalResponse pOut pIn h y) /
          (q - 1) := by
  rw [omittedResponse_eq_two, TripleResponse.weightedResponse_eq_four]
  -- The exact word cardinal is available without adding a Fourier-energy import.
  have hcard : (Fintype.card AES.Word : ℝ) = q := by
    rw [AES.word_card]
    norm_num [q]
  have hn := TripleResponse.normalizer_eq AES.Word AES.word_card_gt_one.le
  rw [hcard] at hn
  funext y
  change (inputWeightedResponse pOut pIn h y -
    singleConditionalResponse pOut pIn (omittedFirst pOut) h y -
    singleConditionalResponse pOut pIn (omittedSecond pOut) h y +
    doubleConditionalResponse pOut pIn h y) / TripleResponse.normalizer AES.Word = _
  rw [hn]

def actualResponse (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (h : (Residual pIn → AES.Word) → ℝ) :=
  minorResponse (selectedRetained 2 4 pOut) (fun _ => residualMatrix AES.wordSuperboxKernel 0)
    (nonzeroWeight (selectedRetained 2 4 pOut) (selectedZeros 2 4 pOut))
    (fun x => normalizedSource pIn h (wordMixAddEquiv.symm x))

theorem actualResponse_eq_omittedResponse (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = omittedResponse pOut pIn h := by
  unfold actualResponse selectedRetained
  funext y
  unfold minorResponse action minorKernel
  rw [← wordMixAddEquiv.toEquiv.sum_comp]
  have hcoe (x : AES.WordState) : wordMixAddEquiv.toEquiv x = wordMixAddEquiv x := rfl
  simp only [hcoe, AddEquiv.symm_apply_apply]
  unfold omittedResponse
  apply Finset.sum_congr rfl
  intro x _
  have hw := omittedWeight_product pOut (wordMixAddEquiv x)
  unfold selectedRetained at hw
  rw [counting_prod_instances (X := OtherCoordinates pOut.val.val.1) _ inferInstance, hw]
  unfold stateKernel
  rw [counting_prod_instances (X := Retained pOut) _ inferInstance]
  -- The hom evaluates at the original physical retained label.
  have hr (j : Retained pOut) :
      retainedHom pOut x j = wordMixAddEquiv x j.val := rfl
  simp_rw [hr]
  ring

theorem actualResponse_eq_split (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (h : (Residual pIn → AES.Word) → ℝ) :
    actualResponse pOut pIn h = fun y =>
      (inputWeightedResponse pOut pIn h y -
        singleConditionalResponse pOut pIn (omittedFirst pOut) h y -
        singleConditionalResponse pOut pIn (omittedSecond pOut) h y + doubleConditionalResponse pOut pIn h y) /
          (q - 1) := by
  rw [actualResponse_eq_omittedResponse, omittedResponse_eq_split]

end AESConcrete.TwoOmittedOneInputSplit
