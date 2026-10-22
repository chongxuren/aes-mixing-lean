import AESConcrete.ReturnMiddleGeometry
import AESConcrete.IndexedGraphEnergy
import AESConcrete.AllColumnBound
import AESConcrete.WordFourierBounds

/-!
# Four normalized cases of the actual three-coordinate middle estimate

Geometry is imported from ReturnMiddleGeometry; this file supplies the actual
ordinary/Fourier residual resources and derives one energy inequality for
every r,s, both full/zero choices and arbitrary signed joint h. The final
statement has no external analytic resource premise.

Constructive fixed AES10/14/16 with independent uniform retained keys,
whitening, omitted final MixColumns and ordered-distinct reference.

This is the middle estimate only; it does not establish a physical return cap
or complete AES theorem.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ReturnMiddleEnergy
set_option maxRecDepth 100000
open AESMixing
open AESConcrete.ReturnMiddleGeometry
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)
open AESConcrete.WordFourierCore (wordFourier wordPairing wordConjugate)

def rho : ℝ := 21 / 131072
def kappa : ℝ := 2 / (15 * 4294967296)

def residualWord : Word → Word → ℝ := residualMatrix AES.wordSuperboxKernel 0

/-- Channel action on the three original retained labels after the raw slice. -/
def middleResponse (r s : Fin 4) (sourceFull targetFull : Bool) (h : Three → ℝ) :
    Three → ℝ :=
  action (coordinateKernel (fun _ : Fin 3 => residualWord))
    (middleInput wordMixAddEquiv r s sourceFull targetFull h)

theorem residualWord_energy (f : Word → ℝ) :
    (∑ y, action residualWord f y ^ 2) ≤ rho ^ 2 * ∑ x, f x ^ 2 :=
  SharpDampedWordNorm.word_superbox_residual_energy f

theorem residualWord_column (x : Word) :
    (∑ y, residualWord y x ^ 2) ≤ kappa :=
  le_of_lt (AllColumnBound.actual_word_residual_column_energy_lt x)

theorem conjugate_residualWord_energy (f : Word → ℝ) :
    (∑ y, action (wordConjugate residualWord) f y ^ 2) ≤
      rho ^ 2 * ∑ x, f x ^ 2 :=
  WordFourierBounds.fourier_residual_energy_le .ordinary .ordinary false f

theorem conjugate_residualWord_column (x : Word) :
    (∑ y, wordConjugate residualWord y x ^ 2) ≤ kappa :=
  le_of_lt (WordFourierBounds.fourier_residual_column_energy_lt .ordinary .ordinary false x)

section ThreeGraph

-- Label zero is one retained physical coordinate r.succAbove 0. The two
-- other retained labels are free; no original label is replaced by a new one.
private def freeLabel (i : Fin 3) : Prop := i ≠ 0

private instance : DecidablePred freeLabel :=
  fun i => inferInstanceAs (Decidable (i ≠ (0 : Fin 3)))

/-- Specialize the accepted indexed graph theorem to two free retained labels. -/
theorem graph3_energy (K : Word → Word → ℝ) (nu delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hK : ∀ f : Word → ℝ,
      (∑ y, action K f y ^ 2) ≤ nu ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ x, (∑ y, K y x ^ 2) ≤ delta)
    (g : Three → ℝ) (hg : Graph3 g) :
    (∑ y, action (coordinateKernel (fun _ : Fin 3 => K)) g y ^ 2) ≤
      nu ^ 4 * delta * ∑ x, g x ^ 2 := by
  have hf : Fintype.card (IndexedGraphEnergy.FreeCoordinates freeLabel) = 2 := by decide
  have hd : Fintype.card (IndexedGraphEnergy.DependentCoordinates freeLabel) = 1 := by decide
  have he := IndexedGraphEnergy.coordinate_partial_graph_energy
    (fun _ : Fin 3 => K) freeLabel (fun _ => nu) (fun _ => delta)
    (fun _ => hdelta) (fun _ => hK) (fun _ => hcolumn) g (by
      intro w v v' hv hv'
      have hh := hg
        ((IndexedGraphEnergy.splitCoordinates freeLabel).symm (v, w))
        ((IndexedGraphEnergy.splitCoordinates freeLabel).symm (v', w)) hv hv' (by
          intro i hi
          change IndexedGraphEnergy.joinCoordinates freeLabel v w i =
            IndexedGraphEnergy.joinCoordinates freeLabel v' w i
          have hfree : freeLabel i := hi
          dsimp only [IndexedGraphEnergy.joinCoordinates]
          simp only [dif_pos hfree])
      have hfirst := congrArg
        (fun z => ((IndexedGraphEnergy.splitCoordinates freeLabel) z).1) hh
      simpa only [Equiv.apply_symm_apply] using hfirst)
  simp only [Finset.prod_const, Finset.card_univ, hf, hd, pow_one] at he
  convert he using 1 <;> ring

theorem residual_three_graph_energy (g : Three → ℝ) (hg : Graph3 g) :
    (∑ y, action (coordinateKernel (fun _ : Fin 3 => residualWord)) g y ^ 2) ≤
      rho ^ 4 * kappa * ∑ x, g x ^ 2 :=
  graph3_energy residualWord rho kappa (by norm_num [kappa])
    residualWord_energy residualWord_column g hg

/-- The graph premise concerns the actual normalized product-Fourier input. -/
theorem residual_three_fourier_graph_energy (g : Three → ℝ)
    (hg : Graph3 (action (coordinateKernel (fun _ : Fin 3 => wordFourier)) g)) :
    (∑ y, action (coordinateKernel (fun _ : Fin 3 => residualWord)) g y ^ 2) ≤
      rho ^ 4 * kappa * ∑ x, g x ^ 2 := by
  have he := graph3_energy (wordConjugate residualWord) rho kappa
    (by norm_num [kappa]) conjugate_residualWord_energy conjugate_residualWord_column
    (action (coordinateKernel (fun _ : Fin 3 => wordFourier)) g) hg
  have hconj := FourierGraphEnergy.coordinate_fourier_conjugation_energy
    (I := Fin 3) WordFourierCore.wordPairing word_add_self residualWord g
  have hunit := FourierGraphEnergy.coordinate_fourier_input_energy
    (I := Fin 3) WordFourierCore.wordPairing word_add_self g
  change (∑ y, action (coordinateKernel (fun _ : Fin 3 => wordConjugate residualWord))
      (action (coordinateKernel (fun _ : Fin 3 => wordFourier)) g) y ^ 2) =
    ∑ y, action (coordinateKernel (fun _ : Fin 3 => residualWord)) g y ^ 2 at hconj
  change (∑ y, action (coordinateKernel (fun _ : Fin 3 => wordFourier)) g y ^ 2) =
    ∑ x, g x ^ 2 at hunit
  rw [hconj, hunit] at he
  exact he

end ThreeGraph

theorem residual_three_energy (g : Three → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : Fin 3 => residualWord)) g y ^ 2) ≤
      rho ^ 6 * ∑ x, g x ^ 2 := by
  simpa only [Fintype.card_fin, Nat.reduceMul] using
    FiniteTensorEnergy.uniform_coordinate_energy (I := Fin 3)
      residualWord rho residualWord_energy g

theorem zero_zero_middle_energy (r s : Fin 4) (h : Three → ℝ) :
    (∑ y, middleResponse r s false false h y ^ 2) ≤
      rho ^ 4 * kappa * ∑ x, h x ^ 2 := by
  have hg := ReturnMiddleGeometry.zero_zero_middle_graph
    wordMixAddEquiv wordMixAddEquiv_zeroMDS r s h
  have he := residual_three_graph_energy
    (middleInput wordMixAddEquiv r s false false h) hg
  have hi := middleInput_energy_le wordMixAddEquiv
    (by rw [AES.word_card]; norm_num) r s false false h
  exact he.trans (mul_le_mul_of_nonneg_left hi (by norm_num [rho, kappa]))

theorem full_full_middle_energy (r s : Fin 4) (h : Three → ℝ) :
    (∑ y, middleResponse r s true true h y ^ 2) ≤
      rho ^ 4 * kappa * ∑ x, h x ^ 2 := by
  have he := residual_three_fourier_graph_energy
    (middleInput wordMixAddEquiv r s true true h)
    (full_full_middle_fourier_graph r s h)
  have hi := middleInput_energy_le wordMixAddEquiv
    (by rw [AES.word_card]; norm_num) r s true true h
  exact he.trans (mul_le_mul_of_nonneg_left hi (by norm_num [rho, kappa]))

theorem mixed_scalar_bound :
    rho ^ 6 * (1 / 4294967296 : ℝ) ≤ rho ^ 4 * kappa := by
  norm_num [rho, kappa]

theorem zero_full_middle_energy (r s : Fin 4) (h : Three → ℝ) :
    (∑ y, middleResponse r s false true h y ^ 2) ≤
      rho ^ 4 * kappa * ∑ x, h x ^ 2 := by
  have he := residual_three_energy (middleInput wordMixAddEquiv r s false true h)
  rw [ReturnMiddleGeometry.zero_full_middle_energy r s h] at he
  calc
    (∑ y, middleResponse r s false true h y ^ 2)
        ≤ rho ^ 6 * ((1 / 4294967296 : ℝ) * ∑ x, h x ^ 2) := he
    _ = (rho ^ 6 * (1 / 4294967296 : ℝ)) * ∑ x, h x ^ 2 := by ring
    _ ≤ rho ^ 4 * kappa * ∑ x, h x ^ 2 :=
      mul_le_mul_of_nonneg_right mixed_scalar_bound
        (Finset.sum_nonneg (fun x _ => sq_nonneg (h x)))

theorem full_zero_middle_energy (r s : Fin 4) (h : Three → ℝ) :
    (∑ y, middleResponse r s true false h y ^ 2) ≤
      rho ^ 4 * kappa * ∑ x, h x ^ 2 := by
  have he := residual_three_energy (middleInput wordMixAddEquiv r s true false h)
  rw [ReturnMiddleGeometry.full_zero_middle_energy r s h] at he
  calc
    (∑ y, middleResponse r s true false h y ^ 2)
        ≤ rho ^ 6 * ((1 / 4294967296 : ℝ) * ∑ x, h x ^ 2) := he
    _ = (rho ^ 6 * (1 / 4294967296 : ℝ)) * ∑ x, h x ^ 2 := by ring
    _ ≤ rho ^ 4 * kappa * ∑ x, h x ^ 2 :=
      mul_le_mul_of_nonneg_right mixed_scalar_bound
        (Finset.sum_nonneg (fun x _ => sq_nonneg (h x)))

/-- Actual all-four-case middle estimate. No product-input or extra analytic
premise, projection swap through wordMix, or output orthogonality is assumed. -/
theorem middle_energy (r s : Fin 4) (sourceFull targetFull : Bool) (h : Three → ℝ) :
    (∑ y, middleResponse r s sourceFull targetFull h y ^ 2) ≤
      rho ^ 4 * kappa * ∑ x, h x ^ 2 := by
  cases sourceFull <;> cases targetFull
  · exact zero_zero_middle_energy r s h
  · exact zero_full_middle_energy r s h
  · exact full_zero_middle_energy r s h
  · exact full_full_middle_energy r s h

end AESConcrete.ReturnMiddleEnergy
