import AESConcrete.IndexedTripleEnergy
import AESConcrete.ThreeActiveGeometry
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar

/-!
# Full three-active-source Fourier energy

The residual amplitude is one signed function on its original joint source
type. Only the extra uniform coordinate is repeated. The retained additive
equivalence makes the repetition an actual translation invariance, and its
surjective singleton projection supplies the Fourier graph. Raw and normalized
counting energies are stated separately.

Candidate only; no compilation, independent acceptance or physical cap is
asserted. Constructive mathematics only; no attacks. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct pairs
and the fixed 10/14/16 target remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeActiveFourierEnergy
open AESMixing
open AESConcrete.IndexedGraphEnergy

variable {I U V : Type*} [Fintype I] [DecidableEq I] [Fintype U] [Fintype V]

/-- One signed joint residual amplitude, repeated over exactly one source leg. -/
def fullInput (e : (U × V) ≃ (I → V)) (h : U → ℝ) : (I → V) → ℝ :=
  fun x => h (e.symm x).1

/-- The raw full-source response has no uniform normalization hidden in its sum. -/
def fullResponse (e : (U × V) ≃ (I → V)) (T : V → V → ℝ)
    (h : U → ℝ) (y : I → V) : ℝ :=
  ∑ uv : U × V, (∏ i : I, T (y i) (e uv i)) * h uv.1

omit [DecidableEq I] in
/-- The full term in the same raw response interface as the restricted terms. -/
theorem fullResponse_eq_response (e : (U × V) ≃ (I → V))
    (T : V → V → ℝ) (h : U → ℝ) (y : I → V) :
    fullResponse e T h y =
      IndexedTripleEnergy.response T e (fun uv => h uv.1) y := by
  unfold fullResponse IndexedTripleEnergy.response
  apply Finset.sum_congr rfl
  intro uv _
  ring

theorem fullResponse_eq_action (e : (U × V) ≃ (I → V))
    (T : V → V → ℝ) (h : U → ℝ) (y : I → V) :
    fullResponse e T h y =
      action (coordinateKernel (fun _ : I => T)) (fullInput e h) y := by
  have he := e.sum_comp
    (fun x : I → V => (∏ i : I, T (y i) (x i)) * fullInput e h x)
  simpa only [fullResponse, fullInput, Equiv.symm_apply_apply,
    action, coordinateKernel] using he

/-- The sole repeated uniform source leg contributes exactly `card V`. -/
theorem fullInput_energy (e : (U × V) ≃ (I → V)) (h : U → ℝ) :
    (∑ x, fullInput e h x ^ 2) = (Fintype.card V : ℝ) * ∑ u, h u ^ 2 := by
  calc
    (∑ x, fullInput e h x ^ 2) =
        ∑ uv : U × V, fullInput e h (e uv) ^ 2 :=
      (e.sum_comp (fun x => fullInput e h x ^ 2)).symm
    _ = ∑ u : U, ∑ _v : V, h u ^ 2 := by
      simp only [fullInput, Equiv.symm_apply_apply, Fintype.sum_prod_type]
    _ = (Fintype.card V : ℝ) * ∑ u, h u ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

/-- Normalization by the one extra word leg, separate from residual amplitude. -/
def normalizedInput (e : (U × V) ≃ (I → V)) (h : U → ℝ) : (I → V) → ℝ :=
  fun x => fullInput e h x / Real.sqrt (Fintype.card V : ℝ)

theorem normalizedInput_energy [Nonempty V]
    (e : (U × V) ≃ (I → V)) (h : U → ℝ) :
    (∑ x, normalizedInput e h x ^ 2) = ∑ u, h u ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  simp only [normalizedInput, div_pow, ← Finset.sum_div,
    Real.sq_sqrt hcard.le, fullInput_energy]
  field_simp [ne_of_gt hcard]

section Additive
variable [AddCommGroup U] [AddCommGroup V]

omit [Fintype I] [DecidableEq I] [Fintype U] [Fintype V] in
/-- Actual uniform-source translations leave the joint residual tuple fixed. -/
theorem fullInput_translation (e : (U × V) ≃+ (I → V))
    (h : U → ℝ) (x : I → V) (t : V) :
    fullInput e.toEquiv h (x + e (0, t)) = fullInput e.toEquiv h x := by
  change h (e.symm (x + e (0, t))).1 = h (e.symm x).1
  rw [map_add, e.symm_apply_apply]
  change h ((e.symm x).1 + 0) = h (e.symm x).1
  rw [add_zero]

omit [Fintype I] [DecidableEq I] [Fintype U] in
theorem normalizedInput_translation (e : (U × V) ≃+ (I → V))
    (h : U → ℝ) (x : I → V) (t : V) :
    normalizedInput e.toEquiv h (x + e (0, t)) = normalizedInput e.toEquiv h x := by
  simp only [normalizedInput, fullInput_translation e h]

/-- The normalized full source pays two operator factors and one column
factor, all for the actual two-sided Fourier conjugate. -/
theorem normalizedInput_response_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (e : (U × V) ≃+ (I → V)) (s : I)
    (hfree : Fintype.card (FreeCoordinates (fun i : I => i ≠ s)) = 2)
    (hsurj : Function.Surjective (fun t : V => e (0, t) s))
    (T : V → V → ℝ) (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, fourierConjugate B T y v ^ 2) ≤ kappa)
    (h : U → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : I => T))
      (normalizedInput e.toEquiv h) y ^ 2) ≤ rho ^ 4 * kappa * ∑ u, h u ^ 2 := by
  have he := IndexedTripleEnergy.invariant_triple_energy B hchar s hfree
    (fun t => e (0, t)) hsurj T rho kappa hkappa hT hcolumn
    (normalizedInput e.toEquiv h) (normalizedInput_translation e h)
  rw [normalizedInput_energy] at he
  exact he

/-- The raw full response carries exactly one additional counting factor. -/
theorem fullResponse_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (e : (U × V) ≃+ (I → V)) (s : I)
    (hfree : Fintype.card (FreeCoordinates (fun i : I => i ≠ s)) = 2)
    (hsurj : Function.Surjective (fun t : V => e (0, t) s))
    (T : V → V → ℝ) (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, fourierConjugate B T y v ^ 2) ≤ kappa)
    (h : U → ℝ) :
    (∑ y, fullResponse e.toEquiv T h y ^ 2) ≤
      (rho ^ 4 * kappa * (Fintype.card V : ℝ)) * ∑ u, h u ^ 2 := by
  have he := IndexedTripleEnergy.invariant_triple_energy B hchar s hfree
    (fun t => e (0, t)) hsurj T rho kappa hkappa hT hcolumn
    (fullInput e.toEquiv h) (fullInput_translation e h)
  rw [fullInput_energy] at he
  simp_rw [fullResponse_eq_action]
  exact he.trans_eq (by ring)

end Additive

section ActualWord
variable [AddCommGroup U]

/-- Ordinary AES-word resources, including the proved two-sided column bound. -/
theorem word_fullResponse_energy
    (e : (U × AES.Word) ≃+ (I → AES.Word)) (s : I)
    (hfree : Fintype.card (FreeCoordinates (fun i : I => i ≠ s)) = 2)
    (hsurj : Function.Surjective (fun t : AES.Word => e (0, t) s))
    (h : U → ℝ) :
    (∑ y, fullResponse e.toEquiv (residualMatrix AES.wordSuperboxKernel 0) h y ^ 2) ≤
      (UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa * ActivityCodeScalar.q) *
        ∑ u, h u ^ 2 := by
  have hT : ∀ g : AES.Word → ℝ,
      (∑ y, action (fourierConjugate WordFourierCore.wordPairing
        (residualMatrix AES.wordSuperboxKernel 0)) g y ^ 2) ≤
        UniformGraphScalar.rho ^ 2 * ∑ x, g x ^ 2 :=
    WordFourierBounds.fourier_residual_energy_le .ordinary .ordinary false
  have hc : ∀ v : AES.Word,
      (∑ y, fourierConjugate WordFourierCore.wordPairing
        (residualMatrix AES.wordSuperboxKernel 0) y v ^ 2) ≤ UniformGraphScalar.kappa := by
    intro v
    exact (WordFourierBounds.fourier_residual_column_energy_lt
      .ordinary .ordinary false v).le
  have he := fullResponse_energy WordFourierCore.wordPairing word_add_self e s hfree
    hsurj (residualMatrix AES.wordSuperboxKernel 0) UniformGraphScalar.rho
    UniformGraphScalar.kappa UniformGraphScalar.kappa_nonneg hT hc h
  have hcard : (Fintype.card AES.Word : ℝ) = ActivityCodeScalar.q := by
    rw [AES.word_card]
    norm_num [ActivityCodeScalar.q]
  rw [hcard] at he
  exact he

/-- The normalized source estimate with the actual ordinary word kernel. -/
theorem word_normalizedInput_response_energy
    (e : (U × AES.Word) ≃+ (I → AES.Word)) (s : I)
    (hfree : Fintype.card (FreeCoordinates (fun i : I => i ≠ s)) = 2)
    (hsurj : Function.Surjective (fun t : AES.Word => e (0, t) s))
    (h : U → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : I => residualMatrix AES.wordSuperboxKernel 0))
      (normalizedInput e.toEquiv h) y ^ 2) ≤
      UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa * ∑ u, h u ^ 2 := by
  apply normalizedInput_response_energy WordFourierCore.wordPairing word_add_self
    e s hfree hsurj _ _ _ UniformGraphScalar.kappa_nonneg
  · exact WordFourierBounds.fourier_residual_energy_le .ordinary .ordinary false
  · intro v
    exact (WordFourierBounds.fourier_residual_column_energy_lt
      .ordinary .ordinary false v).le

end ActualWord

/-- All geometry premises are discharged for the actual selected supports.
The source amplitude retains the two original residual physical labels. -/
theorem retained_fullResponse_energy
    (pOut : ResidualIncidenceCoefficient.SelectedSupport 3 4)
    (pIn : ResidualIncidenceCoefficient.SelectedSupport 2 3)
    (h : (ThreeActiveSource.ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, fullResponse (ThreeActiveGeometry.retainedEquiv pOut pIn).toEquiv
      (residualMatrix AES.wordSuperboxKernel 0) h y ^ 2) ≤
      (UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa * ActivityCodeScalar.q) *
        ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [ThreeActiveGeometry.retainedCoordinates_card]; norm_num)
  let s : MaskCoordinates pOut.val.val.1 := Classical.choice inferInstance
  apply word_fullResponse_energy (ThreeActiveGeometry.retainedEquiv pOut pIn) s
    (ThreeActiveGeometry.retained_other_card pOut s)
  exact (ThreeActiveGeometry.retained_uniform_coordinate_bijective
    WordCrossZero.wordMixAddEquiv.toAddMonoidHom WordCrossZero.wordMixAddEquiv_zeroMDS
    pIn pOut.val.val.1 s).surjective

/-- Exact normalized full-source response for the actual retained triple. -/
theorem retained_normalizedInput_response_energy
    (pOut : ResidualIncidenceCoefficient.SelectedSupport 3 4)
    (pIn : ResidualIncidenceCoefficient.SelectedSupport 2 3)
    (h : (ThreeActiveSource.ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y, action (coordinateKernel
      (fun _ : MaskCoordinates pOut.val.val.1 => residualMatrix AES.wordSuperboxKernel 0))
      (normalizedInput (ThreeActiveGeometry.retainedEquiv pOut pIn).toEquiv h) y ^ 2) ≤
      UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [ThreeActiveGeometry.retainedCoordinates_card]; norm_num)
  let s : MaskCoordinates pOut.val.val.1 := Classical.choice inferInstance
  apply word_normalizedInput_response_energy (ThreeActiveGeometry.retainedEquiv pOut pIn) s
    (ThreeActiveGeometry.retained_other_card pOut s)
  exact (ThreeActiveGeometry.retained_uniform_coordinate_bijective
    WordCrossZero.wordMixAddEquiv.toAddMonoidHom WordCrossZero.wordMixAddEquiv_zeroMDS
    pIn pOut.val.val.1 s).surjective

end AESConcrete.ThreeActiveFourierEnergy
