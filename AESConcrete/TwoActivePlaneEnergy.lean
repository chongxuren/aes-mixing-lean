import AESConcrete.IndexedFourierSupport
import AESConcrete.UniformGraphScalar
import AESConcrete.ActivityCodeScalar
import AESConcrete.TwoActiveGeometry

/-!
# Signed plane response on two retained coordinates

The retained-pair equivalence and its uniform-coordinate surjectivity are
explicit geometry inputs. The raw plane input repeats the same signed
amplitude over the second source coordinate, so its counting energy is
exactly the alphabet cardinality times the original energy. Fourier graph
support then saves one residual operator factor. No physical cap is asserted.

Constructive AES 10/14/16 continuation only; no attacks, manuscript edits,
or changes to the fixed independent-retained-key experiment.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TwoActivePlaneEnergy
open AESMixing
open AESConcrete.IndexedGraphEnergy

variable {I V : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Fintype V]

/-- The same signed residual amplitude on every point of the source plane. -/
def planeInput (e : (V × V) ≃ (I → V)) (h : V → ℝ) : (I → V) → ℝ :=
  fun x => h (e.symm x).1

/-- Raw response with no source or output normalization hidden in the sum. -/
def planeResponse (e : (V × V) ≃ (I → V)) (T : V → V → ℝ)
    (h : V → ℝ) (y : I → V) : ℝ :=
  ∑ uv : V × V, (∏ i : I, T (y i) (e uv i)) * h uv.1

omit [AddCommGroup V] in
theorem planeResponse_eq_action (e : (V × V) ≃ (I → V))
    (T : V → V → ℝ) (h : V → ℝ) (y : I → V) :
    planeResponse e T h y =
      action (coordinateKernel (fun _ : I => T)) (planeInput e h) y := by
  have he := e.sum_comp
    (fun x : I → V => (∏ i : I, T (y i) (x i)) * planeInput e h x)
  simpa only [planeResponse, planeInput, Equiv.symm_apply_apply,
    action, coordinateKernel] using he

omit [AddCommGroup V] in
/-- The factor `card V` is the exact count of the free uniform source
coordinate. It is not an upper bound or a replacement of the physical plane. -/
theorem planeInput_energy (e : (V × V) ≃ (I → V)) (h : V → ℝ) :
    (∑ x, planeInput e h x ^ 2) = (Fintype.card V : ℝ) * ∑ u, h u ^ 2 := by
  calc
    (∑ x, planeInput e h x ^ 2) =
        ∑ uv : V × V, planeInput e h (e uv) ^ 2 :=
      (e.sum_comp (fun x => planeInput e h x ^ 2)).symm
    _ = ∑ u : V, ∑ _v : V, h u ^ 2 := by
      simp only [planeInput, Equiv.symm_apply_apply, Fintype.sum_prod_type]
    _ = (Fintype.card V : ℝ) * ∑ u, h u ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]

omit [Fintype I] [DecidableEq I] [Fintype V] in
/-- In the actual retained coordinates the uniform source direction acts
by translation and leaves the first source coordinate unchanged. -/
theorem planeInput_translation (e : (V × V) ≃+ (I → V))
    (h : V → ℝ) (x : I → V) (t : V) :
    planeInput e.toEquiv h (x + e (0, t)) = planeInput e.toEquiv h x := by
  change h (e.symm (x + e (0, t))).1 = h (e.symm x).1
  rw [map_add, e.symm_apply_apply]
  change h ((e.symm x).1 + 0) = h (e.symm x).1
  rw [add_zero]

/-- One operator factor and one column factor for the raw plane response.
Both are resources for the actual two-sided Fourier conjugate of `T`. -/
theorem planeResponse_energy
    (B : CharacterPairing V) (hchar : ∀ v : V, v + v = 0)
    (e : (V × V) ≃+ (I → V)) (s : I)
    (hfree : Fintype.card (FreeCoordinates (fun i : I => i ≠ s)) = 1)
    (hsurj : Function.Surjective (fun t : V => e (0, t) s))
    (T : V → V → ℝ) (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, fourierConjugate B T y v ^ 2) ≤ kappa)
    (h : V → ℝ) :
    (∑ y, planeResponse e.toEquiv T h y ^ 2) ≤
      (rho ^ 2 * kappa * (Fintype.card V : ℝ)) * ∑ u, h u ^ 2 := by
  have he := IndexedFourierSupport.invariant_pair_energy B hchar s hfree
    (fun t => e (0, t)) hsurj T rho kappa hkappa hT hcolumn
    (planeInput e.toEquiv h) (planeInput_translation e h)
  rw [planeInput_energy] at he
  simp_rw [planeResponse_eq_action]
  exact he.trans_eq (by ring)

/-- Actual AES residual resources, still with an explicit retained geometry
interface. A later geometry specialization must discharge that interface. -/
theorem word_planeResponse_energy
    (e : (AES.Word × AES.Word) ≃+ (I → AES.Word)) (s : I)
    (hfree : Fintype.card (FreeCoordinates (fun i : I => i ≠ s)) = 1)
    (hsurj : Function.Surjective (fun t : AES.Word => e (0, t) s))
    (h : AES.Word → ℝ) :
    (∑ y, planeResponse e.toEquiv (residualMatrix AES.wordSuperboxKernel 0) h y ^ 2) ≤
      (UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa * ActivityCodeScalar.q) *
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
  have he := planeResponse_energy WordFourierCore.wordPairing word_add_self e s hfree
    hsurj (residualMatrix AES.wordSuperboxKernel 0) UniformGraphScalar.rho
    UniformGraphScalar.kappa UniformGraphScalar.kappa_nonneg hT hc h
  have hcard : (Fintype.card AES.Word : ℝ) = ActivityCodeScalar.q := by
    rw [AES.word_card]
    norm_num [ActivityCodeScalar.q]
  rw [hcard] at he
  exact he

/-- The concrete two-input/two-retained-output MDS geometry discharges all
translation and cardinality premises. Only the selected physical supports
and the original signed amplitude remain as inputs. -/
theorem retained_planeResponse_energy
    (pOut : ResidualIncidenceCoefficient.SelectedSupport 2 4)
    (pIn : ResidualIncidenceCoefficient.SelectedSupport 1 2)
    (h : AES.Word → ℝ) :
    (∑ y, planeResponse (TwoActiveGeometry.retainedEquiv pOut pIn).toEquiv
      (residualMatrix AES.wordSuperboxKernel 0) h y ^ 2) ≤
      (UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa * ActivityCodeScalar.q) *
        ∑ u, h u ^ 2 := by
  classical
  have hcard : Fintype.card (MaskCoordinates pOut.val.val.1) = 2 := by
    rw [maskCoordinates_card, TwoActiveGeometry.retainedMask_size]
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [hcard]; norm_num)
  let s : MaskCoordinates pOut.val.val.1 := Classical.choice inferInstance
  apply word_planeResponse_energy (TwoActiveGeometry.retainedEquiv pOut pIn) s
    (TwoActiveGeometry.pair_other_card _ (TwoActiveGeometry.retainedMask_size pOut) s)
  exact (TwoActiveGeometry.retained_uniform_coordinate_bijective
    WordCrossZero.wordMixAddEquiv.toAddMonoidHom WordCrossZero.wordMixAddEquiv_zeroMDS
    pIn pOut.val.val.1 s).surjective

end AESConcrete.TwoActivePlaneEnergy
