import AESConcrete.IndexedTripleEnergy
import AESConcrete.ThreeActiveShortening
import AESConcrete.SharpDampedWordNorm
import AESConcrete.AllColumnBound
import AESConcrete.UniformGraphScalar

/-!
# Two-dimensional shortened responses on three retained labels

A plane's actual projection to two retained labels supplies its free tuple.
The last retained label is a graph value. The original signed amplitude is
reindexed exactly; two operator factors and one column factor give the energy
coefficient. Source normalization, zero-locus geometry and output geometry
remain separate interfaces.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and the fixed 10/14/16 target remain unchanged. No
physical cap or inventory is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeActivePlaneEnergy
open AESMixing
open AESConcrete.IndexedGraphEnergy

variable {I V C : Type*} [Fintype I] [DecidableEq I] [Fintype C] [Fintype V]

omit [Fintype C] [Fintype V] in
/-- The complement of one physical label in a retained triple has size two. -/
theorem otherCoordinates_card (hI : Fintype.card I = 3) (s : I) :
    Fintype.card (FreeCoordinates (fun i : I => i ≠ s)) = 2 := by
  classical
  rw [Fintype.card_subtype_compl (fun i : I => i = s),
    Fintype.card_subtype_eq, hI]

/-- Two residual operator factors and one column factor, with no loss in
the exact source-to-free-tuple reindexing. -/
theorem plane_energy_of_equiv (hI : Fintype.card I = 3) (s : I)
    (T : V → V → ℝ) (curve : C → I → V) (mu : C → ℝ)
    (e : C ≃ (FreeCoordinates (fun i : I => i ≠ s) → V))
    (he : ∀ c i, e c i = curve c i.val)
    (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action T g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, T y v ^ 2) ≤ kappa) :
    (∑ y : I → V, IndexedTripleEnergy.response T curve mu y ^ 2) ≤
      rho ^ 4 * kappa * ∑ c, mu c ^ 2 := by
  have he' := IndexedTripleEnergy.response_energy_of_equiv
    (fun i : I => i ≠ s) T curve mu e he rho kappa hkappa hT hcolumn
  simpa only [Finset.prod_const, Finset.card_univ, otherCoordinates_card hI s,
    IndexedFourierSupport.dependentCoordinates_card, pow_one, ← pow_mul] using he'

/-- A proved physical projection bijection supplies the plane's equivalence. -/
theorem plane_energy_of_bijective (hI : Fintype.card I = 3) (s : I)
    (T : V → V → ℝ) (curve : C → I → V) (mu : C → ℝ)
    (hprojection : Function.Bijective
      (fun c : C => fun i : FreeCoordinates (fun j : I => j ≠ s) => curve c i.val))
    (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action T g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, T y v ^ 2) ≤ kappa) :
    (∑ y : I → V, IndexedTripleEnergy.response T curve mu y ^ 2) ≤
      rho ^ 4 * kappa * ∑ c, mu c ^ 2 :=
  plane_energy_of_equiv hI s T curve mu
    (Equiv.ofBijective _ hprojection) (fun _ _ => rfl)
    rho kappa hkappa hT hcolumn

/-- The amplitude has exactly its original joint residual energy when the
plane projects bijectively to that residual tuple. -/
theorem residual_amplitude_energy {U : Type*} [Fintype U]
    (source : C ≃ U) (h : U → ℝ) :
    (∑ c, h (source c) ^ 2) = ∑ u, h u ^ 2 :=
  source.sum_comp (fun u => h u ^ 2)

section ActualWord
variable {C : Type*} [Fintype C]

/-- Actual AES residual resources discharge both analytic premises. -/
theorem word_plane_energy_of_bijective
    (hI : Fintype.card I = 3) (s : I)
    (curve : C → I → AES.Word) (mu : C → ℝ)
    (hprojection : Function.Bijective
      (fun c : C => fun i : FreeCoordinates (fun j : I => j ≠ s) => curve c i.val)) :
    (∑ y : I → AES.Word,
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0) curve mu y ^ 2) ≤
      UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa * ∑ c, mu c ^ 2 := by
  apply plane_energy_of_bijective hI s _ curve mu hprojection
    UniformGraphScalar.rho UniformGraphScalar.kappa UniformGraphScalar.kappa_nonneg
  · exact SharpDampedWordNorm.word_superbox_residual_energy
  · intro v
    exact (AllColumnBound.actual_word_residual_column_energy_lt v).le

/-- Both shortened planes may use this same original signed `h`; there is
no independent-coordinate or source-fiber factor. -/
theorem word_plane_residual_energy {U : Type*} [Fintype U]
    (hI : Fintype.card I = 3) (s : I)
    (curve : C → I → AES.Word) (source : C ≃ U) (h : U → ℝ)
    (hprojection : Function.Bijective
      (fun c : C => fun i : FreeCoordinates (fun j : I => j ≠ s) => curve c i.val)) :
    (∑ y : I → AES.Word, IndexedTripleEnergy.response
      (residualMatrix AES.wordSuperboxKernel 0) curve (fun c => h (source c)) y ^ 2) ≤
      UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa * ∑ u, h u ^ 2 := by
  have he := word_plane_energy_of_bijective hI s curve (fun c => h (source c)) hprojection
  rw [residual_amplitude_energy source h] at he
  exact he

end ActualWord

/-- The actual uniform-input-zero plane with the full original residual energy. -/
theorem retained_vPlane_energy
    (pOut : ResidualIncidenceCoefficient.SelectedSupport 3 4)
    (pIn : ResidualIncidenceCoefficient.SelectedSupport 2 3)
    (h : (ThreeActiveSource.ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y : MaskCoordinates pOut.val.val.1 → AES.Word,
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (fun uv : ThreeActiveShortening.vPlane (V := AES.Word) pIn =>
          ThreeActiveGeometry.sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom
            pIn pOut.val.val.1 uv.val)
        (fun uv => h uv.val.1) y ^ 2) ≤
      UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [ThreeActiveGeometry.retainedCoordinates_card]; norm_num)
  let s : MaskCoordinates pOut.val.val.1 := Classical.choice inferInstance
  have he := word_plane_energy_of_bijective
    (ThreeActiveGeometry.retainedCoordinates_card pOut) s
    (fun uv : ThreeActiveShortening.vPlane (V := AES.Word) pIn =>
      ThreeActiveGeometry.sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn pOut.val.val.1 uv.val)
    (fun uv => h uv.val.1)
    (ThreeActiveShortening.vPlane_retained_pair_bijective
      WordCrossZero.wordMixAddEquiv.toAddMonoidHom WordCrossZero.wordMixAddEquiv_zeroMDS
      pOut pIn s)
  rw [ThreeActiveShortening.vPlane_residual_energy] at he
  exact he

/-- The actual omitted-output-zero plane uses the same arbitrary signed `h`.
Its residual-pair projection is bijective, so there is no fiber loss. -/
theorem retained_zeroPlane_energy
    (pOut : ResidualIncidenceCoefficient.SelectedSupport 3 4)
    (pIn : ResidualIncidenceCoefficient.SelectedSupport 2 3)
    (h : (ThreeActiveSource.ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y : MaskCoordinates pOut.val.val.1 → AES.Word,
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (fun uv : ThreeActiveShortening.zeroPlane WordCrossZero.wordMixAddEquiv.toAddMonoidHom
          pIn (ThreeActiveGeometry.omittedLabel pOut) =>
          ThreeActiveGeometry.sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom
            pIn pOut.val.val.1 uv.val)
        (fun uv => h uv.val.1) y ^ 2) ≤
      UniformGraphScalar.rho ^ 4 * UniformGraphScalar.kappa * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [ThreeActiveGeometry.retainedCoordinates_card]; norm_num)
  let s : MaskCoordinates pOut.val.val.1 := Classical.choice inferInstance
  have he := word_plane_energy_of_bijective
    (ThreeActiveGeometry.retainedCoordinates_card pOut) s
    (fun uv : ThreeActiveShortening.zeroPlane WordCrossZero.wordMixAddEquiv.toAddMonoidHom
      pIn (ThreeActiveGeometry.omittedLabel pOut) =>
      ThreeActiveGeometry.sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn pOut.val.val.1 uv.val)
    (fun uv => h uv.val.1)
    (ThreeActiveShortening.zeroPlane_retained_pair_bijective
      WordCrossZero.wordMixAddEquiv.toAddMonoidHom WordCrossZero.wordMixAddEquiv_zeroMDS
      pOut pIn s)
  rw [ThreeActiveShortening.zeroPlane_residual_energy
    WordCrossZero.wordMixAddEquiv.toAddMonoidHom WordCrossZero.wordMixAddEquiv_zeroMDS] at he
  exact he

end AESConcrete.ThreeActivePlaneEnergy
