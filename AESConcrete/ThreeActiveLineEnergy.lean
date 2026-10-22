import AESConcrete.ThreeActivePlaneEnergy

/-!
# Intersection-line energy on three retained physical labels

One actual retained coordinate parameterizes the line bijectively. The other
two retained labels receive column-energy bounds, and the free label receives
the operator bound. The joint residual amplitude is restricted injectively;
its squared sum is bounded by the original energy. The intersection response
is retained and is not asserted to vanish.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and the fixed 10/14/16 target remain unchanged. No
physical cap or inventory is asserted.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ThreeActiveLineEnergy
open AESMixing
open AESConcrete.IndexedGraphEnergy

section Singleton
variable {I V : Type*}

/-- Values on the actual distinguished singleton label, without relabeling it. -/
def singletonTupleEquiv (s : I) : V ≃ (FreeCoordinates (fun i : I => i = s) → V) where
  toFun v := fun _ => v
  invFun x := x ⟨s, rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext i
    exact congrArg x (show (⟨s, rfl⟩ : FreeCoordinates (fun j : I => j = s)) = i from
      Subtype.ext i.property.symm)

end Singleton

section Curve
variable {I V C : Type*} [Fintype I] [DecidableEq I] [Fintype C] [Fintype V]

/-- One operator factor and two genuine column factors. The line amplitude
has arbitrary signs and includes its value at the zero source. -/
theorem line_energy_of_equiv (hI : Fintype.card I = 3) (s : I)
    (T : V → V → ℝ) (curve : C → I → V) (mu : C → ℝ)
    (e : C ≃ V) (he : ∀ c, e c = curve c s)
    (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action T g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, T y v ^ 2) ≤ kappa) :
    (∑ y : I → V, IndexedTripleEnergy.response T curve mu y ^ 2) ≤
      rho ^ 2 * kappa ^ 2 * ∑ c, mu c ^ 2 := by
  classical
  let ep := e.trans (singletonTupleEquiv (V := V) s)
  have hep : ∀ c (i : FreeCoordinates (fun j : I => j = s)), ep c i = curve c i.val := by
    intro c i
    change e c = curve c i.val
    rw [i.property]
    exact he c
  have hb := IndexedTripleEnergy.response_energy_of_equiv
    (fun i : I => i = s) T curve mu ep hep rho kappa hkappa hT hcolumn
  have hfree : Fintype.card (FreeCoordinates (fun i : I => i = s)) = 1 :=
    Fintype.card_subtype_eq s
  have hdep : Fintype.card (DependentCoordinates (fun i : I => i = s)) = 2 :=
    ThreeActivePlaneEnergy.otherCoordinates_card hI s
  -- Cardinalities are independent of the decidable-predicate instances chosen
  -- in the generic graph theorem and this singleton specialization.
  have hfree' : Nat.card (FreeCoordinates (fun i : I => i = s)) = 1 := by
    simpa only [Nat.card_eq_fintype_card] using hfree
  have hdep' : Nat.card (DependentCoordinates (fun i : I => i = s)) = 2 := by
    simpa only [Nat.card_eq_fintype_card] using hdep
  simpa only [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    hfree', hdep', pow_one] using hb

/-- A proved singleton output projection bijection supplies the line parameter. -/
theorem line_energy_of_bijective (hI : Fintype.card I = 3) (s : I)
    (T : V → V → ℝ) (curve : C → I → V) (mu : C → ℝ)
    (hprojection : Function.Bijective (fun c : C => curve c s))
    (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action T g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, T y v ^ 2) ≤ kappa) :
    (∑ y : I → V, IndexedTripleEnergy.response T curve mu y ^ 2) ≤
      rho ^ 2 * kappa ^ 2 * ∑ c, mu c ^ 2 :=
  line_energy_of_equiv hI s T curve mu
    (Equiv.ofBijective _ hprojection) (fun _ => rfl)
    rho kappa hkappa hT hcolumn

/-- The original joint residual energy dominates its injective restriction to
the intersection line. This is an inequality, rather than an energy identity. -/
theorem line_restriction_energy {U : Type*} [Fintype U]
    (hI : Fintype.card I = 3) (s : I)
    (T : V → V → ℝ) (curve : C → I → V)
    (r : C → U) (hr : Function.Injective r) (h : U → ℝ)
    (hprojection : Function.Bijective (fun c : C => curve c s))
    (rho kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hT : ∀ g : V → ℝ,
      (∑ y, action T g y ^ 2) ≤ rho ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ v : V, (∑ y, T y v ^ 2) ≤ kappa) :
    (∑ y : I → V, IndexedTripleEnergy.response T curve (fun c => h (r c)) y ^ 2) ≤
      rho ^ 2 * kappa ^ 2 * ∑ u, h u ^ 2 := by
  have hb := line_energy_of_bijective hI s T curve (fun c => h (r c))
    hprojection rho kappa hkappa hT hcolumn
  exact hb.trans (mul_le_mul_of_nonneg_left
    (IndexedTripleEnergy.restriction_energy_le r hr h)
    (mul_nonneg (sq_nonneg rho) (sq_nonneg kappa)))

end Curve

section ActualWord
variable {I C : Type*} [Fintype I] [DecidableEq I] [Fintype C]

/-- Actual ordinary AES word resources for the retained intersection line. -/
theorem word_line_energy_of_bijective
    (hI : Fintype.card I = 3) (s : I)
    (curve : C → I → AES.Word) (mu : C → ℝ)
    (hprojection : Function.Bijective (fun c : C => curve c s)) :
    (∑ y : I → AES.Word,
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0) curve mu y ^ 2) ≤
      UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2 * ∑ c, mu c ^ 2 := by
  apply line_energy_of_bijective hI s _ curve mu hprojection
    UniformGraphScalar.rho UniformGraphScalar.kappa UniformGraphScalar.kappa_nonneg
  · exact SharpDampedWordNorm.word_superbox_residual_energy
  · intro v
    exact (AllColumnBound.actual_word_residual_column_energy_lt v).le

/-- The actual-kernel restriction bound, charged against the same full signed
joint amplitude used by the two plane terms and the full-source term. -/
theorem word_line_restriction_energy {U : Type*} [Fintype U]
    (hI : Fintype.card I = 3) (s : I)
    (curve : C → I → AES.Word) (r : C → U) (hr : Function.Injective r) (h : U → ℝ)
    (hprojection : Function.Bijective (fun c : C => curve c s)) :
    (∑ y : I → AES.Word, IndexedTripleEnergy.response
      (residualMatrix AES.wordSuperboxKernel 0) curve (fun c => h (r c)) y ^ 2) ≤
      UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2 * ∑ u, h u ^ 2 := by
  apply line_restriction_energy hI s _ curve r hr h hprojection
    UniformGraphScalar.rho UniformGraphScalar.kappa UniformGraphScalar.kappa_nonneg
  · exact SharpDampedWordNorm.word_superbox_residual_energy
  · intro v
    exact (AllColumnBound.actual_word_residual_column_energy_lt v).le

end ActualWord

/-- The actual `v=z=0` intersection line. Its response is kept, including
zero, and its amplitude restriction is charged to the original residual pair. -/
theorem retained_intersectionLine_energy
    (pOut : ResidualIncidenceCoefficient.SelectedSupport 3 4)
    (pIn : ResidualIncidenceCoefficient.SelectedSupport 2 3)
    (h : (ThreeActiveSource.ResidualPositions pIn → AES.Word) → ℝ) :
    (∑ y : MaskCoordinates pOut.val.val.1 → AES.Word,
      IndexedTripleEnergy.response (residualMatrix AES.wordSuperboxKernel 0)
        (fun uv : ThreeActiveShortening.intersectionLine
          WordCrossZero.wordMixAddEquiv.toAddMonoidHom pIn (ThreeActiveGeometry.omittedLabel pOut) =>
          ThreeActiveGeometry.sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom
            pIn pOut.val.val.1 uv.val)
        (fun uv => h uv.val.1) y ^ 2) ≤
      UniformGraphScalar.rho ^ 2 * UniformGraphScalar.kappa ^ 2 * ∑ u, h u ^ 2 := by
  classical
  haveI : Nonempty (MaskCoordinates pOut.val.val.1) :=
    Fintype.card_pos_iff.mp (by rw [ThreeActiveGeometry.retainedCoordinates_card]; norm_num)
  let s : MaskCoordinates pOut.val.val.1 := Classical.choice inferInstance
  apply word_line_restriction_energy (ThreeActiveGeometry.retainedCoordinates_card pOut) s
    (fun uv : ThreeActiveShortening.intersectionLine
      WordCrossZero.wordMixAddEquiv.toAddMonoidHom pIn (ThreeActiveGeometry.omittedLabel pOut) =>
      ThreeActiveGeometry.sourceMap WordCrossZero.wordMixAddEquiv.toAddMonoidHom
        pIn pOut.val.val.1 uv.val)
    (fun uv => uv.val.1)
    (ThreeActiveShortening.intersectionLine_residual_injective
      WordCrossZero.wordMixAddEquiv.toAddMonoidHom pIn (ThreeActiveGeometry.omittedLabel pOut)) h
  exact ThreeActiveShortening.word_intersectionLine_output_bijective pIn
    (ThreeActiveGeometry.omittedLabel pOut) s.val (ThreeActiveGeometry.retained_ne_omitted pOut s)

end AESConcrete.ThreeActiveLineEnergy
