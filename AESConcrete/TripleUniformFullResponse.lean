import AESConcrete.TripleUniformSource
import AESConcrete.ThreeActiveGeometry
import AESConcrete.WordMixedCentering
import AESMixing.MDSInverse

/-!
# actual full-source fibers for one residual and three uniform inputs

Three retained output words and the omitted physical output word parameterize
the full four-word source. At fixed retained values, inverse singleton MDS and
an additive translation identify the omitted word with the original residual
input word. Exact fiber sums precede two distinct cancellations: zero-sum
actual amplitudes cancel before the kernel, while arbitrary signed amplitudes
cancel after the actual residual row sums. Singleton MDS also proves the
quadruple-zero kernel endpoint without an h(0) premise.

No selected-minor identity, event-family bound, physical (12,7) cap or
inventory is asserted. Independent retained keys, whitening, omitted final
MixColumns, ordered-distinct reference pairs and fixed AES 10/14/16 remain
unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.TripleUniformFullResponse
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TripleUniformSource
open AESConcrete.ThreeActiveGeometry
  (omittedLabel omittedLabel_not_retained retained_ne_omitted retainedCoordinates_card)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

attribute [local instance] Classical.propDecidable

abbrev SourceWord (pIn : SelectedSupport 1 4) :=
  AES.Word × (SourceUniformPositions pIn → AES.Word)

abbrev Retained (pOut : SelectedSupport 3 4) := MaskCoordinates pOut.val.val.1

/-- All four original input labels, with their actual source equivalence. -/
def sourceWordEquiv (pIn : SelectedSupport 1 4) : SourceWord pIn ≃ AES.WordState :=
  sourceEquiv pIn

theorem sourceWord_card (pIn : SelectedSupport 1 4) :
    Fintype.card (SourceWord pIn) = Fintype.card AES.Word ^ 4 := by
  rw [Fintype.card_congr (sourceWordEquiv pIn), Fintype.card_fun, Fintype.card_fin]

/-- Before any retained fiber sum, every residual value has exactly three
unrestricted original uniform words in the full counting energy. -/
theorem fullSource_amplitude_energy (pIn : SelectedSupport 1 4) (h : AES.Word → ℝ) :
    (∑ uv : SourceWord pIn, h uv.1 ^ 2) =
      (Fintype.card AES.Word : ℝ) ^ 3 * ∑ u, h u ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    uniformTuple_card, Nat.cast_pow]
  exact (Finset.mul_sum _ _ _).symm

def retainedMap (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (uv : SourceWord pIn) : Retained pOut → AES.Word :=
  restrictCoordinates pOut.val.val.1 (wordMixAddEquiv (source pIn uv.1 uv.2))

def omittedValue (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (uv : SourceWord pIn) : AES.Word :=
  wordMixAddEquiv (source pIn uv.1 uv.2) (omittedLabel pOut)

theorem omittedLabel_eq_of_not_retained (pOut : SelectedSupport 3 4)
    (i : Fin 4) (hi : maskBit pOut.val.val.1 i ≠ true) : i = omittedLabel pOut := by
  have hc : maskBit (maskComplement pOut.val.val.1) i = true := by
    rw [maskComplement_bit]
    cases hb : maskBit pOut.val.val.1 i <;> simp_all
  exact congrArg Subtype.val
    (ThreeActiveGeometry.omittedPosition_unique pOut ⟨i, hc⟩)

/-- The retained extension and omitted singleton axis have disjoint supports. -/
def completeOutput (pOut : SelectedSupport 3 4)
    (x : Retained pOut → AES.Word) (z : AES.Word) : AES.WordState :=
  extendCoordinates pOut.val.val.1 x + Pi.single (omittedLabel pOut) z

theorem completeOutput_retained (pOut : SelectedSupport 3 4)
    (x : Retained pOut → AES.Word) (z : AES.Word) :
    restrictCoordinates pOut.val.val.1 (completeOutput pOut x z) = x := by
  funext i
  change extendCoordinates pOut.val.val.1 x i.val +
    (Pi.single (omittedLabel pOut) z : AES.WordState) i.val = x i
  simp only [extendCoordinates, dif_pos i.property,
    Pi.single_eq_of_ne (retained_ne_omitted pOut i), add_zero]

theorem completeOutput_omitted (pOut : SelectedSupport 3 4)
    (x : Retained pOut → AES.Word) (z : AES.Word) :
    completeOutput pOut x z (omittedLabel pOut) = z := by
  simp [completeOutput, extendCoordinates, omittedLabel_not_retained pOut]

theorem completeOutput_reconstruct (pOut : SelectedSupport 3 4) (w : AES.WordState) :
    completeOutput pOut (restrictCoordinates pOut.val.val.1 w)
      (w (omittedLabel pOut)) = w := by
  funext i
  by_cases hi : maskBit pOut.val.val.1 i = true
  · have hne : i ≠ omittedLabel pOut := retained_ne_omitted pOut ⟨i, hi⟩
    simp only [completeOutput, Pi.add_apply, extendCoordinates, dif_pos hi,
      restrictCoordinates, Pi.single_eq_of_ne hne, add_zero]
  · have he := omittedLabel_eq_of_not_retained pOut i hi
    subst i
    exact completeOutput_omitted pOut _ _

/-- The output split keeps all physical labels and the missing word. -/
def completeOutputEquiv (pOut : SelectedSupport 3 4) :
    ((Retained pOut → AES.Word) × AES.Word) ≃ AES.WordState where
  toFun xz := completeOutput pOut xz.1 xz.2
  invFun w := (restrictCoordinates pOut.val.val.1 w, w (omittedLabel pOut))
  left_inv xz := Prod.ext (completeOutput_retained pOut xz.1 xz.2)
    (completeOutput_omitted pOut xz.1 xz.2)
  right_inv w := completeOutput_reconstruct pOut w

/-- Full-source equivalence to a retained triple together with its omitted word. -/
def sourceOutputEquiv (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4) :
    SourceWord pIn ≃ (Retained pOut → AES.Word) × AES.Word :=
  ((sourceWordEquiv pIn).trans wordMixAddEquiv.toEquiv).trans
    (completeOutputEquiv pOut).symm

@[simp]
theorem sourceOutputEquiv_apply (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (uv : SourceWord pIn) :
    sourceOutputEquiv pOut pIn uv = (retainedMap pOut pIn uv, omittedValue pOut pIn uv) := rfl

theorem sourceOutputEquiv_symm_retained
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) (z : AES.Word) :
    retainedMap pOut pIn ((sourceOutputEquiv pOut pIn).symm (x, z)) = x :=
  congrArg Prod.fst ((sourceOutputEquiv pOut pIn).apply_symm_apply (x, z))

theorem sourceOutputEquiv_symm_residual
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) (z : AES.Word) :
    ((sourceOutputEquiv pOut pIn).symm (x, z)).1 =
      wordMixAddEquiv.symm (completeOutput pOut x z) (residualLabel pIn) := rfl

private theorem wordMixHom_apply (x : AES.WordState) :
    wordMixAddEquiv.toAddMonoidHom x = wordMixAddEquiv x := rfl

private theorem wordMixSymmHom_apply (x : AES.WordState) :
    wordMixAddEquiv.symm.toAddMonoidHom x = wordMixAddEquiv.symm x := rfl

/-- Variable part: actual inverse singleton MDS. Fixed part: the retained
output extension followed by inverse diffusion and residual evaluation. -/
def omittedResidualAffineEquiv (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) : AES.Word ≃ AES.Word :=
  (TwoActiveGeometry.singletonCoordinateEquiv wordMixAddEquiv.symm.toAddMonoidHom
    (zeroMDS_inverse wordMixAddEquiv wordMixAddEquiv_zeroMDS)
    (omittedLabel pOut) (residualLabel pIn)).trans
      (Equiv.addLeft
        (wordMixAddEquiv.symm (extendCoordinates pOut.val.val.1 x) (residualLabel pIn)))

@[simp]
theorem omittedResidualAffineEquiv_apply
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) (z : AES.Word) :
    omittedResidualAffineEquiv pOut pIn x z =
      wordMixAddEquiv.symm (completeOutput pOut x z) (residualLabel pIn) := by
  change wordMixAddEquiv.symm (extendCoordinates pOut.val.val.1 x) (residualLabel pIn) +
    TwoActiveGeometry.singletonCoordinateEquiv wordMixAddEquiv.symm.toAddMonoidHom
      (zeroMDS_inverse wordMixAddEquiv wordMixAddEquiv_zeroMDS)
      (omittedLabel pOut) (residualLabel pIn) z = _
  rw [TwoActiveGeometry.singletonCoordinateEquiv_apply, wordMixSymmHom_apply]
  exact (congrFun (wordMixAddEquiv.symm.map_add
    (extendCoordinates pOut.val.val.1 x) (Pi.single (omittedLabel pOut) z))
      (residualLabel pIn)).symm

/-- Explicit actual affine bijection at every fixed retained triple. -/
theorem omitted_residual_bijective
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) :
    Function.Bijective (fun z : AES.Word =>
      wordMixAddEquiv.symm (completeOutput pOut x z) (residualLabel pIn)) := by
  have he : (omittedResidualAffineEquiv pOut pIn x : AES.Word → AES.Word) =
      (fun z => wordMixAddEquiv.symm (completeOutput pOut x z) (residualLabel pIn)) :=
    funext (omittedResidualAffineEquiv_apply pOut pIn x)
  rw [← he]
  exact (omittedResidualAffineEquiv pOut pIn x).bijective

theorem omitted_residual_sum
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) (h : AES.Word → ℝ) :
    (∑ z : AES.Word,
      h (wordMixAddEquiv.symm (completeOutput pOut x z) (residualLabel pIn))) = ∑ u, h u := by
  have hs := Equiv.sum_comp (omittedResidualAffineEquiv pOut pIn x) h
  simpa only [omittedResidualAffineEquiv_apply] using hs

/-- Each actual retained fiber has exactly one omitted-word parameter. -/
def retainedFiberEquiv (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) :
    {uv : SourceWord pIn // retainedMap pOut pIn uv = x} ≃ AES.Word where
  toFun uv := omittedValue pOut pIn uv.val
  invFun z := ⟨(sourceOutputEquiv pOut pIn).symm (x, z),
    sourceOutputEquiv_symm_retained pOut pIn x z⟩
  left_inv uv := by
    apply Subtype.ext
    apply (sourceOutputEquiv pOut pIn).injective
    rw [Equiv.apply_symm_apply, sourceOutputEquiv_apply]
    exact Prod.ext uv.property.symm rfl
  right_inv z :=
    congrArg Prod.snd ((sourceOutputEquiv pOut pIn).apply_symm_apply (x, z))

theorem retainedFiber_card (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) :
    Fintype.card {uv : SourceWord pIn // retainedMap pOut pIn uv = x} =
      Fintype.card AES.Word := Fintype.card_congr (retainedFiberEquiv pOut pIn x)

theorem retainedFiberEquiv_symm_residual
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) (z : AES.Word) :
    ((retainedFiberEquiv pOut pIn x).symm z).val.1 =
      wordMixAddEquiv.symm (completeOutput pOut x z) (residualLabel pIn) := rfl

/-- Exact counting fiber sum, with no zero-sum premise or multiplicity loss. -/
theorem retainedFiber_sum (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) (h : AES.Word → ℝ) :
    (∑ uv : {uv : SourceWord pIn // retainedMap pOut pIn uv = x}, h uv.val.1) =
      ∑ u, h u := by
  calc
    _ = ∑ z : AES.Word, h (((retainedFiberEquiv pOut pIn x).symm z).val.1) :=
      (Equiv.sum_comp (retainedFiberEquiv pOut pIn x).symm (fun uv => h uv.val.1)).symm
    _ = _ := by
      simp_rw [retainedFiberEquiv_symm_residual]
      exact omitted_residual_sum pOut pIn x h

/-- Pre-kernel cancellation requires the amplitude's zero sum. -/
theorem retainedFiber_sum_zero (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (x : Retained pOut → AES.Word) (h : AES.Word → ℝ) (hsum : (∑ u, h u) = 0) :
    (∑ uv : {uv : SourceWord pIn // retainedMap pOut pIn uv = x}, h uv.val.1) = 0 :=
  (retainedFiber_sum pOut pIn x h).trans hsum

/-- The extracted actual component supplies the zero sum needed above.
Its source representation and original counting energy remain attached. -/
theorem actual_source_fibers_zero (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (f : AES.WordState → ℝ) :
    ∃ h : AES.Word → ℝ,
      h 0 = 0 ∧ (∑ u, h u) = 0 ∧
      (∀ u v, supportIndexComponent (0 : AES.Word) pIn.val f (source pIn u v) =
        h u * ∏ i : SourceUniformPositions pIn, NonzeroUniformGraphCap.nonzeroUniform (v i)) ∧
      ((∑ w, supportIndexComponent (0 : AES.Word) pIn.val f w ^ 2) = ∑ u, h u ^ 2) ∧
      (∀ x : Retained pOut → AES.Word,
        (∑ uv : {uv : SourceWord pIn // retainedMap pOut pIn uv = x}, h uv.val.1) = 0) := by
  obtain ⟨h, hzero, hsum, hsource, henergy⟩ := word_source_representation pIn f
  exact ⟨h, hzero, hsum, hsource, henergy,
    fun x => retainedFiber_sum_zero pOut pIn x h hsum⟩

def residualKernel (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (y : Retained pOut → AES.Word) (uv : SourceWord pIn) : ℝ :=
  ∏ i : Retained pOut,
    residualMatrix AES.wordSuperboxKernel 0 (y i) (retainedMap pOut pIn uv i)

def rawFullResponse (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (y : Retained pOut → AES.Word) : ℝ :=
  ∑ uv : SourceWord pIn, h uv.1 * residualKernel pOut pIn y uv

/-- Exact full-source factorization before applying residual row sums. -/
theorem rawFullResponse_factorization
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (y : Retained pOut → AES.Word) :
    rawFullResponse pOut pIn h y = (∑ u, h u) *
      ∑ x : Retained pOut → AES.Word, ∏ i : Retained pOut,
        residualMatrix AES.wordSuperboxKernel 0 (y i) (x i) := by
  unfold rawFullResponse residualKernel
  rw [← Equiv.sum_comp (sourceOutputEquiv pOut pIn).symm
    (fun uv : SourceWord pIn => h uv.1 * ∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (retainedMap pOut pIn uv i))]
  rw [Fintype.sum_prod_type]
  simp_rw [sourceOutputEquiv_symm_retained, sourceOutputEquiv_symm_residual]
  calc
    _ = ∑ x : Retained pOut → AES.Word, (∑ u, h u) *
        ∏ i : Retained pOut, residualMatrix AES.wordSuperboxKernel 0 (y i) (x i) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_mul, omitted_residual_sum pOut pIn x h]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem retainedResidual_sum_zero (pOut : SelectedSupport 3 4)
    (y : Retained pOut → AES.Word) :
    (∑ x : Retained pOut → AES.Word, ∏ i : Retained pOut,
      residualMatrix AES.wordSuperboxKernel 0 (y i) (x i)) = 0 := by
  rw [← Fintype.prod_sum
    (fun i : Retained pOut => fun v : AES.Word => residualMatrix AES.wordSuperboxKernel 0 (y i) v)]
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let i : Retained pOut := Classical.choice inferInstance
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact WordMixedCentering.residual_row_sum AES.wordSuperboxKernel
    AES.word_superbox_pointed (y i)

/-- Post-kernel cancellation is valid for arbitrary signed h, including h(0).
The actual residual row sums, rather than an amplitude premise, kill it. -/
theorem rawFullResponse_zero (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (y : Retained pOut → AES.Word) : rawFullResponse pOut pIn h y = 0 := by
  rw [rawFullResponse_factorization, retainedResidual_sum_zero, mul_zero]

theorem residualKernel_zero_source
    (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (y : Retained pOut → AES.Word) : residualKernel pOut pIn y (0, 0) = 0 := by
  haveI : Nonempty (Retained pOut) :=
    Fintype.card_pos_iff.mp (by rw [retainedCoordinates_card]; norm_num)
  let i : Retained pOut := Classical.choice inferInstance
  unfold residualKernel
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  change residualMatrix AES.wordSuperboxKernel 0 (y i)
    (wordMixAddEquiv (source pIn 0 0) i.val) = 0
  rw [source_zero, map_zero, Pi.zero_apply, AES.word_residual_zero_column]

/-- Three original uniform-input zeros and the omitted-output zero force
the source to zero by actual forward singleton MDS. -/
theorem quadruple_zero_source (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (uv : SourceWord pIn)
    (huniform : ∀ i : SourceUniformPositions pIn, uv.2 i = 0)
    (homitted : omittedValue pOut pIn uv = 0) : uv = (0, 0) := by
  have hv : uv.2 = 0 := funext huniform
  have hz : wordMixAddEquiv (Pi.single (residualLabel pIn) uv.1) (omittedLabel pOut) = 0 := by
    simpa only [omittedValue, hv, source_residual_axis] using homitted
  have hu : uv.1 = 0 := by
    apply (TwoActiveGeometry.singletonCoordinateEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS (residualLabel pIn) (omittedLabel pOut)).injective
    rw [TwoActiveGeometry.singletonCoordinateEquiv_zero]
    simpa only [TwoActiveGeometry.singletonCoordinateEquiv_apply, wordMixHom_apply] using hz
  exact Prod.ext hu hv

/-- The endpoint kernel vanishes independently of any amplitude constraint. -/
theorem quadruple_zero_kernel (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (y : Retained pOut → AES.Word) (uv : SourceWord pIn)
    (huniform : ∀ i : SourceUniformPositions pIn, uv.2 i = 0)
    (homitted : omittedValue pOut pIn uv = 0) : residualKernel pOut pIn y uv = 0 := by
  rw [quadruple_zero_source pOut pIn uv huniform homitted]
  exact residualKernel_zero_source pOut pIn y

theorem quadruple_zero_summand (pOut : SelectedSupport 3 4) (pIn : SelectedSupport 1 4)
    (h : AES.Word → ℝ) (y : Retained pOut → AES.Word) (uv : SourceWord pIn)
    (huniform : ∀ i : SourceUniformPositions pIn, uv.2 i = 0)
    (homitted : omittedValue pOut pIn uv = 0) : h uv.1 * residualKernel pOut pIn y uv = 0 := by
  rw [quadruple_zero_kernel pOut pIn y uv huniform homitted, mul_zero]

end AESConcrete.TripleUniformFullResponse
