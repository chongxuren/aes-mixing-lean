import AESConcrete.TwoOmittedOneInputGeometry

/-!
# Genuine original input/output-zero domains for (10,12)

Event domains preserve physical states and original J,E; they do not choose a
new signed amplitude. Input-zero and each single-output-zero retained map have
q-point fibers. The double-output-zero retained pair is bijective and its J
projection is injective. These are actual MDS interfaces, not desired response
bounds. Constructive fixed AES10/14/16.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.TwoOmittedOneInputEvents
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoOmittedOneInputGeometry
open AESConcrete.ShortenedWeightedGeometry (ShortenedCode graphEquiv singletonTupleEquiv)
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)
open AESConcrete.WordCrossZero (wordMixAddEquiv wordMixAddEquiv_zeroMDS)

-- Keep executable finite-mask decision instances before the local classical one.
theorem complement_disjoint : ∀ E : Fin 16, MaskDisjoint (maskComplement E) E := by decide

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

abbrev InputZero (pIn : SelectedSupport 3 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom 0 (singletonMask (inputUniform pIn).val)

abbrev SingleZero (pOut : SelectedSupport 2 4) (a : Omitted pOut) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom (singletonMask a.val) 0

abbrev DoubleZero (pOut : SelectedSupport 2 4) :=
  ShortenedCode wordMixAddEquiv.toAddMonoidHom (maskComplement pOut.val.val.1) 0

def eventRetained (pOut : SelectedSupport 2 4) (r z : Fin 16) :
    ShortenedCode wordMixAddEquiv.toAddMonoidHom r z →+ (Retained pOut → AES.Word) :=
  ShortenedWeightedGeometry.retainedHom wordMixAddEquiv.toAddMonoidHom r z pOut.val.val.1

def inputRestrictionEquiv (pIn : SelectedSupport 3 4) :
    {x : AES.WordState // x (inputUniform pIn).val = 0} ≃ InputZero pIn where
  toFun x := ⟨x.val, by
    constructor
    · intro i hi; exact (empty_mask_coordinate ⟨i,hi⟩).elim
    · intro i hi; rw [(singletonMask_bit _ _).mp hi]; exact x.property⟩
  invFun x := ⟨x.val, x.property.2 _ ((singletonMask_bit _ _).mpr rfl)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def singleRestrictionEquiv (pOut : SelectedSupport 2 4) (a : Omitted pOut) :
    {x : AES.WordState // wordMixAddEquiv x a.val = 0} ≃ SingleZero pOut a where
  toFun x := ⟨x.val, by
    constructor
    · intro i hi; rw [(singletonMask_bit _ _).mp hi]; exact x.property
    · intro i hi; exact (empty_mask_coordinate ⟨i,hi⟩).elim⟩
  invFun x := ⟨x.val, x.property.1 _ ((singletonMask_bit _ _).mpr rfl)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def doubleRestrictionEquiv (pOut : SelectedSupport 2 4) :
    {x : AES.WordState // wordMixAddEquiv x (omittedFirst pOut).val = 0 ∧
      wordMixAddEquiv x (omittedSecond pOut).val = 0} ≃ DoubleZero pOut where
  toFun x := ⟨x.val, by
    constructor
    · intro i hi
      rcases (omitted_partition pOut i).mp hi with he | he
      · rw [he]; exact x.property.1
      · rw [he]; exact x.property.2
    · intro i hi; exact (empty_mask_coordinate ⟨i,hi⟩).elim⟩
  invFun x := ⟨x.val, x.property.1 _ ((omitted_partition pOut _).mpr (Or.inl rfl)),
    x.property.1 _ ((omitted_partition pOut _).mpr (Or.inr rfl))⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem inputUniform_ne_residual (pIn : SelectedSupport 3 4) (j : Residual pIn) :
    (inputUniform pIn).val ≠ j.val := by
  intro he
  apply (inputUniform pIn).property
  rw [he]
  exact j.property

/-- Input zero u leaves precisely the original complete residual tuple J. -/
def inputZeroResidualEquiv (pIn : SelectedSupport 3 4) :
    InputZero pIn ≃ (Residual pIn → AES.Word) := by
  have hz : MaskDisjoint (singletonMask (inputUniform pIn).val) pIn.val.val.1 := by
    intro i hi hJ
    have he := (singletonMask_bit _ _).mp hi
    subst i
    exact (inputUniform pIn).property hJ
  exact Equiv.ofBijective (fun c => residualTuple pIn c.val)
    ((RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS 0 (singletonMask (inputUniform pIn).val) pIn.val.val.1 hz
      (by simp only [show maskSize (0 : Fin 16) = 0 by decide,
        singletonMask_size, residualMask_size])).comp
          (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

/-- One original residual word and E give the exact q-point retained fibers. -/
def inputZeroFiberParam (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (j : Residual pIn) : InputZero pIn ≃ AES.Word × (Retained pOut → AES.Word) := by
  have hz : MaskDisjoint (singletonMask (inputUniform pIn).val) (singletonMask j.val) := by
    intro i hi hj
    exact inputUniform_ne_residual pIn j
      (((singletonMask_bit _ _).mp hi).symm.trans ((singletonMask_bit _ _).mp hj))
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS 0 (singletonMask (inputUniform pIn).val) pOut.val.val.1
      (singletonMask j.val) (empty_disjoint _) hz
      (by simp only [show maskSize (0 : Fin 16) = 0 by decide,
        singletonMask_size, retainedMask_size]))).trans
          (Equiv.prodCongr (singletonTupleEquiv j.val) (Equiv.refl _))

theorem inputZeroFiberParam_snd (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (j : Residual pIn) (c : InputZero pIn) :
    (inputZeroFiberParam pOut pIn j c).2 =
      eventRetained pOut 0 (singletonMask (inputUniform pIn).val) c := rfl

/-- A single genuine output zero leaves J as a joint bijective input tuple. -/
def singleZeroResidualEquiv (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (a : Omitted pOut) : SingleZero pOut a ≃ (Residual pIn → AES.Word) :=
  Equiv.ofBijective (fun c => residualTuple pIn c.val)
    ((RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS (singletonMask a.val) 0 pIn.val.val.1 (empty_disjoint _)
      (by simp only [singletonMask_size, show maskSize (0 : Fin 16) = 0 by decide,
        residualMask_size])).comp
          (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

def singleZeroFiberParam (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (a : Omitted pOut) (j : Residual pIn) :
    SingleZero pOut a ≃ AES.Word × (Retained pOut → AES.Word) := by
  have hr : MaskDisjoint (singletonMask a.val) pOut.val.val.1 := by
    intro i hi hE
    have he := (singletonMask_bit _ _).mp hi
    subst i
    exact a.property hE
  exact ((graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).trans
    (RestrictedMDSCoordinates.mixedSplitEquiv wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS (singletonMask a.val) 0 pOut.val.val.1 (singletonMask j.val)
      hr (empty_disjoint _)
      (by simp only [singletonMask_size, show maskSize (0 : Fin 16) = 0 by decide,
        retainedMask_size]))).trans
          (Equiv.prodCongr (singletonTupleEquiv j.val) (Equiv.refl _))

theorem singleZeroFiberParam_snd (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) (a : Omitted pOut) (j : Residual pIn)
    (c : SingleZero pOut a) :
    (singleZeroFiberParam pOut pIn a j c).2 =
      eventRetained pOut (singletonMask a.val) 0 c := rfl

theorem doubleZeroMask_size (pOut : SelectedSupport 2 4) :
    maskSize (maskComplement pOut.val.val.1) = 2 := by
  rw [maskComplement_size, retainedMask_size]

/-- No retained-fiber energy loss remains on the double-output-zero plane. -/
def doubleZeroRetainedEquiv (pOut : SelectedSupport 2 4) :
    DoubleZero pOut ≃ (Retained pOut → AES.Word) :=
  Equiv.ofBijective (eventRetained pOut (maskComplement pOut.val.val.1) 0)
    ((RestrictedMDSCoordinates.output_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS (maskComplement pOut.val.val.1) 0 pOut.val.val.1
      (complement_disjoint _)
      (by simp only [doubleZeroMask_size, show maskSize (0 : Fin 16) = 0 by decide,
        retainedMask_size])).comp
          (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective)

/-- Two J labels are already an information set; hence the complete J map injects. -/
theorem doubleZeroResidual_injective (pOut : SelectedSupport 2 4)
    (pIn : SelectedSupport 3 4) :
    Function.Injective (fun c : DoubleZero pOut => residualTuple pIn c.val) := by
  have hp : Function.Injective (fun c : DoubleZero pOut =>
      fun i : MaskCoordinates (residualPairMask pIn) => c.val i.val) :=
    ((RestrictedMDSCoordinates.input_projection_bijective wordMixAddEquiv.toAddMonoidHom
      wordMixAddEquiv_zeroMDS (maskComplement pOut.val.val.1) 0 (residualPairMask pIn)
      (empty_disjoint _)
      (by simp only [doubleZeroMask_size, show maskSize (0 : Fin 16) = 0 by decide,
        residualPairMask_size])).comp
          (graphEquiv wordMixAddEquiv.toAddMonoidHom _ _).bijective).injective
  intro c d he
  apply hp
  funext i
  exact congrFun he ⟨i.val, residualPairMask_subset pIn i.val i.property⟩

/-- Each input-zero retained fiber has exactly one free original input word. -/
theorem inputZero_fiber_card (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (j : Residual pIn) (z : Retained pOut → AES.Word) :
    Fintype.card {c : InputZero pIn //
      eventRetained pOut 0 (singletonMask (inputUniform pIn).val) c = z} = Fintype.card AES.Word := by
  -- Nat.card removes the irrelevant choice of fiber DecidablePred/Fintype.
  simpa only [← Nat.card_eq_fintype_card] using
    OmittedUniformTwoInputPushforward.fiber_card _ (inputZeroFiberParam pOut pIn j)
      (inputZeroFiberParam_snd pOut pIn j) z

/-- Each single-output-zero retained fiber has exactly one free original input word. -/
theorem singleZero_fiber_card (pOut : SelectedSupport 2 4) (pIn : SelectedSupport 3 4)
    (a : Omitted pOut) (j : Residual pIn) (z : Retained pOut → AES.Word) :
    Fintype.card {c : SingleZero pOut a //
      eventRetained pOut (singletonMask a.val) 0 c = z} = Fintype.card AES.Word := by
  simpa only [← Nat.card_eq_fintype_card] using
    OmittedUniformTwoInputPushforward.fiber_card _ (singleZeroFiberParam pOut pIn a j)
      (singleZeroFiberParam_snd pOut pIn a j) z

end AESConcrete.TwoOmittedOneInputEvents
