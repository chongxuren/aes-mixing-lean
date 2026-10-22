import AESConcrete.DoubleUniformGeometry
import AESConcrete.RestrictedMDSCoordinates

/-!
# Physical planes and lines for one residual and two uniform inputs

The omitted-output-zero plane retains the original three input labels. Its
residual value together with either original uniform value is an information
set. The residual-zero subgroup inside this plane is an actual shortened
line, and every nonzero-constrained output is a bijective line parameter.
All source values, including zero, are kept. This file supplies geometry and
counting identities; no operator bound or accepted inventory entry is added.

Candidate only. Constructive mathematics only; no attacks. Independent uniform
retained keys, whitening, omitted final MixColumns, ordered-distinct reference
pairs and the fixed 10/14/16 target remain unchanged.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.DoubleUniformShortening
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.DoubleUniformSource
open AESConcrete.DoubleUniformGeometry
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)

def singletonTupleEquiv {V : Type*} (i : Fin 4) :
    (MaskCoordinates (singletonMask i) → V) ≃ V where
  toFun x := x ⟨i, (singletonMask_bit i i).mpr rfl⟩
  invFun v := fun _ => v
  left_inv x := by
    funext j
    have hj : j.val = i := (singletonMask_bit i j.val).mp j.property
    exact congrArg x (Subtype.ext hj).symm
  right_inv _ := rfl

section Additive
variable {V : Type*} [AddCommGroup V]

/-- The actual omitted coordinate, as a homomorphism on the physical source. -/
def omittedHom (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) :
    (V × (SourceUniformPositions p → V)) →+ V where
  toFun uv := L (source p uv.1 uv.2) z
  map_zero' := by
    change L (source p (0 : V) 0) z = 0
    simp only [source_zero, map_zero, Pi.zero_apply]
  map_add' uv uv' := by
    rw [source_pair_add, map_add]
    rfl

/-- One physical output zero, with only the original inactive input fixed. -/
def zeroPlaneSubgroup (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) :
    AddSubgroup (V × (SourceUniformPositions p → V)) := (omittedHom L p z).ker

abbrev zeroPlane (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) := ↥(zeroPlaneSubgroup L p z)

@[simp]
theorem zeroPlane_condition (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (uv : zeroPlane L p z) :
    L (source p uv.val.1 uv.val.2) z = 0 := uv.property

def planeResidualHom (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) : zeroPlane L p z →+ V where
  toFun uv := uv.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The uniform translation line within the omitted-output-zero plane. -/
def uniformLineSubgroup (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) : AddSubgroup (zeroPlane L p z) :=
  (planeResidualHom L p z).ker

abbrev uniformLine (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) := ↥(uniformLineSubgroup L p z)

@[simp]
theorem uniformLine_residual_zero (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (c : uniformLine L p z) :
    c.val.val.1 = 0 := c.property

/-- Inclusion is the actual plane translation; its residual value is zero. -/
def uniformLineTranslation (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) : uniformLine L p z →+ zeroPlane L p z :=
  (uniformLineSubgroup L p z).subtype

theorem plane_residual_translation (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (uv : zeroPlane L p z)
    (c : uniformLine L p z) :
    (uv + uniformLineTranslation L p z c).val.1 = uv.val.1 := by
  change uv.val.1 + c.val.val.1 = uv.val.1
  rw [uniformLine_residual_zero, add_zero]

/-- The graph equivalence keeps the imposed output and input zero masks separate. -/
def zeroPlaneEquiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) :
    zeroPlane L p z ≃ ShortenedGraph L (singletonMask z) p.val.val.2 where
  toFun uv := ⟨source p uv.val.1 uv.val.2, by
    constructor
    · intro j hj
      have he : j = z := (singletonMask_bit z j).mp hj
      simpa only [he] using zeroPlane_condition L p z uv
    · exact source_onSource p uv.val.1 uv.val.2⟩
  invFun x := ⟨(x.val (residualLabel p), fun i => x.val i.val.val), by
    change L (source p (x.val (residualLabel p)) (fun i => x.val i.val.val)) z = 0
    rw [source_reconstruct p x.val x.property.2]
    exact x.property.1 z ((singletonMask_bit z z).mpr rfl)⟩
  left_inv uv := by
    apply Subtype.ext
    apply Prod.ext
    · exact source_residual p uv.val.1 uv.val.2
    · funext i
      exact source_uniform p uv.val.1 uv.val.2 i
  right_inv x := by
    apply Subtype.ext
    exact source_reconstruct p x.val x.property.2

theorem zeroPlane_shortening (p : SelectedSupport 1 3) (z : Fin 4) :
    maskSize (singletonMask z) + maskSize p.val.val.2 = 2 := by
  rw [singletonMask_size]
  have hp := p.property
  omega

def uniformLineInputMask (p : SelectedSupport 1 3) : Fin 16 :=
  maskUnion p.val.val.2 p.val.val.1

theorem uniformLineInputMask_size (p : SelectedSupport 1 3) :
    maskSize (uniformLineInputMask p) = 2 := by
  rw [uniformLineInputMask, maskUnion_size _ _ p.val.property.1]
  have hp := p.property
  have hd := p.val.property.2
  omega

/-- One output zero and the original inactive and residual input zeros. -/
def uniformLineEquiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) :
    uniformLine L p z ≃ ShortenedGraph L (singletonMask z) (uniformLineInputMask p) where
  toFun c := ⟨source p c.val.val.1 c.val.val.2, by
    constructor
    · intro j hj
      have he : j = z := (singletonMask_bit z j).mp hj
      simpa only [he] using zeroPlane_condition L p z c.val
    · intro j hj
      rw [uniformLineInputMask, maskUnion_bit, Bool.or_eq_true] at hj
      rcases hj with hj | hj
      · exact source_inactive p _ _ j hj
      · rw [residualLabel_eq_of_mem p j hj, source_residual, uniformLine_residual_zero]⟩
  invFun x := by
    have hinactive : OnSource p x.val := by
      intro j hj
      apply x.property.2 j
      rw [uniformLineInputMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inl hj
    refine ⟨⟨(x.val (residualLabel p), fun i => x.val i.val.val), ?_⟩, ?_⟩
    · change L (source p (x.val (residualLabel p)) (fun i => x.val i.val.val)) z = 0
      rw [source_reconstruct p x.val hinactive]
      exact x.property.1 z ((singletonMask_bit z z).mpr rfl)
    · change x.val (residualLabel p) = 0
      apply x.property.2 (residualLabel p)
      rw [uniformLineInputMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inr (residualLabel_mem p)
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact source_residual p _ _
    · funext i
      exact source_uniform p _ _ i
  right_inv x := by
    apply Subtype.ext
    apply source_reconstruct
    intro j hj
    apply x.property.2 j
    rw [uniformLineInputMask, maskUnion_bit, Bool.or_eq_true]
    exact Or.inl hj

theorem uniformLine_shortening (p : SelectedSupport 1 3) (z : Fin 4) :
    maskSize (singletonMask z) + maskSize (uniformLineInputMask p) = 3 := by
  rw [singletonMask_size, uniformLineInputMask_size]

end Additive

section FiniteMDS
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

-- Use explicit finite instances for the subgroup types in counting sums.
instance zeroPlaneFintype (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) : Fintype (zeroPlane L p z) := by
  classical
  exact inferInstance

instance uniformLineFintype (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) : Fintype (uniformLine L p z) := by
  classical
  exact inferInstance

/-- Two named free input values are an information set for any shortened plane. -/
theorem shortened_input_pair_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (hshort : maskSize r + maskSize z = 2)
    (a b : Fin 4) (hab : a ≠ b)
    (ha : maskBit z a ≠ true) (hb : maskBit z b ≠ true) :
    Function.Bijective (fun c : ShortenedGraph L r z => (c.val a, c.val b)) := by
  have hdisj : MaskDisjoint (singletonMask a) (singletonMask b) := by
    intro i hi hj
    exact hab (((singletonMask_bit a i).mp hi).symm.trans
      ((singletonMask_bit b i).mp hj))
  have hz : MaskDisjoint z (maskUnion (singletonMask a) (singletonMask b)) := by
    intro i hi hj
    rw [maskUnion_bit, Bool.or_eq_true] at hj
    rcases hj with hj | hj
    · exact ha (((singletonMask_bit a i).mp hj) ▸ hi)
    · exact hb (((singletonMask_bit b i).mp hj) ▸ hi)
  have hsize : maskSize r + maskSize z + maskSize (singletonMask a) +
      maskSize (singletonMask b) = 4 := by
    rw [singletonMask_size, singletonMask_size, hshort]
  exact ((RestrictedMDSCoordinates.inputSplitEquiv L hL r z
    (singletonMask a) (singletonMask b) hdisj hz hsize).trans
      (Equiv.prodCongr (singletonTupleEquiv a) (singletonTupleEquiv b))).bijective

/-- Each fixed residual value has precisely one free original uniform word. -/
theorem zeroPlane_parameter_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p) :
    Function.Bijective (fun uv : zeroPlane L p z => (uv.val.1, uv.val.2 j)) := by
  have hne : residualLabel p ≠ j.val.val := by
    intro he
    exact j.val.property (he ▸ residualLabel_mem p)
  have hh := (shortened_input_pair_bijective L hL (singletonMask z) p.val.val.2
    (zeroPlane_shortening p z) (residualLabel p) j.val.val hne
    (residualLabel_not_inactive p) j.property).comp (zeroPlaneEquiv L p z).bijective
  change Function.Bijective (fun uv : zeroPlane L p z =>
    (source p uv.val.1 uv.val.2 (residualLabel p), source p uv.val.1 uv.val.2 j.val.val)) at hh
  simpa only [source_residual, source_uniform] using hh

def zeroPlaneParameterEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p) :
    zeroPlane L p z ≃ V × V :=
  Equiv.ofBijective (fun uv => (uv.val.1, uv.val.2 j))
    (zeroPlane_parameter_bijective L hL p z j)

/-- Any two physical outputs outside the zero parameterize the plane. -/
theorem zeroPlane_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z : Fin 4) (out : Fin 16)
    (hout : maskSize out = 2) (hzout : maskBit out z ≠ true) :
    Function.Bijective (fun uv : zeroPlane L p z =>
      fun i : MaskCoordinates out => L (source p uv.val.1 uv.val.2) i.val) := by
  have hr : MaskDisjoint (singletonMask z) out := by
    intro i hi
    have hiz : i = z := (singletonMask_bit z i).mp hi
    simpa only [hiz] using hzout
  have hsize : maskSize (singletonMask z) + maskSize p.val.val.2 + maskSize out = 4 := by
    rw [zeroPlane_shortening, hout]
  exact (RestrictedMDSCoordinates.output_projection_bijective L hL
    (singletonMask z) p.val.val.2 out hr hsize).comp (zeroPlaneEquiv L p z).bijective

/-- Every retained singleton is an information set on the uniform translation line. -/
theorem uniformLine_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z k : Fin 4) (hk : k ≠ z) :
    Function.Bijective (fun c : uniformLine L p z =>
      L (source p c.val.val.1 c.val.val.2) k) := by
  have hkbit : maskBit (singletonMask z) k ≠ true := by
    intro hkbit
    exact hk ((singletonMask_bit z k).mp hkbit)
  exact (ShortenedLineResponse.output_coordinate_bijective L hL
    (singletonMask z) (uniformLineInputMask p) (uniformLine_shortening p z)
    k hkbit).comp (uniformLineEquiv L p z).bijective

/-- Counting measure gives exactly q copies of the same residual energy. -/
theorem zeroPlane_residual_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p) (h : V → ℝ) :
    (∑ uv : zeroPlane L p z, h uv.val.1 ^ 2) =
      (Fintype.card V : ℝ) * ∑ u : V, h u ^ 2 := by
  have hs := (zeroPlaneParameterEquiv L hL p z j).sum_comp
    (fun a : V × V => h a.1 ^ 2)
  change (∑ uv : zeroPlane L p z, h uv.val.1 ^ 2) =
    ∑ a : V × V, h a.1 ^ 2 at hs
  rw [hs, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

end FiniteMDS

section SourceZeros
variable {V : Type*} [AddCommGroup V]

theorem uniform_physical_label_injective (p : SelectedSupport 1 3) :
    Function.Injective (fun j : SourceUniformPositions p => j.val.val) := by
  intro j k h
  exact Subtype.ext (Subtype.ext h)

def sourceZeroInputMask (p : SelectedSupport 1 3) (j : SourceUniformPositions p) : Fin 16 :=
  maskUnion p.val.val.2 (singletonMask j.val.val)

theorem sourceZeroInputMask_size (p : SelectedSupport 1 3) (j : SourceUniformPositions p) :
    maskSize (sourceZeroInputMask p j) = 2 := by
  have hd : MaskDisjoint p.val.val.2 (singletonMask j.val.val) := by
    intro i hi hj
    exact j.property (((singletonMask_bit j.val.val i).mp hj) ▸ hi)
  rw [sourceZeroInputMask, maskUnion_size _ _ hd, singletonMask_size]
  have hp := p.property
  omega

theorem sourceZeroInputMask_not_residual (p : SelectedSupport 1 3)
    (j : SourceUniformPositions p) :
    maskBit (sourceZeroInputMask p j) (residualLabel p) ≠ true := by
  intro he
  rw [sourceZeroInputMask, maskUnion_bit, Bool.or_eq_true] at he
  rcases he with he | he
  · exact residualLabel_not_inactive p he
  · have hh := (singletonMask_bit j.val.val (residualLabel p)).mp he
    exact j.val.property (hh ▸ residualLabel_mem p)

theorem sourceZeroInputMask_not_other (p : SelectedSupport 1 3)
    (j k : SourceUniformPositions p) (hkj : k ≠ j) :
    maskBit (sourceZeroInputMask p j) k.val.val ≠ true := by
  intro he
  rw [sourceZeroInputMask, maskUnion_bit, Bool.or_eq_true] at he
  rcases he with he | he
  · exact k.property he
  · exact hkj (uniform_physical_label_injective p
      ((singletonMask_bit j.val.val k.val.val).mp he))

def uniformValueHom (p : SelectedSupport 1 3) (j : SourceUniformPositions p) :
    (V × (SourceUniformPositions p → V)) →+ V where
  toFun uv := uv.2 j
  map_zero' := rfl
  map_add' _ _ := rfl

def sourceZeroPlaneSubgroup (p : SelectedSupport 1 3) (j : SourceUniformPositions p) :
    AddSubgroup (V × (SourceUniformPositions p → V)) := (uniformValueHom p j).ker

abbrev sourceZeroPlane (p : SelectedSupport 1 3) (j : SourceUniformPositions p) :=
  ↥(sourceZeroPlaneSubgroup (V := V) p j)

@[simp]
theorem sourceZeroPlane_condition (p : SelectedSupport 1 3) (j : SourceUniformPositions p)
    (uv : sourceZeroPlane (V := V) p j) : uv.val.2 j = 0 := uv.property

def sourceZeroPlaneEquiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (j : SourceUniformPositions p) :
    sourceZeroPlane (V := V) p j ≃ ShortenedGraph L 0 (sourceZeroInputMask p j) where
  toFun uv := ⟨source p uv.val.1 uv.val.2, by
    constructor
    · intro i hi
      exact (empty_mask_coordinate ⟨i, hi⟩).elim
    · intro i hi
      rw [sourceZeroInputMask, maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact source_inactive p _ _ i hi
      · rw [(singletonMask_bit j.val.val i).mp hi, source_uniform, sourceZeroPlane_condition]⟩
  invFun x := by
    refine ⟨(x.val (residualLabel p), fun i => x.val i.val.val), ?_⟩
    change x.val j.val.val = 0
    apply x.property.2 j.val.val
    rw [sourceZeroInputMask, maskUnion_bit, Bool.or_eq_true]
    exact Or.inr ((singletonMask_bit j.val.val j.val.val).mpr rfl)
  left_inv uv := by
    apply Subtype.ext
    apply Prod.ext
    · exact source_residual p _ _
    · funext i
      exact source_uniform p _ _ i
  right_inv x := by
    apply Subtype.ext
    apply source_reconstruct
    intro i hi
    apply x.property.2 i
    rw [sourceZeroInputMask, maskUnion_bit, Bool.or_eq_true]
    exact Or.inl hi

/-- A double-zero line with one original uniform input and one output zero. -/
def sourceZeroOutputLineSubgroup (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p) :
    AddSubgroup (zeroPlane L p z) :=
  ((uniformValueHom p j).comp (zeroPlaneSubgroup L p z).subtype).ker

abbrev sourceZeroOutputLine (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p) :=
  ↥(sourceZeroOutputLineSubgroup L p z j)

def sourceZeroOutputLineEquiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p) :
    sourceZeroOutputLine L p z j ≃ ShortenedGraph L (singletonMask z) (sourceZeroInputMask p j) where
  toFun c := ⟨source p c.val.val.1 c.val.val.2, by
    constructor
    · intro i hi
      have he : i = z := (singletonMask_bit z i).mp hi
      simpa only [he] using zeroPlane_condition L p z c.val
    · intro i hi
      rw [sourceZeroInputMask, maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · exact source_inactive p _ _ i hi
      · rw [(singletonMask_bit j.val.val i).mp hi, source_uniform]
        exact c.property⟩
  invFun x := by
    have hinactive : OnSource p x.val := by
      intro i hi
      apply x.property.2 i
      rw [sourceZeroInputMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inl hi
    refine ⟨⟨(x.val (residualLabel p), fun i => x.val i.val.val), ?_⟩, ?_⟩
    · change L (source p (x.val (residualLabel p)) (fun i => x.val i.val.val)) z = 0
      rw [source_reconstruct p x.val hinactive]
      exact x.property.1 z ((singletonMask_bit z z).mpr rfl)
    · change x.val j.val.val = 0
      apply x.property.2 j.val.val
      rw [sourceZeroInputMask, maskUnion_bit, Bool.or_eq_true]
      exact Or.inr ((singletonMask_bit j.val.val j.val.val).mpr rfl)
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact source_residual p _ _
    · funext i
      exact source_uniform p _ _ i
  right_inv x := by
    apply Subtype.ext
    apply source_reconstruct
    intro i hi
    apply x.property.2 i
    rw [sourceZeroInputMask, maskUnion_bit, Bool.or_eq_true]
    exact Or.inl hi

end SourceZeros

section SourceZerosFinite
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

instance sourceZeroPlaneFintype (p : SelectedSupport 1 3) (j : SourceUniformPositions p) :
    Fintype (sourceZeroPlane (V := V) p j) := by
  classical
  exact inferInstance

instance sourceZeroOutputLineFintype (L : (Fin 4 → V) →+ (Fin 4 → V))
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p) :
    Fintype (sourceZeroOutputLine L p z j) := by
  classical
  exact inferInstance

theorem sourceZeroPlane_parameter_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j k : SourceUniformPositions p) (hkj : k ≠ j) :
    Function.Bijective (fun uv : sourceZeroPlane (V := V) p j => (uv.val.1, uv.val.2 k)) := by
  have hs : maskSize (0 : Fin 16) + maskSize (sourceZeroInputMask p j) = 2 := by
    rw [show maskSize (0 : Fin 16) = 0 by decide, sourceZeroInputMask_size]
  have hne : residualLabel p ≠ k.val.val := by
    intro he
    exact k.val.property (he ▸ residualLabel_mem p)
  have hb := (shortened_input_pair_bijective L hL 0 (sourceZeroInputMask p j) hs
    (residualLabel p) k.val.val hne (sourceZeroInputMask_not_residual p j)
    (sourceZeroInputMask_not_other p j k hkj)).comp (sourceZeroPlaneEquiv L p j).bijective
  change Function.Bijective (fun uv : sourceZeroPlane (V := V) p j =>
    (source p uv.val.1 uv.val.2 (residualLabel p), source p uv.val.1 uv.val.2 k.val.val)) at hb
  simpa only [source_residual, source_uniform] using hb

def sourceZeroPlaneParameterEquiv
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j k : SourceUniformPositions p) (hkj : k ≠ j) :
    sourceZeroPlane (V := V) p j ≃ V × V :=
  Equiv.ofBijective (fun uv => (uv.val.1, uv.val.2 k))
    (sourceZeroPlane_parameter_bijective L hL p j k hkj)

theorem sourceZeroPlane_residual_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (j k : SourceUniformPositions p) (hkj : k ≠ j) (h : V → ℝ) :
    (∑ uv : sourceZeroPlane (V := V) p j, h uv.val.1 ^ 2) =
      (Fintype.card V : ℝ) * ∑ u : V, h u ^ 2 := by
  have hs := (sourceZeroPlaneParameterEquiv L hL p j k hkj).sum_comp
    (fun a : V × V => h a.1 ^ 2)
  change (∑ uv : sourceZeroPlane (V := V) p j, h uv.val.1 ^ 2) =
    ∑ a : V × V, h a.1 ^ 2 at hs
  rw [hs, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (Finset.mul_sum _ _ _).symm

theorem sourceZeroOutputLine_shortening (p : SelectedSupport 1 3)
    (z : Fin 4) (j : SourceUniformPositions p) :
    maskSize (singletonMask z) + maskSize (sourceZeroInputMask p j) = 3 := by
  rw [singletonMask_size, sourceZeroInputMask_size]

/-- The residual input itself bijectively parameterizes each mixed double-zero line. -/
theorem sourceZeroOutputLine_residual_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p) :
    Function.Bijective (fun c : sourceZeroOutputLine L p z j => c.val.val.1) := by
  have hb := (ShortenedLineResponse.input_coordinate_bijective L hL
    (singletonMask z) (sourceZeroInputMask p j) (sourceZeroOutputLine_shortening p z j)
    (residualLabel p) (sourceZeroInputMask_not_residual p j)).comp
      (sourceZeroOutputLineEquiv L p z j).bijective
  change Function.Bijective (fun c : sourceZeroOutputLine L p z j =>
    source p c.val.val.1 c.val.val.2 (residualLabel p)) at hb
  simpa only [source_residual] using hb

theorem sourceZeroOutputLine_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p)
    (i : Fin 4) (hi : i ≠ z) :
    Function.Bijective (fun c : sourceZeroOutputLine L p z j =>
      L (source p c.val.val.1 c.val.val.2) i) := by
  have hibit : maskBit (singletonMask z) i ≠ true := by
    intro he
    exact hi ((singletonMask_bit z i).mp he)
  exact (ShortenedLineResponse.output_coordinate_bijective L hL
    (singletonMask z) (sourceZeroInputMask p j) (sourceZeroOutputLine_shortening p z j)
    i hibit).comp (sourceZeroOutputLineEquiv L p z j).bijective

theorem sourceZeroOutputLine_residual_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 3) (z : Fin 4) (j : SourceUniformPositions p) (h : V → ℝ) :
    (∑ c : sourceZeroOutputLine L p z j, h c.val.val.1 ^ 2) = ∑ u : V, h u ^ 2 :=
  (Equiv.ofBijective (fun c : sourceZeroOutputLine L p z j => c.val.val.1)
    (sourceZeroOutputLine_residual_bijective L hL p z j)).sum_comp (fun u => h u ^ 2)

end SourceZerosFinite
end AESConcrete.DoubleUniformShortening
