/- Module role: Support projections, orthogonality, centering and distance conversion.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Model.SupportProfile
import AESMixing.SupportRepresentation
import AESMixing.MDSInverse
import AESMixing.ConstraintExpansion

/-!
# Literal zero-complement embeddings for outside support projections

For an arbitrary finite coordinate set, zero insertion, zero extraction,
and the counting embedding are literal coordinate maps. Extraction is the
counting adjoint of the embedding, and the embedding is an isometry.
For every four-position mask, the complementary inactive-mask projection
is exactly E * P * E^*, with P the joint marked residual projection.
The degree-three/support-three component is the sum of the four resulting
orthogonal fixed patterns, on arbitrary signed joint input.

 It supplies identities only: no cap, fiber-constant
input, product-input assumption, local AES estimate, or mixing theorem.
Constructive work only; no attacks or manuscript/predecessor changes.

Direct source pins, SHA-256, 2026-10-20:
AES8/SupportProfile.lean
  b873b7dc3b2af0bba4ef773c91ff5344d071350983c48694e897b12779df304a
AESMixing/SupportRepresentation.lean
  3e0fd449bb8dc97e178f68154e13e7185328f8a55782fe6580d888752b2c25a4
AESMixing/MDSInverse.lean
  56df2df21166ac17b0b7cd38b4e71a91ce96cff527bd872edb2e8cb626d6a9bb
AESMixing/ConstraintExpansion.lean
  57827e66e8cdc10f7c8002e1042c884cc16899f56cfa295e8636f0f083d0bfb3
Used support interfaces, SHA-256:
AESMixing/CoordinateEmbedding.lean
  e15e16aa032c0033e179e1826387874e42bffb244da717d1877f2ed2fe3c3f23
AESMixing/SupportOrthogonality.lean
  759ccc8e3c88f6f1fc56a6c4aebd12c1b65b4031c245e7fafd1a152901aa1def
AESMixing/ProjectedIncidence.lean
  dd763bbc5015743c1609a32ef14a9a7b3dd93e540f303b1c138bb0d8f4d0b1f3
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

noncomputable section
open scoped BigOperators

namespace AES8.ZeroOutsideProjection
open AESMixing AESMixing.AES

section TupleEvaluation
variable {J V : Type*} [Fintype J] [DecidableEq J] [DecidableEq V]

/-- A product of literal zero tests is the test for the constant tuple. -/
theorem prod_identity_const (z : V) (v : J → V) :
    (∏ i, identityKernel (v i) z) =
      if v = (fun _ => z) then (1 : ℝ) else 0 := by
  simp only [identityKernel, product_indicator, funext_iff]

variable [Fintype V]

/-- Symbolic tuple evaluation; no alphabet values are enumerated. -/
theorem zeroTuple_sum (z : V) (f : (J → V) → ℝ) :
    (∑ v : J → V, (∏ i, identityKernel (v i) z) * f v) = f (fun _ => z) := by
  simp_rw [prod_identity_const]
  simp

end TupleEvaluation

section GenericCoordinates
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
variable (p : I → Prop) [DecidablePred p]

/-- Keep all selected coordinates jointly, and insert z at every other position. -/
def zeroInsert (z : V) (u : {i // p i} → V) : I → V :=
  (Equiv.piEquivPiSubtypeProd p (fun _ => V)).symm (u, fun _ => z)

@[simp] theorem zeroInsert_marked (z : V) (u : {i // p i} → V) (i : {i // p i}) :
    zeroInsert p z u i.val = u i := by
  simp [zeroInsert, Equiv.piEquivPiSubtypeProd, i.property]

@[simp] theorem zeroInsert_unmarked (z : V) (u : {i // p i} → V)
    (i : {i // ¬p i}) : zeroInsert p z u i.val = z := by
  simp [zeroInsert, Equiv.piEquivPiSubtypeProd, i.property]

/-- Evaluation on the literal inserted tuple, rather than an average. -/
def zeroExtract (z : V) (f : (I → V) → ℝ) (u : {i // p i} → V) : ℝ :=
  f (zeroInsert p z u)

/-- Counting embedding with a literal delta at every unmarked coordinate. -/
def zeroEmbed (z : V) (g : ({i // p i} → V) → ℝ) : (I → V) → ℝ :=
  coordinateEmbedding p (fun _ x => identityKernel x z) g

theorem zeroEmbed_apply (z : V) (g : ({i // p i} → V) → ℝ) (x : I → V) :
    zeroEmbed p z g x =
      if ∀ i : {i // ¬p i}, x i.val = z then g (fun i => x i.val) else 0 := by
  unfold zeroEmbed coordinateEmbedding
  simp only [identityKernel, product_indicator]
  by_cases h : ∀ i : {i // ¬p i}, x i.val = z <;> simp [h]

theorem zeroExtract_embed (z : V) (g : ({i // p i} → V) → ℝ) :
    zeroExtract p z (zeroEmbed p z g) = g := by
  funext u
  unfold zeroExtract zeroEmbed coordinateEmbedding
  have hm : (fun i : {i // p i} => zeroInsert p z u i.val) = u := by
    funext i
    exact zeroInsert_marked p z u i
  rw [hm]
  simp only [zeroInsert_unmarked]
  simp [identityKernel]

theorem zeroEmbed_energy (z : V) (g : ({i // p i} → V) → ℝ) :
    (∑ x, zeroEmbed p z g x ^ 2) = ∑ u, g u ^ 2 := by
  exact coordinateEmbedding_isometry p (fun _ x => identityKernel x z)
    (fun _ => by simp [identityKernel]) g

/-- Extraction is exactly the counting adjoint, without a cardinality factor. -/
theorem zeroEmbed_adjoint (z : V) (g : ({i // p i} → V) → ℝ)
    (f : (I → V) → ℝ) :
    (∑ x, zeroEmbed p z g x * f x) =
      ∑ u, g u * zeroExtract p z f u := by
  let e := Equiv.piEquivPiSubtypeProd p (fun _ => V)
  have hm (u : {i // p i} → V) (v : {i // ¬p i} → V) (i : {i // p i}) :
      e.symm (u,v) i.val = u i := by
    simp [e, Equiv.piEquivPiSubtypeProd, i.property]
  have hu (u : {i // p i} → V) (v : {i // ¬p i} → V) (i : {i // ¬p i}) :
      e.symm (u,v) i.val = v i := by
    simp [e, Equiv.piEquivPiSubtypeProd, i.property]
  have he (u : {i // p i} → V) (v : {i // ¬p i} → V) :
      zeroEmbed p z g (e.symm (u,v)) = g u * ∏ i, identityKernel (v i) z := by
    unfold zeroEmbed coordinateEmbedding
    have hmarked : (fun i : {i // p i} => e.symm (u,v) i.val) = u := by
      funext i
      exact hm u v i
    rw [hmarked]
    simp only [hu]
  rw [← e.symm.sum_comp (fun x => zeroEmbed p z g x * f x), Fintype.sum_prod_type]
  simp_rw [he]
  apply Finset.sum_congr rfl
  intro u _
  calc
    _ = g u * ∑ v : {i // ¬p i} → V,
        (∏ i, identityKernel (v i) z) * f (e.symm (u,v)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ = g u * zeroExtract p z f u := by
      rw [zeroTuple_sum]
      rfl

end GenericCoordinates

section ComplementMasks
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem complement_disjoint (m : Fin 16) : MaskDisjoint (maskComplement m) m := by
  intro i hi hm
  simp [maskComplement_bit, hm] at hi

private theorem complement_supportConstant (m : Fin 16)
    (i : {i : Fin 4 // maskBit m i ≠ true}) (x : V) :
    supportConstant (maskBit (maskComplement m) i.val) x = identityKernel x 0 := by
  have hi : maskBit m i.val = false := Bool.eq_false_iff.mpr i.property
  simp [supportConstant, maskComplement_bit, hi]

private theorem complement_supportDualConstant (m : Fin 16)
    (i : {i : Fin 4 // maskBit m i ≠ true}) (x : V) :
    supportDualConstant (maskBit (maskComplement m) i.val) x = identityKernel x 0 := by
  have hi : maskBit m i.val = false := Bool.eq_false_iff.mpr i.property
  simp [supportDualConstant, supportConstant, maskComplement_bit, hi]

/-- A complement mask leaves no constant-nonzero coordinate behind. -/
theorem supportEmbedding_complement (m : Fin 16)
    (g : (MaskCoordinates m → V) → ℝ) :
    supportEmbedding (maskComplement m) m g =
      zeroEmbed (fun i : Fin 4 => maskBit m i = true) 0 g := by
  unfold supportEmbedding zeroEmbed
  apply congrArg (fun a : {i : Fin 4 // maskBit m i ≠ true} → V → ℝ =>
    coordinateEmbedding (fun i : Fin 4 => maskBit m i = true) a g)
  funext i x
  exact complement_supportConstant m i x

/-- The dual constants evaluate the complete unmarked tuple at zero. -/
theorem supportCoefficient_complement (m : Fin 16) (f : (Fin 4 → V) → ℝ) :
    supportCoefficient (maskComplement m) m f =
      zeroExtract (fun i : Fin 4 => maskBit m i = true) 0 f := by
  funext u
  unfold supportCoefficient zeroExtract
  simp_rw [complement_supportDualConstant]
  exact zeroTuple_sum (0 : V)
    (fun v => f ((Equiv.piEquivPiSubtypeProd
      (fun i : Fin 4 => maskBit m i = true) (fun _ => V)).symm (u,v)))

def complementKernel (m : Fin 16) : (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  supportProduct 0 (maskBit m) (maskBit (maskComplement m))

def complementProjection (m : Fin 16) (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  action (complementKernel m) f

/-- Exact E * P * E^* on arbitrary signed joint input, for any mask. -/
theorem complementProjection_eq_embed_residual_extract
    (m : Fin 16) (f : (Fin 4 → V) → ℝ) :
    complementProjection m f =
      zeroEmbed (fun i : Fin 4 => maskBit m i = true) 0
        (markedResidual m (zeroExtract (fun i : Fin 4 => maskBit m i = true) 0 f)) := by
  unfold complementProjection complementKernel
  rw [supportProduct_embedding (maskComplement m) m (complement_disjoint m) f,
    supportEmbedding_complement, supportCoefficient_complement]

theorem markedResidual_eq_coordinateResidual (m : Fin 16)
    (g : (MaskCoordinates m → V) → ℝ) :
    markedResidual m g =
      action (coordinateKernel (fun _ : MaskCoordinates m => residualProjection (0 : V))) g := by
  rfl

theorem complementKernel_symmetric (m : Fin 16) (x y : Fin 4 → V) :
    complementKernel m x y = complementKernel m y x :=
  supportProduct_symmetric 0 (maskBit m) (maskBit (maskComplement m)) x y

theorem complementProjection_idempotent (hn : 1 < Fintype.card V)
    (m : Fin 16) (f : (Fin 4 → V) → ℝ) :
    complementProjection m (complementProjection m f) = complementProjection m f := by
  unfold complementProjection complementKernel
  rw [← kernelCompose_action, supportProduct_compose 0 hn, if_pos rfl]

end ComplementMasks

-- All following decidable certificates concern only four position names
-- and two four-bit masks. They do not enumerate AES word or state values.
def singleMask : Fin 4 → Fin 16 := ![1, 2, 4, 8]
def outsideMask (r : Fin 4) : Fin 16 := maskComplement (singleMask r)

theorem singleMask_bit_iff : ∀ r i : Fin 4,
    maskBit (singleMask r) i = true ↔ i = r := by decide

theorem outsideMask_bit_iff : ∀ r i : Fin 4,
    maskBit (outsideMask r) i = true ↔ i ≠ r := by decide

theorem singleMask_injective : Function.Injective singleMask := by decide

abbrev OutsideCoordinates (r : Fin 4) := MaskCoordinates (outsideMask r)

section FixedPatterns
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def insertZero (r : Fin 4) (u : OutsideCoordinates r → V) : Fin 4 → V :=
  zeroInsert (fun i : Fin 4 => maskBit (outsideMask r) i = true) 0 u

def extractZero (r : Fin 4) (f : (Fin 4 → V) → ℝ) : (OutsideCoordinates r → V) → ℝ :=
  zeroExtract (fun i : Fin 4 => maskBit (outsideMask r) i = true) 0 f

def embedZero (r : Fin 4) (g : (OutsideCoordinates r → V) → ℝ) : (Fin 4 → V) → ℝ :=
  zeroEmbed (fun i : Fin 4 => maskBit (outsideMask r) i = true) 0 g

def Q (r : Fin 4) (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  complementProjection (outsideMask r) f

@[simp] theorem insertZero_omitted (r : Fin 4) (u : OutsideCoordinates r → V) :
    insertZero r u r = 0 := by
  have hr : maskBit (outsideMask r) r ≠ true := by
    simp [outsideMask_bit_iff]
  exact zeroInsert_unmarked (fun i : Fin 4 => maskBit (outsideMask r) i = true)
    (0 : V) u ⟨r,hr⟩

@[simp] theorem insertZero_retained (r : Fin 4) (u : OutsideCoordinates r → V)
    (i : OutsideCoordinates r) : insertZero r u i.val = u i :=
  zeroInsert_marked (fun i : Fin 4 => maskBit (outsideMask r) i = true) (0 : V) u i

/-- Literal e0 insertion, with every other coordinate still joint. -/
theorem embedZero_apply (r : Fin 4) (g : (OutsideCoordinates r → V) → ℝ)
    (y : Fin 4 → V) :
    embedZero r g y = if y r = 0 then g (fun i => y i.val) else 0 := by
  unfold embedZero
  rw [zeroEmbed_apply]
  have hzero :
      (∀ i : {i : Fin 4 // ¬maskBit (outsideMask r) i = true}, y i.val = 0) ↔
        y r = 0 := by
    constructor
    · intro h
      exact h ⟨r, by simp [outsideMask_bit_iff]⟩
    · intro h i
      have hir : i.val = r := by
        by_contra hne
        exact i.property ((outsideMask_bit_iff r i.val).mpr hne)
      simpa only [hir] using h
  simp only [hzero]

theorem extractZero_embedZero (r : Fin 4) (g : (OutsideCoordinates r → V) → ℝ) :
    extractZero r (embedZero r g) = g :=
  zeroExtract_embed (fun i : Fin 4 => maskBit (outsideMask r) i = true) (0 : V) g

theorem embedZero_energy (r : Fin 4) (g : (OutsideCoordinates r → V) → ℝ) :
    (∑ x, embedZero r g x ^ 2) = ∑ u, g u ^ 2 :=
  zeroEmbed_energy (fun i : Fin 4 => maskBit (outsideMask r) i = true) (0 : V) g

theorem Q_eq_support_action (r : Fin 4) (f : (Fin 4 → V) → ℝ) :
    Q r f = action (supportProduct (0 : V)
      (maskBit (outsideMask r)) (maskBit (singleMask r))) f := by
  simp only [Q, complementProjection, complementKernel, outsideMask,
    maskComplement_involutive]

theorem Q_eq_embed_residual_extract (r : Fin 4) (f : (Fin 4 → V) → ℝ) :
    Q r f = embedZero r (markedResidual (outsideMask r) (extractZero r f)) :=
  complementProjection_eq_embed_residual_extract (outsideMask r) f

theorem Q_idempotent (hn : 1 < Fintype.card V) (r : Fin 4)
    (f : (Fin 4 → V) → ℝ) : Q r (Q r f) = Q r f :=
  complementProjection_idempotent hn (outsideMask r) f

theorem Q_orthogonal (hn : 1 < Fintype.card V) (r s : Fin 4) (hrs : r ≠ s)
    (f g : (Fin 4 → V) → ℝ) : (∑ x, Q r f x * Q s g x) = 0 := by
  simp_rw [Q_eq_support_action]
  apply supportProduct_mixed_orthogonal (0 : V) hn
  intro h
  exact hrs (singleMask_injective (maskBits_injective h.2))

theorem extractZero_Q (r : Fin 4) (f : (Fin 4 → V) → ℝ) :
    extractZero r (Q r f) = markedResidual (outsideMask r) (extractZero r f) := by
  rw [Q_eq_embed_residual_extract, extractZero_embedZero]

theorem residualCoefficient_fixed (hn : 1 < Fintype.card V) (r : Fin 4)
    (f : (Fin 4 → V) → ℝ) :
    markedResidual (outsideMask r)
      (markedResidual (outsideMask r) (extractZero r f)) =
        markedResidual (outsideMask r) (extractZero r f) :=
  markedResidual_idempotent hn (outsideMask r) (extractZero r f)

theorem Q_energy_eq_coefficient (r : Fin 4) (f : (Fin 4 → V) → ℝ) :
    (∑ x, Q r f x ^ 2) =
      ∑ u, markedResidual (outsideMask r) (extractZero r f) u ^ 2 := by
  rw [Q_eq_embed_residual_extract, embedZero_energy]

end FixedPatterns

section ComponentEleven
open AES8.SupportProfile (Label Valid raw)

def patternLabel (r : Fin 4) : Label := (outsideMask r, singleMask r)

def SelectedLabel (p : Label) : Prop :=
  Valid p ∧ maskSize p.1 = 3 ∧ 4 - maskSize p.2 = 3

instance (p : Label) : Decidable (SelectedLabel p) := by
  unfold SelectedLabel
  infer_instance

theorem patternLabel_selected : ∀ r : Fin 4, SelectedLabel (patternLabel r) := by decide

def patternLabelEquiv : Fin 4 ≃ {p : Label // SelectedLabel p} :=
  Equiv.ofBijective (fun r => ⟨patternLabel r, patternLabel_selected r⟩) (by decide)

theorem Q_eq_raw (r : Fin 4) (f : AES.WordState → ℝ) :
    Q r f = raw (patternLabel r) f :=
  Q_eq_support_action r f

/-- Exact refined-component equality, including vanishing invalid mask pairs. -/
theorem component_eleven_eq_sum_Q (f : AES.WordState → ℝ) :
    SupportProfile.component f 11 = fun y => ∑ r : Fin 4, Q r f y := by
  funext y
  rw [SupportProfile.component_eq_support_residual]
  change (∑ p : Label, if maskSize p.1 = 3 ∧ 4 - maskSize p.2 = 3
    then raw p f y else 0) = _
  have ht (p : Label) :
      (if maskSize p.1 = 3 ∧ 4 - maskSize p.2 = 3 then raw p f y else 0) =
        if SelectedLabel p then raw p f y else 0 := by
    by_cases hv : Valid p
    · simp only [SelectedLabel, hv, true_and]
    · simp [SelectedLabel, hv, SupportProfile.raw_invalid p hv f]
  simp_rw [ht]
  have hs : (∑ p : {p : Label // SelectedLabel p}, raw p.val f y) =
      ∑ p : Label, if SelectedLabel p then raw p f y else 0 := by
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [← hs]
  calc
    _ = ∑ r : Fin 4, raw (patternLabel r) f y :=
      (patternLabelEquiv.sum_comp (fun p => raw p.val f y)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      exact congrFun (Q_eq_raw r f).symm y

theorem component_eleven_energy (f : AES.WordState → ℝ) :
    (∑ x, SupportProfile.component f 11 x ^ 2) =
      ∑ r : Fin 4, ∑ x, Q r f x ^ 2 := by
  rw [component_eleven_eq_sum_Q]
  exact orthogonal_family_energy (fun r : Fin 4 => Q r f)
    (fun r s hrs => Q_orthogonal SupportProfile.word_card_gt_one r s hrs f f)

end ComponentEleven
end AES8.ZeroOutsideProjection
