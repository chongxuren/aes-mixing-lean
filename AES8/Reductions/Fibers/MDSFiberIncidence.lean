/- Module role: Actual AES fiber domains, coordinate bijections and incidence identities.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Fibers.MDSFiberCollision
import AES8.Math.FiberIncidence

/-!
# Normalized incidence on actual MDS observation images

The target below consists of precisely the observations attained by an actual
prescribed-coordinate affine graph.  Its projection has fiber cardinality
`|V|^(4 - total)`, with truncated natural subtraction.  For `total ≤ 4` this
is the prescribed-coordinate MDS count.  For `4 ≤ total`, the existing MDS
zero theorem proves injection, and admissibility supplies the unique preimage.
In particular, the latter case requires no surjectivity onto all tuples.

The proved cardinality supplies the hypotheses of the generic normalized-fiber
isometry.  A separate low-dimensional statement also exposes the isometry on
the full tuple target, where the existing MDS count applies to every label.
These are raw graph-fiber identities.  Identification with marked middle-image
codes, coordinate inclusions, Fourier changes and local AES operator estimates
remain separate obligations.  Constructive proof work only; no attacks or
predecessor/manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace AES8.MDSFiberIncidence
open AESMixing AESMixing.AES AES8.MDSFiberCollision

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The literal range of the selected observation map on the prescribed graph. -/
abbrev AdmissibleImage (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (u v : Fin 4 → V) :=
  {y : ObservedIndex out inp → V //
    ∃ x : AffineGraph L r z u v, projection L r z out inp u v x = y}

instance admissibleImageFintype (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (u v : Fin 4 → V) :
    Fintype (AdmissibleImage L r z out inp u v) :=
  Fintype.ofFinite _

/-- Observation with its attained-label witness retained in the target type. -/
def imageProjection (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (x : AffineGraph L r z u v) : AdmissibleImage L r z out inp u v :=
  ⟨projection L r z out inp u v x, ⟨x, rfl⟩⟩

@[simp] theorem imageProjection_val (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (u v : Fin 4 → V) (x : AffineGraph L r z u v) :
    (imageProjection L r z out inp u v x).val = projection L r z out inp u v x :=
  rfl

/-- Surjectivity is onto the explicitly attained labels, for arbitrary masks. -/
theorem imageProjection_surjective (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (u v : Fin 4 → V) :
    Function.Surjective (imageProjection L r z out inp u v) := by
  intro y
  rcases y.property with ⟨x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

/-- Restricting the target to the attained image leaves each nonempty fiber unchanged. -/
def imageProjectionFiberEquiv (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (y : AdmissibleImage L r z out inp u v) :
    {x : AffineGraph L r z u v // imageProjection L r z out inp u v x = y} ≃
      {x : AffineGraph L r z u v // projection L r z out inp u v x = y.val} where
  toFun x := ⟨x.val, congrArg Subtype.val x.property⟩
  invFun x := ⟨x.val, Subtype.ext x.property⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl

/-- The existing low-dimensional MDS count applies to each attained label. -/
theorem imageProjection_fiber_card_low
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hle : maskSize r + maskSize z + maskSize out + maskSize inp ≤ 4)
    (y : AdmissibleImage L r z out inp u v) :
    Fintype.card
        {x : AffineGraph L r z u v // imageProjection L r z out inp u v x = y} =
      Fintype.card V ^
        (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)) := by
  rw [Fintype.card_congr (imageProjectionFiberEquiv L r z out inp u v y)]
  exact projection_fiber_card L hL r z out inp u v hr hz hle y.val

/-- At least four distinct fixed/observed graph coordinates determine the input. -/
theorem projection_injective_high
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hle : 4 ≤ maskSize r + maskSize z + maskSize out + maskSize inp) :
    Function.Injective (projection L r z out inp u v) := by
  intro x y he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply mds_graph_zero_high L hL (maskUnion r out) (maskUnion z inp)
  · rw [maskUnion_size r out hr, maskUnion_size z inp hz]
    omega
  · constructor
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rw [map_sub]
      change L x.val i - L y.val i = 0
      apply sub_eq_zero.mpr
      rcases hi with hi | hi
      · rw [x.property.1 i hi, y.property.1 i hi]
      · exact congrFun he (Sum.inl ⟨i, hi⟩)
    · intro i hi
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      change x.val i - y.val i = 0
      apply sub_eq_zero.mpr
      rcases hi with hi | hi
      · rw [x.property.2 i hi, y.property.2 i hi]
      · exact congrFun he (Sum.inr ⟨i, hi⟩)

theorem imageProjection_injective_high
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hle : 4 ≤ maskSize r + maskSize z + maskSize out + maskSize inp) :
    Function.Injective (imageProjection L r z out inp u v) := by
  intro x y he
  exact projection_injective_high L hL r z out inp u v hr hz hle
    (congrArg Subtype.val he)

/-- Every admissible high-dimensional label has exactly one preimage. -/
theorem imageProjection_fiber_card_high
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hle : 4 ≤ maskSize r + maskSize z + maskSize out + maskSize inp)
    (y : AdmissibleImage L r z out inp u v) :
    Fintype.card
      {x : AffineGraph L r z u v // imageProjection L r z out inp u v x = y} = 1 := by
  rcases imageProjection_surjective L r z out inp u v y with ⟨x, hx⟩
  have hinj := imageProjection_injective_high L hL r z out inp u v hr hz hle
  letI : Unique
      {x : AffineGraph L r z u v // imageProjection L r z out inp u v x = y} :=
    { default := ⟨x, hx⟩
      uniq := fun w => Subtype.ext (hinj (w.property.trans hx.symm)) }
  simp

/-- Exact multiplicity on the admissible image, with no equal-fiber premise. -/
theorem imageProjection_fiber_card
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (y : AdmissibleImage L r z out inp u v) :
    Fintype.card
        {x : AffineGraph L r z u v // imageProjection L r z out inp u v x = y} =
      Fintype.card V ^
        (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)) := by
  by_cases hle : maskSize r + maskSize z + maskSize out + maskSize inp ≤ 4
  · exact imageProjection_fiber_card_low L hL r z out inp u v hr hz hle y
  · have hhigh : 4 ≤ maskSize r + maskSize z + maskSize out + maskSize inp := by omega
    rw [imageProjection_fiber_card_high L hL r z out inp u v hr hz hhigh y]
    simp [Nat.sub_eq_zero_of_le hhigh]

/-- The multiplicity used in normalization is positive because `V` contains zero. -/
theorem fiberMultiplicity_pos (r z out inp : Fin 16) :
    0 < Fintype.card V ^
      (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)) :=
  pow_pos (Fintype.card_pos_iff.mpr ⟨(0 : V)⟩) _

/-- Normalized observation lift preserves signed counting energy on the actual image. -/
theorem imageProjection_normalizedLift_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : AdmissibleImage L r z out inp u v → ℝ) :
    (∑ x : AffineGraph L r z u v,
      FiberIncidence.normalizedLift (imageProjection L r z out inp u v)
        (Fintype.card V ^
          (4 - (maskSize r + maskSize z + maskSize out + maskSize inp))) f x ^ 2) =
      ∑ y : AdmissibleImage L r z out inp u v, f y ^ 2 := by
  exact FiberIncidence.normalizedLift_energy
    (imageProjection L r z out inp u v)
    (Fintype.card V ^
      (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)))
    (fiberMultiplicity_pos r z out inp)
    (imageProjection_fiber_card L hL r z out inp u v hr hz) f

/-- The counting-`l2` isometry holds for all masks on the explicit admissible image. -/
theorem imageProjection_normalizedLift_l2
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : AdmissibleImage L r z out inp u v → ℝ) :
    AESMixing.l2
        (FiberIncidence.normalizedLift (imageProjection L r z out inp u v)
          (Fintype.card V ^
            (4 - (maskSize r + maskSize z + maskSize out + maskSize inp))) f) =
      AESMixing.l2 f := by
  exact FiberIncidence.normalizedLift_l2
    (imageProjection L r z out inp u v)
    (Fintype.card V ^
      (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)))
    (fiberMultiplicity_pos r z out inp)
    (imageProjection_fiber_card L hL r z out inp u v hr hz) f

/-- At most four fixed/observed coordinates also permit the full tuple target. -/
theorem projection_normalizedLift_l2_low
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (u v : Fin 4 → V)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (hle : maskSize r + maskSize z + maskSize out + maskSize inp ≤ 4)
    (f : (ObservedIndex out inp → V) → ℝ) :
    AESMixing.l2
        (FiberIncidence.normalizedLift (projection L r z out inp u v)
          (Fintype.card V ^
            (4 - (maskSize r + maskSize z + maskSize out + maskSize inp))) f) =
      AESMixing.l2 f := by
  exact FiberIncidence.normalizedLift_l2
    (projection L r z out inp u v)
    (Fintype.card V ^
      (4 - (maskSize r + maskSize z + maskSize out + maskSize inp)))
    (fiberMultiplicity_pos r z out inp)
    (projection_fiber_card L hL r z out inp u v hr hz hle) f

/-- Concrete grouped AES boundary specialization on its attained observation image. -/
theorem aes_imageProjection_normalizedLift_l2 (r z out inp : Fin 16)
    (u v : AES.WordState) (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : AdmissibleImage AESPaper.GroupedRecurrence.boundary.toAddMonoidHom
      r z out inp u v → ℝ) :
    AESMixing.l2
        (FiberIncidence.normalizedLift
          (imageProjection AESPaper.GroupedRecurrence.boundary.toAddMonoidHom
            r z out inp u v)
          (Fintype.card AES.Word ^
            (4 - (maskSize r + maskSize z + maskSize out + maskSize inp))) f) =
      AESMixing.l2 f :=
  imageProjection_normalizedLift_l2 AESPaper.GroupedRecurrence.boundary.toAddMonoidHom
    AESPaper.ActivityKernel.aesBoundary_zeroMDS r z out inp u v hr hz f

end AES8.MDSFiberIncidence
