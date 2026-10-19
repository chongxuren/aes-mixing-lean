import AESConcrete.ShortenedByteLinearity
import AESConcrete.LineOverlap
import AESMixing.IncidenceCounting

/-!
# Actual shortened-line geometry and slope ratios

For a fixed marked output triple, three-zero choices lie among the other
five graph positions. Their zero masks share at least one position; distinct
choices have a union of at least four positions. The MDS zero theorem then
rules out a common ratio in all three derived line coefficients. Sharing two
zero positions rules out even a repeated ratio in two marked coordinates.
The coefficient maps come from the actual AES shortening, not a slope table.
Constructive scope only; plane/Fourier geometry remains separate.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedLineGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedByteLinearity
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.ByteLineBounds (leg)
open AESConcrete.DampedLineGram (lineResponse)

private theorem mask_union_comm : ∀ r s : Fin 16, maskUnion r s = maskUnion s r := by decide
private theorem mask_size_le_four : ∀ r : Fin 16, maskSize r ≤ 4 := by decide
private theorem mask_union_size_ge : ∀ r s : Fin 16, maskSize r ≤ maskSize (maskUnion r s) := by decide
private theorem mask_union_size_eq : ∀ r s : Fin 16,
    maskSize (maskUnion r s) = maskSize r → maskUnion r s = r := by decide
private theorem mask_union_intersection_size : ∀ r s : Fin 16,
    maskSize (maskUnion r s) + maskSize (maskIntersection r s) = maskSize r + maskSize s := by decide

theorem choice_common_nonempty (out : Fin 16) (hout : maskSize out = 3)
    (p q : ShorteningChoice out 3) :
    1 ≤ maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) := by
  have hdisj : MaskDisjoint (maskUnion p.val.1 q.val.1) out := by
    intro i hi ho
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    rcases hi with hi | hi
    · exact p.property.1 i hi ho
    · exact q.property.1 i hi ho
  have hr := disjoint_mask_size_le_four _ _ hdisj
  have hz := mask_size_le_four (maskUnion p.val.2 q.val.2)
  have he1 := mask_union_intersection_size p.val.1 q.val.1
  have he2 := mask_union_intersection_size p.val.2 q.val.2
  have hp := p.property.2
  have hq := q.property.2
  omega

theorem choice_union_high (out : Fin 16) (p q : ShorteningChoice out 3) (hpq : p ≠ q) :
    4 ≤ maskSize (maskUnion p.val.1 q.val.1) + maskSize (maskUnion p.val.2 q.val.2) := by
  have hp := p.property.2
  have hq := q.property.2
  have hp1 := mask_union_size_ge p.val.1 q.val.1
  have hp2 := mask_union_size_ge p.val.2 q.val.2
  have hq1 := mask_union_size_ge q.val.1 p.val.1
  have hq2 := mask_union_size_ge q.val.2 p.val.2
  rw [mask_union_comm q.val.1 p.val.1] at hq1
  rw [mask_union_comm q.val.2 p.val.2] at hq2
  by_contra hlow
  have he1 : maskSize (maskUnion p.val.1 q.val.1) = maskSize p.val.1 := by omega
  have he2 : maskSize (maskUnion p.val.2 q.val.2) = maskSize p.val.2 := by omega
  have he1' : maskSize (maskUnion q.val.1 p.val.1) = maskSize q.val.1 := by
    rw [mask_union_comm q.val.1 p.val.1]
    omega
  have he2' : maskSize (maskUnion q.val.2 p.val.2) = maskSize q.val.2 := by
    rw [mask_union_comm q.val.2 p.val.2]
    omega
  have h1 : p.val.1 = q.val.1 := by
    have ha := mask_union_size_eq p.val.1 q.val.1 he1
    have hb := mask_union_size_eq q.val.1 p.val.1 he1'
    rw [mask_union_comm q.val.1 p.val.1] at hb
    exact ha.symm.trans hb
  have h2 : p.val.2 = q.val.2 := by
    have ha := mask_union_size_eq p.val.2 q.val.2 he2
    have hb := mask_union_size_eq q.val.2 p.val.2 he2'
    rw [mask_union_comm q.val.2 p.val.2] at hb
    exact ha.symm.trans hb
  exact hpq (Subtype.ext (Prod.ext h1 h2))

section MDSGeometry
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem graph_zeros_union (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z r' z' : Fin 16) (x : Fin 4 → V)
    (hx : graphZeroConditions L r z x) (hx' : graphZeroConditions L r' z' x) :
    graphZeroConditions L (maskUnion r r') (maskUnion z z') x := by
  constructor
  · intro i hi
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    exact hi.elim (hx.1 i) (hx'.1 i)
  · intro i hi
    rw [maskUnion_bit, Bool.or_eq_true] at hi
    exact hi.elim (hx.2 i) (hx'.2 i)

/-- Enough common zero constraints and equal output coordinates force
the two actual graph points to agree. -/
theorem shortened_points_equal (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z r' z' sel : Fin 16)
    (hdisj : MaskDisjoint (maskIntersection r r') sel)
    (hsize : 4 ≤ maskSize (maskIntersection r r') + maskSize (maskIntersection z z') + maskSize sel)
    (x : ShortenedGraph L r z) (y : ShortenedGraph L r' z')
    (heq : ∀ i, maskBit sel i = true → L x.val i = L y.val i) : x.val = y.val := by
  apply sub_eq_zero.mp
  apply mds_graph_zero_high L hL (maskUnion (maskIntersection r r') sel)
    (maskIntersection z z')
  · rw [maskUnion_size _ _ hdisj]
    omega
  · constructor
    · intro i hi
      rw [map_sub]
      change L x.val i - L y.val i = 0
      apply sub_eq_zero.mpr
      rw [maskUnion_bit, Bool.or_eq_true] at hi
      rcases hi with hi | hi
      · simp only [maskIntersection_bit, Bool.and_eq_true] at hi
        rw [x.property.1 i hi.1, y.property.1 i hi.2]
      · exact heq i hi
    · intro i hi
      change x.val i - y.val i = 0
      simp only [maskIntersection_bit, Bool.and_eq_true] at hi
      rw [x.property.2 i hi.1, y.property.2 i hi.2, sub_self]

theorem equal_points_zero (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (out : Fin 16) (p q : ShorteningChoice out 3) (hpq : p ≠ q)
    (x : ShortenedGraph L p.val.1 p.val.2) (y : ShortenedGraph L q.val.1 q.val.2)
    (hxy : x.val = y.val) : x.val = 0 := by
  apply mds_graph_zero_high L hL (maskUnion p.val.1 q.val.1) (maskUnion p.val.2 q.val.2)
    (choice_union_high out p q hpq) x.val
  apply graph_zeros_union
  · exact x.property
  · rw [hxy]
    exact y.property

end MDSGeometry

/-- An explicit enumeration of the three marked output coordinates.
The equivalence carries both distinctness and coverage of the chosen mask. -/
def markedPositions {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out) : Fin 3 → GraphPosition :=
  fun i => Sum.inl (e i).val

theorem marked_remaining {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (i : Fin 3) : remaining p.val.1 p.val.2 (markedPositions e i) := by
  intro h
  exact p.property.1 (e i).val h (e i).property

def coefficient (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) : Fin 3 → Byte :=
  lineCoefficient inverse p.val.1 p.val.2 p.property.2 (markedPositions e) (marked_remaining e p)

theorem coefficient_nonzero (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (i : Fin 3) : coefficient inverse e p i ≠ 0 :=
  lineCoefficient_ne_zero inverse p.val.1 p.val.2 p.property.2
    (markedPositions e) (marked_remaining e p) i

def basisPoint (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) : ShortenedGraph (byteDiffusionHom inverse) p.val.1 p.val.2 :=
  (coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    p.val.1 p.val.2 p.property.2 (markedPositions e 0) (marked_remaining e p 0)).symm 1

theorem basis_coordinate (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (i : Fin 3) :
    byteDiffusionHom inverse (basisPoint inverse e p).val (e i).val = coefficient inverse e p i := by
  exact (lineCoordinatePerm_apply (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    p.val.1 p.val.2 p.property.2 (markedPositions e) (marked_remaining e p) i 1).symm

theorem basis_nonzero (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) : (basisPoint inverse e p).val ≠ 0 := by
  have href : byteDiffusionHom inverse (basisPoint inverse e p).val (e 0).val = 1 := by
    have h := (coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      p.val.1 p.val.2 p.property.2 (markedPositions e 0) (marked_remaining e p 0)).apply_symm_apply 1
    rw [coordinateEquiv_apply] at h
    exact h
  intro h
  rw [h, map_zero] at href
  exact zero_ne_one href

theorem scaled_basis_coordinate (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p : ShorteningChoice out 3) (c : Byte) (i : Fin 3) :
    byteDiffusionHom inverse (scaleGraph inverse p.val.1 p.val.2 c (basisPoint inverse e p)).val (e i).val =
      c * coefficient inverse e p i := by
  have h := graphCoordinate_scale inverse p.val.1 p.val.2 c (basisPoint inverse e p) (markedPositions e i)
  change byteDiffusionHom inverse (scaleGraph inverse p.val.1 p.val.2 c (basisPoint inverse e p)).val (e i).val =
    c * byteDiffusionHom inverse (basisPoint inverse e p).val (e i).val at h
  rw [basis_coordinate] at h
  exact h

private theorem pair_equal_at_ratio (inverse : Bool) {out : Fin 16} (e : Fin 3 ≃ MaskCoordinates out)
    (p q : ShorteningChoice out 3) (c : Byte) (i : Fin 3)
    (hc : c = coefficient inverse e p i / coefficient inverse e q i) :
    byteDiffusionHom inverse (basisPoint inverse e p).val (e i).val =
      byteDiffusionHom inverse
        (scaleGraph inverse q.val.1 q.val.2 c (basisPoint inverse e q)).val (e i).val := by
  rw [basis_coordinate, scaled_basis_coordinate, hc]
  field_simp [coefficient_nonzero inverse e q i]

private theorem common_disjoint_out {out : Fin 16} (p q : ShorteningChoice out 3) :
    MaskDisjoint (maskIntersection p.val.1 q.val.1) out := by
  intro i hi ho
  simp only [maskIntersection_bit, Bool.and_eq_true] at hi
  exact p.property.1 i hi.1 ho

/-- Distinct actual three-zero choices cannot define a common slope ratio
in all three marked coordinates. This supplies the eta2 geometric premise. -/
theorem distinct_choices_ratios_nonconstant (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p q : ShorteningChoice out 3) (hpq : p ≠ q) :
    ¬ (coefficient inverse e p 0 / coefficient inverse e q 0 =
        coefficient inverse e p 1 / coefficient inverse e q 1 ∧
      coefficient inverse e p 1 / coefficient inverse e q 1 =
        coefficient inverse e p 2 / coefficient inverse e q 2) := by
  intro hr
  let c := coefficient inverse e p 0 / coefficient inverse e q 0
  let x := basisPoint inverse e p
  let y := scaleGraph inverse q.val.1 q.val.2 c (basisPoint inverse e q)
  have hratio (i : Fin 3) : c = coefficient inverse e p i / coefficient inverse e q i := by
    fin_cases i
    · rfl
    · exact hr.1
    · exact hr.1.trans hr.2
  have heq (i : Fin 4) (hi : maskBit out i = true) :
      byteDiffusionHom inverse x.val i = byteDiffusionHom inverse y.val i := by
    obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
    have hv : (e j).val = i := congrArg Subtype.val hj
    simpa only [hv] using pair_equal_at_ratio inverse e p q c j (hratio j)
  have hxy := shortened_points_equal (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    p.val.1 p.val.2 q.val.1 q.val.2 out (common_disjoint_out p q)
    (by have hc := choice_common_nonempty out hout p q; omega) x y heq
  exact basis_nonzero inverse e p
    (equal_points_zero (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) out p q hpq x y hxy)

private theorem pair_mask_size : ∀ i j : Fin 4, i ≠ j →
    maskSize (maskUnion (singletonMask i) (singletonMask j)) = 2 := by decide

/-- Two shared zero positions make the three coordinate slope ratios
pairwise distinct. This supplies the eta1 geometric premise. -/
theorem two_common_zeros_ratios_injective (inverse : Bool) (out : Fin 16)
    (e : Fin 3 ≃ MaskCoordinates out) (p q : ShorteningChoice out 3) (hpq : p ≠ q)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 2) :
    Function.Injective (fun i => coefficient inverse e p i / coefficient inverse e q i) := by
  intro i j hij
  by_contra hne
  let sel := maskUnion (singletonMask (e i).val) (singletonMask (e j).val)
  have hpos : (e i).val ≠ (e j).val := by
    intro h
    exact hne (e.injective (Subtype.ext h))
  have hsel : maskSize sel = 2 := pair_mask_size _ _ hpos
  have hbits (k : Fin 4) : maskBit sel k = true ↔ k = (e i).val ∨ k = (e j).val := by
    simp only [sel, maskUnion_bit, Bool.or_eq_true, singletonMask_bit]
  have hdisj : MaskDisjoint (maskIntersection p.val.1 q.val.1) sel := by
    intro k hk hs
    have ho : maskBit out k = true := by
      rcases (hbits k).mp hs with hi | hj
      · simpa only [hi] using (e i).property
      · simpa only [hj] using (e j).property
    exact common_disjoint_out p q k hk ho
  let c := coefficient inverse e p i / coefficient inverse e q i
  let x := basisPoint inverse e p
  let y := scaleGraph inverse q.val.1 q.val.2 c (basisPoint inverse e q)
  have heq (k : Fin 4) (hk : maskBit sel k = true) :
      byteDiffusionHom inverse x.val k = byteDiffusionHom inverse y.val k := by
    rcases (hbits k).mp hk with hi | hj
    · subst k
      exact pair_equal_at_ratio inverse e p q c i rfl
    · subst k
      exact pair_equal_at_ratio inverse e p q c j hij
  have hxy := shortened_points_equal (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    p.val.1 p.val.2 q.val.1 q.val.2 sel hdisj (by omega) x y heq
  exact basis_nonzero inverse e p
    (equal_points_zero (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) out p q hpq x y hxy)

end AESConcrete.ShortenedLineGeometry
