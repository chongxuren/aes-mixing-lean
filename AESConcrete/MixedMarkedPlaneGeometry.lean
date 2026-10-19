import AESConcrete.MixedMarkedPlaneLinearity
import AESConcrete.MixedSelectedSurjection

/-!
# Ratio separation for actual mixed-plane trace duals

Prescribed-coordinate graph decomposition proves that two two-zero
shortenings with at most one common zero have marked images summing onto
the selected physical triple. Their actual trace duals therefore have no
common nonzero point. One common zero sharpens the resulting nonconstant
dual ratios to injective ratios. Constructive mathematics only; no attacks,
assumed code dimensions or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MixedMarkedPlaneGeometry
open AESMixing AESMixing.AES
open AESConcrete.ShortenedLineResponse
open AESConcrete.MixedMarkedCoordinates
open AESConcrete.MixedMarkedPlane
open AESConcrete.MixedMarkedPlaneLinearity

abbrev Byte := BinaryWord 8
set_option maxRecDepth 100000

theorem remaining_union (r z r' z' : Fin 16) (p : GraphPosition)
    (hp : remaining r z p) (hp' : remaining r' z' p) :
    remaining (maskUnion r r') (maskUnion z z') p := by
  cases p with
  | inl i =>
    intro h
    rw [maskUnion_bit, Bool.or_eq_true] at h
    exact h.elim hp hp'
  | inr i =>
    intro h
    rw [maskUnion_bit, Bool.or_eq_true] at h
    exact h.elim hp hp'

/-- The reused decomposition is generic in the raw masks. Its out=0
parameter supplies vacuous mask disjointness, not a coordinate relabeling. -/
theorem actual_plane_sum_surjective (inverse : Bool) (r z r' z' : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (hplane' : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i))
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') ≤ 1)
    (y : Fin 3 → Byte) :
    ∃ (a : plane inverse r z marked) (b : plane inverse r' z' marked), y = a.val + b.val := by
  obtain ⟨x,hx⟩ := MixedSelectedSurjection.selected_projection_surjective
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    (maskIntersection r r') (maskIntersection z z') marked hmarked
    (fun i => remaining_common r z r' z' (marked i) (hm i))
    (by simp only [Fintype.card_fin]; omega) y
  let p : ShorteningChoice 0 2 := ⟨(r,z),mask_disjoint_empty r,hplane⟩
  let q : ShorteningChoice 0 2 := ⟨(r',z'),mask_disjoint_empty r',hplane'⟩
  obtain ⟨xp,xq,hsplit⟩ := ShortenedPlaneGeometry.graph_decomposition
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) 0 p q x.val x.property
  let a : plane inverse r z marked :=
    ⟨projectionHom inverse r z marked ⟨xp.val,xp.property⟩,⟨⟨xp.val,xp.property⟩,rfl⟩⟩
  let b : plane inverse r' z' marked :=
    ⟨projectionHom inverse r' z' marked ⟨xq.val,xq.property⟩,⟨⟨xq.val,xq.property⟩,rfl⟩⟩
  refine ⟨a,b,?_⟩
  funext i
  have hi := congrFun hx i
  change graphCoordinate (byteDiffusionHom inverse) x.val (marked i) = y i at hi
  change y i = graphCoordinate (byteDiffusionHom inverse) xp.val (marked i) +
    graphCoordinate (byteDiffusionHom inverse) xq.val (marked i)
  rw [← hi,hsplit]
  cases marked i <;> simp [graphCoordinate,map_add]

theorem common_dual_zero (inverse : Bool) (r z r' z' : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (hplane' : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i))
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') ≤ 1)
    (w : Fin 3 → Byte) (hp : w ∈ dualPlane inverse r z marked)
    (hq : w ∈ dualPlane inverse r' z' marked) : w = 0 := by
  by_contra hw
  obtain ⟨y,hy⟩ := (bytePairing.product (Fin 3)).nondegenerate w hw
  obtain ⟨a,b,hab⟩ := actual_plane_sum_surjective inverse r z r' z' hplane hplane'
    marked hmarked hm hcommon y
  have hpa : (bytePairing.product (Fin 3)).value w a.val = 1 := hp a
  have hqb : (bytePairing.product (Fin 3)).value w b.val = 1 := hq b
  apply hy
  rw [hab,CharacterPairing.add_right,hpa,hqb,_root_.one_mul]

theorem dualBasis_nonzero (inverse : Bool) (r z : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (marked : Fin 3 → GraphPosition)
    (hmarked : Function.Injective marked) (hm : ∀ i, remaining r z (marked i)) :
    (dualParam inverse r z hplane marked hmarked hm 1).val ≠ 0 := by
  have href : (dualParam inverse r z hplane marked hmarked hm 1).val 0 = 1 := by
    change (dualCoordinateEquiv inverse r z hplane marked hmarked hm 0)
      ((dualCoordinateEquiv inverse r z hplane marked hmarked hm 0).symm 1) = 1
    exact Equiv.apply_symm_apply _ _
  intro hz
  have h := congrFun hz 0
  rw [href] at h
  exact one_ne_zero h

theorem scaled_basis_match (inverse : Bool) (r z r' z' : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (hplane' : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (c : Byte) (i : Fin 3)
    (hc : c = dualCoefficient inverse r z hplane marked hmarked hm i /
      dualCoefficient inverse r' z' hplane' marked hmarked hm' i) :
    (dualParam inverse r z hplane marked hmarked hm 1).val i =
      (dualScale inverse r' z' marked c (dualParam inverse r' z' hplane' marked hmarked hm' 1)).val i := by
  change dualCoefficient inverse r z hplane marked hmarked hm i =
    c * dualCoefficient inverse r' z' hplane' marked hmarked hm' i
  rw [hc]
  field_simp [dualCoefficient_ne_zero inverse r' z' hplane' marked hmarked hm' i]

theorem plane_ratios_nonconstant (inverse : Bool) (r z r' z' : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (hplane' : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') ≤ 1) :
    ¬ (dualCoefficient inverse r z hplane marked hmarked hm 0 /
          dualCoefficient inverse r' z' hplane' marked hmarked hm' 0 =
        dualCoefficient inverse r z hplane marked hmarked hm 1 /
          dualCoefficient inverse r' z' hplane' marked hmarked hm' 1 ∧
      dualCoefficient inverse r z hplane marked hmarked hm 1 /
          dualCoefficient inverse r' z' hplane' marked hmarked hm' 1 =
        dualCoefficient inverse r z hplane marked hmarked hm 2 /
          dualCoefficient inverse r' z' hplane' marked hmarked hm' 2) := by
  intro hr
  let c := dualCoefficient inverse r z hplane marked hmarked hm 0 /
    dualCoefficient inverse r' z' hplane' marked hmarked hm' 0
  let u := dualParam inverse r z hplane marked hmarked hm 1
  let v := dualScale inverse r' z' marked c (dualParam inverse r' z' hplane' marked hmarked hm' 1)
  have hc (i : Fin 3) : c = dualCoefficient inverse r z hplane marked hmarked hm i /
      dualCoefficient inverse r' z' hplane' marked hmarked hm' i := by
    fin_cases i
    · rfl
    · exact hr.1
    · exact hr.1.trans hr.2
  have huv : u.val = v.val := by
    funext i
    exact scaled_basis_match inverse r z r' z' hplane hplane' marked hmarked hm hm' c i (hc i)
  have hq : u.val ∈ dualPlane inverse r' z' marked := by rw [huv]; exact v.property
  exact dualBasis_nonzero inverse r z hplane marked hmarked hm
    (common_dual_zero inverse r z r' z' hplane hplane' marked hmarked hm hcommon u.val u.property hq)

private theorem union_inter_size : ∀ r s : Fin 16,
    maskSize (maskUnion r s) + maskSize (maskIntersection r s) = maskSize r + maskSize s := by decide

private theorem third_coordinate : ∀ i j : Fin 3, i ≠ j →
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ ∀ l : Fin 3, l ≠ k → l = i ∨ l = j := by decide

theorem union_point_mem_left (inverse : Bool) (r z r' z' : Fin 16)
    (marked : Fin 3 → GraphPosition)
    (x : ShortenedGraph (byteDiffusionHom inverse) (maskUnion r r') (maskUnion z z')) :
    (fun i => graphCoordinate (byteDiffusionHom inverse) x.val (marked i)) ∈ plane inverse r z marked := by
  have hx : graphZeroConditions (byteDiffusionHom inverse) r z x.val := by
    constructor
    · intro i hi
      exact x.property.1 i (by rw [maskUnion_bit,Bool.or_eq_true]; exact Or.inl hi)
    · intro i hi
      exact x.property.2 i (by rw [maskUnion_bit,Bool.or_eq_true]; exact Or.inl hi)
  exact ⟨⟨x.val,hx⟩,rfl⟩

theorem union_point_mem_right (inverse : Bool) (r z r' z' : Fin 16)
    (marked : Fin 3 → GraphPosition)
    (x : ShortenedGraph (byteDiffusionHom inverse) (maskUnion r r') (maskUnion z z')) :
    (fun i => graphCoordinate (byteDiffusionHom inverse) x.val (marked i)) ∈ plane inverse r' z' marked := by
  have hx : graphZeroConditions (byteDiffusionHom inverse) r' z' x.val := by
    constructor
    · intro i hi
      exact x.property.1 i (by rw [maskUnion_bit,Bool.or_eq_true]; exact Or.inr hi)
    · intro i hi
      exact x.property.2 i (by rw [maskUnion_bit,Bool.or_eq_true]; exact Or.inr hi)
  exact ⟨⟨x.val,hx⟩,rfl⟩

theorem plane_ratios_injective (inverse : Bool) (r z r' z' : Fin 16)
    (hplane : maskSize r + maskSize z = 2) (hplane' : maskSize r' + maskSize z' = 2)
    (marked : Fin 3 → GraphPosition) (hmarked : Function.Injective marked)
    (hm : ∀ i, remaining r z (marked i)) (hm' : ∀ i, remaining r' z' (marked i))
    (hcommon : maskSize (maskIntersection r r') + maskSize (maskIntersection z z') = 1) :
    Function.Injective (fun i => dualCoefficient inverse r z hplane marked hmarked hm i /
      dualCoefficient inverse r' z' hplane' marked hmarked hm' i) := by
  intro i j hij
  by_contra hne
  obtain ⟨k,hki,hkj,hthird⟩ := third_coordinate i j hne
  let c := dualCoefficient inverse r z hplane marked hmarked hm i /
    dualCoefficient inverse r' z' hplane' marked hmarked hm' i
  let u := dualParam inverse r z hplane marked hmarked hm 1
  let v := dualScale inverse r' z' marked c (dualParam inverse r' z' hplane' marked hmarked hm' 1)
  let h : Fin 3 → Byte := u.val-v.val
  have hi : u.val i = v.val i := scaled_basis_match inverse r z r' z' hplane hplane' marked hmarked hm hm' c i rfl
  have hj : u.val j = v.val j := scaled_basis_match inverse r z r' z' hplane hplane' marked hmarked hm hm' c j hij
  have hsupp (l : Fin 3) (hl : l ≠ k) : h l = 0 := by
    rcases hthird l hl with hli | hlj
    · subst l; exact sub_eq_zero.mpr hi
    · subst l; exact sub_eq_zero.mpr hj
  have hshort : maskSize (maskUnion r r') + maskSize (maskUnion z z') = 3 := by
    have h1 := union_inter_size r r'
    have h2 := union_inter_size z z'
    omega
  have hpair (x : ShortenedGraph (byteDiffusionHom inverse) (maskUnion r r') (maskUnion z z')) :
      (bytePairing.product (Fin 3)).value h
        (fun l => graphCoordinate (byteDiffusionHom inverse) x.val (marked l)) = 1 := by
    let y := fun l => graphCoordinate (byteDiffusionHom inverse) x.val (marked l)
    have hu : (bytePairing.product (Fin 3)).value u.val y = 1 :=
      u.property ⟨y,union_point_mem_left inverse r z r' z' marked x⟩
    have hv : (bytePairing.product (Fin 3)).value v.val y = 1 :=
      v.property ⟨y,union_point_mem_right inverse r z r' z' marked x⟩
    have hh := (bytePairing.product (Fin 3)).add_left h v.val y
    have hsum : h+v.val=u.val := sub_add_cancel _ _
    rw [hsum,hu,hv,_root_.mul_one] at hh
    exact hh.symm
  have hkzero : h k = 0 := by
    by_contra hk
    obtain ⟨value,hvalue⟩ := bytePairing.nondegenerate (h k) hk
    obtain ⟨x,hx⟩ := (coordinateEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
      (maskUnion r r') (maskUnion z z') hshort (marked k)
      (remaining_union r z r' z' (marked k) (hm k) (hm' k))).surjective value
    change graphCoordinate (byteDiffusionHom inverse) x.val (marked k) = value at hx
    have he := hpair x
    change (∏ l : Fin 3, bytePairing.value (h l)
      (graphCoordinate (byteDiffusionHom inverse) x.val (marked l))) = 1 at he
    rw [Finset.prod_eq_single k] at he
    · rw [hx] at he
      exact hvalue he
    · intro l _ hl
      rw [hsupp l hl,CharacterPairing.zero_left]
    · simp
  have hzero : h = 0 := by
    funext l
    by_cases hl : l=k
    · subst l; exact hkzero
    · exact hsupp l hl
  have huv : u.val=v.val := sub_eq_zero.mp hzero
  have hq : u.val ∈ dualPlane inverse r' z' marked := by rw [huv]; exact v.property
  exact dualBasis_nonzero inverse r z hplane marked hmarked hm
    (common_dual_zero inverse r z r' z' hplane hplane' marked hmarked hm (by omega) u.val u.property hq)

end AESConcrete.MixedMarkedPlaneGeometry
