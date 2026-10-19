import AESConcrete.ShortenedPlaneLinearity
import AESMixing.MDSPrescribedCount

/-!
# Actual shortened-plane dual ratio geometry

Prescribed-coordinate existence for the physical MDS graph supplies an
actual decomposition into two distinct two-zero shortenings. Their marked
planes sum to the full marked triple, so their actual annihilator lines
have no common nonzero point. With one common zero constraint, a repeated
dual ratio leaves a difference on only one marked coordinate; the actual
three-zero union shortening makes that remaining coordinate arbitrary.

Constructive proof support only. No slope table, assumed sum dimension,
generic Fourier algebra, mixed-pair bound, or final AES theorem is added.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ShortenedPlaneGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ShortenedLineResponse
open AESConcrete.ShortenedPlane
open AESConcrete.ShortenedPlaneLinearity

set_option maxRecDepth 65536

private theorem union_comm : ∀ r s : Fin 16, maskUnion r s = maskUnion s r := by decide
private theorem union_ge : ∀ r s : Fin 16, maskSize r ≤ maskSize (maskUnion r s) := by decide
private theorem union_eq_size : ∀ r s : Fin 16,
    maskSize (maskUnion r s) = maskSize r → maskUnion r s = r := by decide
private theorem union_inter_size : ∀ r s : Fin 16,
    maskSize (maskUnion r s) + maskSize (maskIntersection r s) = maskSize r + maskSize s := by decide

theorem plane_choice_union_high (out : Fin 16) (p q : ShorteningChoice out 2) (hpq : p ≠ q) :
    3 ≤ maskSize (maskUnion p.val.1 q.val.1) + maskSize (maskUnion p.val.2 q.val.2) := by
  have hp := p.property.2
  have hq := q.property.2
  have hp1 := union_ge p.val.1 q.val.1
  have hp2 := union_ge p.val.2 q.val.2
  have hq1 := union_ge q.val.1 p.val.1
  have hq2 := union_ge q.val.2 p.val.2
  rw [union_comm q.val.1 p.val.1] at hq1
  rw [union_comm q.val.2 p.val.2] at hq2
  by_contra hlow
  have he1 : maskSize (maskUnion p.val.1 q.val.1) = maskSize p.val.1 := by omega
  have he2 : maskSize (maskUnion p.val.2 q.val.2) = maskSize p.val.2 := by omega
  have he1' : maskSize (maskUnion q.val.1 p.val.1) = maskSize q.val.1 := by
    rw [union_comm q.val.1 p.val.1]
    omega
  have he2' : maskSize (maskUnion q.val.2 p.val.2) = maskSize q.val.2 := by
    rw [union_comm q.val.2 p.val.2]
    omega
  have h1 : p.val.1 = q.val.1 := by
    have ha := union_eq_size p.val.1 q.val.1 he1
    have hb := union_eq_size q.val.1 p.val.1 he1'
    rw [union_comm q.val.1 p.val.1] at hb
    exact ha.symm.trans hb
  have h2 : p.val.2 = q.val.2 := by
    have ha := union_eq_size p.val.2 q.val.2 he2
    have hb := union_eq_size q.val.2 p.val.2 he2'
    rw [union_comm q.val.2 p.val.2] at hb
    exact ha.symm.trans hb
  exact hpq (Subtype.ext (Prod.ext h1 h2))

theorem plane_choice_common_le_one (out : Fin 16)
    (p q : ShorteningChoice out 2) (hpq : p ≠ q) :
    maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) ≤ 1 := by
  have hu := plane_choice_union_high out p q hpq
  have h1 := union_inter_size p.val.1 q.val.1
  have h2 := union_inter_size p.val.2 q.val.2
  have hp := p.property.2
  have hq := q.property.2
  omega

theorem plane_choice_union_low (out : Fin 16) (p q : ShorteningChoice out 2) :
    maskSize (maskUnion p.val.1 q.val.1) + maskSize (maskUnion p.val.2 q.val.2) ≤ 4 := by
  have h1 := union_inter_size p.val.1 q.val.1
  have h2 := union_inter_size p.val.2 q.val.2
  have hp := p.property.2
  have hq := q.property.2
  omega

private theorem common_disjoint {out : Fin 16} (p q : ShorteningChoice out 2) :
    MaskDisjoint (maskIntersection p.val.1 q.val.1) out := by
  intro i hi ho
  simp only [maskIntersection_bit, Bool.and_eq_true] at hi
  exact p.property.1 i hi.1 ho

private theorem union_disjoint {out : Fin 16} (p q : ShorteningChoice out 2) :
    MaskDisjoint (maskUnion p.val.1 q.val.1) out := by
  intro i hi ho
  rw [maskUnion_bit, Bool.or_eq_true] at hi
  exact hi.elim (fun h => p.property.1 i h ho) (fun h => q.property.1 i h ho)

section Prescribed
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem prescribed_exists (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z : Fin 16) (hle : maskSize r + maskSize z ≤ 4) (u v : Fin 4 → V) :
    ∃ x, graphPrescribed L r z u v x := by
  have hc := mds_graph_prescribed_count_low L hL r z hle u v
  have hp : 0 < Fintype.card {x : Fin 4 → V // graphPrescribed L r z u v x} := by
    rw [hc]
    exact pow_pos Fintype.card_pos _
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hp
  exact ⟨x.val, x.property⟩

/-- A point satisfying the common zeros splits into actual points of
the two shortenings, using compatible prescriptions on their union. -/
theorem graph_decomposition (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (out : Fin 16) (p q : ShorteningChoice out 2) (x : Fin 4 → V)
    (hx : graphZeroConditions L (maskIntersection p.val.1 q.val.1)
      (maskIntersection p.val.2 q.val.2) x) :
    ∃ (xp : ShortenedGraph L p.val.1 p.val.2) (xq : ShortenedGraph L q.val.1 q.val.2),
      x = xp.val + xq.val := by
  obtain ⟨xp, hp⟩ := prescribed_exists L hL (maskUnion p.val.1 q.val.1)
    (maskUnion p.val.2 q.val.2) (plane_choice_union_low out p q)
    (fun i => if maskBit p.val.1 i = true then 0 else L x i)
    (fun i => if maskBit p.val.2 i = true then 0 else x i)
  have hxp : graphZeroConditions L p.val.1 p.val.2 xp := by
    constructor
    · intro i hi
      have h := hp.1 i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl hi)
      simpa only [if_pos hi] using h
    · intro i hi
      have h := hp.2 i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl hi)
      simpa only [if_pos hi] using h
  have hxq : graphZeroConditions L q.val.1 q.val.2 (x-xp) := by
    constructor
    · intro i hi
      rw [map_sub]
      change L x i - L xp i = 0
      have h := hp.1 i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inr hi)
      dsimp only at h
      by_cases hpi : maskBit p.val.1 i = true
      · rw [if_pos hpi] at h
        have hc : maskBit (maskIntersection p.val.1 q.val.1) i = true := by
          rw [maskIntersection_bit, Bool.and_eq_true]
          exact ⟨hpi, hi⟩
        rw [hx.1 i hc, h, sub_self]
      · rw [if_neg hpi] at h
        exact sub_eq_zero.mpr h.symm
    · intro i hi
      change x i - xp i = 0
      have h := hp.2 i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inr hi)
      dsimp only at h
      by_cases hpi : maskBit p.val.2 i = true
      · rw [if_pos hpi] at h
        have hc : maskBit (maskIntersection p.val.2 q.val.2) i = true := by
          rw [maskIntersection_bit, Bool.and_eq_true]
          exact ⟨hpi, hi⟩
        rw [hx.2 i hc, h, sub_self]
      · rw [if_neg hpi] at h
        exact sub_eq_zero.mpr h.symm
  refine ⟨⟨xp, hxp⟩, ⟨x-xp, hxq⟩, ?_⟩
  change x = xp + (x-xp)
  calc
    x = (x-xp)+xp := (sub_add_cancel x xp).symm
    _ = xp+(x-xp) := add_comm _ _

end Prescribed

/-- The sum of two distinct actual marked planes covers the marked space.
The proof uses prescribed-coordinate existence, not a dimension premise. -/
theorem actual_plane_sum_surjective (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p q : ShorteningChoice out 2) (hpq : p ≠ q)
    (y : Fin 3 → Byte) :
    ∃ (a : plane inverse e p) (b : plane inverse e q), y = a.val + b.val := by
  let r := maskIntersection p.val.1 q.val.1
  let z := maskIntersection p.val.2 q.val.2
  have hd : MaskDisjoint r out := common_disjoint p q
  have hlow : maskSize (maskUnion r out) + maskSize z ≤ 4 := by
    rw [maskUnion_size _ _ hd]
    have hc := plane_choice_common_le_one out p q hpq
    change maskSize r + maskSize z ≤ 1 at hc
    omega
  let target (i : Fin 4) : Byte :=
    if hi : maskBit out i = true then y (e.symm ⟨i, hi⟩) else 0
  obtain ⟨x, hx⟩ := prescribed_exists (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    (maskUnion r out) z hlow target (fun _ => 0)
  have hzeros : graphZeroConditions (byteDiffusionHom inverse) r z x := by
    constructor
    · intro i hi
      have ho : maskBit out i ≠ true := hd i hi
      have hh := hx.1 i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl hi)
      simpa only [target, dif_neg ho] using hh
    · exact hx.2
  have hmarked (i : Fin 3) : byteDiffusionHom inverse x (e i).val = y i := by
    have hh := hx.1 (e i).val (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inr (e i).property)
    have hsub : (⟨(e i).val, (e i).property⟩ : MaskCoordinates out) = e i := Subtype.ext rfl
    have he : e.symm (⟨(e i).val, (e i).property⟩ : MaskCoordinates out) = i := by
      rw [hsub, Equiv.symm_apply_apply]
    simpa only [target, dif_pos (e i).property, he] using hh
  obtain ⟨xp, xq, hsplit⟩ := graph_decomposition (byteDiffusionHom inverse)
    (byteDiffusionHom_zeroMDS inverse) out p q x hzeros
  let a : plane inverse e p :=
    ⟨projectionHom inverse p.val.1 p.val.2 e ⟨xp.val, xp.property⟩, ⟨⟨xp.val, xp.property⟩, rfl⟩⟩
  let b : plane inverse e q :=
    ⟨projectionHom inverse q.val.1 q.val.2 e ⟨xq.val, xq.property⟩, ⟨⟨xq.val, xq.property⟩, rfl⟩⟩
  refine ⟨a, b, ?_⟩
  funext i
  change y i = byteDiffusionHom inverse xp.val (e i).val + byteDiffusionHom inverse xq.val (e i).val
  rw [← hmarked i, hsplit, map_add]
  rfl

/-- Distinct actual plane shortenings have no common nonzero dual point. -/
theorem common_dual_zero (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p q : ShorteningChoice out 2) (hpq : p ≠ q)
    (w : Fin 3 → Byte) (hp : w ∈ dualPlane inverse e p) (hq : w ∈ dualPlane inverse e q) : w = 0 := by
  by_contra hw
  obtain ⟨y, hy⟩ := (bytePairing.product (Fin 3)).nondegenerate w hw
  obtain ⟨a, b, hab⟩ := actual_plane_sum_surjective inverse out hout e p q hpq y
  apply hy
  rw [hab, CharacterPairing.add_right, hp a, hq b, one_mul]

theorem dualBasis_nonzero (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p : ShorteningChoice out 2) :
    (dualParam inverse out hout e p 1).val ≠ 0 := by
  have href : (dualParam inverse out hout e p 1).val 0 = 1 := by
    change (dualCoordinateEquiv inverse out hout e p 0)
      ((dualCoordinateEquiv inverse out hout e p 0).symm 1) = 1
    exact Equiv.apply_symm_apply _ _
  intro hzero
  have h := congrFun hzero 0
  rw [href] at h
  exact one_ne_zero h

private theorem scaled_basis_match (inverse : Bool) (out : Fin 16) (hout : maskSize out = 3)
    (e : Fin 3 ≃ MaskCoordinates out) (p q : ShorteningChoice out 2) (c : Byte) (i : Fin 3)
    (hc : c = dualCoefficient inverse out hout e p i / dualCoefficient inverse out hout e q i) :
    (dualParam inverse out hout e p 1).val i =
      (dualScale inverse e q c (dualParam inverse out hout e q 1)).val i := by
  change dualCoordinatePerm inverse out hout e p i 1 =
    c * dualCoordinatePerm inverse out hout e q i 1
  change dualCoefficient inverse out hout e p i = c * dualCoefficient inverse out hout e q i
  rw [hc]
  field_simp [dualCoefficient_ne_zero inverse out hout e q i]

/-- Actual eta2 geometry for distinct two-zero plane choices. -/
theorem distinct_plane_ratios_nonconstant (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p q : ShorteningChoice out 2) (hpq : p ≠ q) :
    ¬ (dualCoefficient inverse out hout e p 0 / dualCoefficient inverse out hout e q 0 =
        dualCoefficient inverse out hout e p 1 / dualCoefficient inverse out hout e q 1 ∧
      dualCoefficient inverse out hout e p 1 / dualCoefficient inverse out hout e q 1 =
        dualCoefficient inverse out hout e p 2 / dualCoefficient inverse out hout e q 2) := by
  intro hr
  let c := dualCoefficient inverse out hout e p 0 / dualCoefficient inverse out hout e q 0
  let u := dualParam inverse out hout e p 1
  let v := dualScale inverse e q c (dualParam inverse out hout e q 1)
  have hc (i : Fin 3) : c = dualCoefficient inverse out hout e p i / dualCoefficient inverse out hout e q i := by
    fin_cases i
    · rfl
    · exact hr.1
    · exact hr.1.trans hr.2
  have huv : u.val = v.val := by
    funext i
    exact scaled_basis_match inverse out hout e p q c i (hc i)
  have hq : u.val ∈ dualPlane inverse e q := by rw [huv]; exact v.property
  exact dualBasis_nonzero inverse out hout e p
    (common_dual_zero inverse out hout e p q hpq u.val u.property hq)

private theorem third_coordinate : ∀ i j : Fin 3, i ≠ j →
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ ∀ l : Fin 3, l ≠ k → l = i ∨ l = j := by decide

private theorem union_point_mem (inverse : Bool) {out : Fin 16}
    (e : Fin 3 ≃ MaskCoordinates out) (p q : ShorteningChoice out 2)
    (x : ShortenedGraph (byteDiffusionHom inverse) (maskUnion p.val.1 q.val.1) (maskUnion p.val.2 q.val.2)) :
    (fun i => byteDiffusionHom inverse x.val (e i).val) ∈ plane inverse e p := by
  have hx : graphZeroConditions (byteDiffusionHom inverse) p.val.1 p.val.2 x.val := by
    constructor
    · intro i hi
      exact x.property.1 i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl hi)
    · intro i hi
      exact x.property.2 i (by rw [maskUnion_bit, Bool.or_eq_true]; exact Or.inl hi)
  exact ⟨⟨x.val, hx⟩, rfl⟩

/-- One common physical zero makes the actual dual slope ratios pairwise
distinct, supplying the eta1 geometric premise for the Fourier-input lines. -/
theorem one_common_zero_ratios_injective (inverse : Bool) (out : Fin 16)
    (hout : maskSize out = 3) (e : Fin 3 ≃ MaskCoordinates out)
    (p q : ShorteningChoice out 2) (hpq : p ≠ q)
    (hcommon : maskSize (maskIntersection p.val.1 q.val.1) +
      maskSize (maskIntersection p.val.2 q.val.2) = 1) :
    Function.Injective (fun i => dualCoefficient inverse out hout e p i / dualCoefficient inverse out hout e q i) := by
  intro i j hij
  by_contra hne
  obtain ⟨k, hki, hkj, hthird⟩ := third_coordinate i j hne
  let c := dualCoefficient inverse out hout e p i / dualCoefficient inverse out hout e q i
  let u := dualParam inverse out hout e p 1
  let v := dualScale inverse e q c (dualParam inverse out hout e q 1)
  let h : Fin 3 → Byte := u.val - v.val
  have hi : u.val i = v.val i := scaled_basis_match inverse out hout e p q c i rfl
  have hj : u.val j = v.val j := scaled_basis_match inverse out hout e p q c j hij
  have hsupp (l : Fin 3) (hl : l ≠ k) : h l = 0 := by
    rcases hthird l hl with hli | hlj
    · subst l; exact sub_eq_zero.mpr hi
    · subst l; exact sub_eq_zero.mpr hj
  have hshort : maskSize (maskUnion p.val.1 q.val.1) + maskSize (maskUnion p.val.2 q.val.2) = 3 := by
    have h1 := union_inter_size p.val.1 q.val.1
    have h2 := union_inter_size p.val.2 q.val.2
    have hp := p.property.2
    have hq := q.property.2
    omega
  have hpair (x : ShortenedGraph (byteDiffusionHom inverse)
      (maskUnion p.val.1 q.val.1) (maskUnion p.val.2 q.val.2)) :
      (bytePairing.product (Fin 3)).value h (fun l => byteDiffusionHom inverse x.val (e l).val) = 1 := by
    let y := fun l => byteDiffusionHom inverse x.val (e l).val
    have hmp : y ∈ plane inverse e p := union_point_mem inverse e p q x
    have hmq : y ∈ plane inverse e q := by
      let xs : ShortenedGraph (byteDiffusionHom inverse) (maskUnion q.val.1 p.val.1)
          (maskUnion q.val.2 p.val.2) := ⟨x.val, by simpa only [union_comm] using x.property⟩
      exact union_point_mem inverse e q p xs
    have hu : (bytePairing.product (Fin 3)).value u.val y = 1 := u.property ⟨y, hmp⟩
    have hv : (bytePairing.product (Fin 3)).value v.val y = 1 := v.property ⟨y, hmq⟩
    have hh := (bytePairing.product (Fin 3)).add_left h v.val y
    have hsum : h + v.val = u.val := sub_add_cancel _ _
    rw [hsum, hu, hv, mul_one] at hh
    exact hh.symm
  have hkzero : h k = 0 := by
    by_contra hk
    obtain ⟨z, hz⟩ := bytePairing.nondegenerate (h k) hk
    have hr : maskBit (maskUnion p.val.1 q.val.1) (e k).val ≠ true :=
      fun hh => union_disjoint p q (e k).val hh (e k).property
    obtain ⟨x, hx⟩ := (output_coordinate_bijective (byteDiffusionHom inverse)
      (byteDiffusionHom_zeroMDS inverse) (maskUnion p.val.1 q.val.1)
      (maskUnion p.val.2 q.val.2) hshort (e k).val hr).2 z
    change byteDiffusionHom inverse x.val (e k).val = z at hx
    have he := hpair x
    change (∏ l : Fin 3, bytePairing.value (h l) (byteDiffusionHom inverse x.val (e l).val)) = 1 at he
    rw [Finset.prod_eq_single k] at he
    · rw [hx] at he
      exact hz he
    · intro l _ hl
      rw [hsupp l hl, CharacterPairing.zero_left]
    · simp
  have hzero : h = 0 := by
    funext l
    by_cases hl : l = k
    · subst l; exact hkzero
    · exact hsupp l hl
  have huv : u.val = v.val := sub_eq_zero.mp hzero
  have hq : u.val ∈ dualPlane inverse e q := by rw [huv]; exact v.property
  exact dualBasis_nonzero inverse out hout e p
    (common_dual_zero inverse out hout e p q hpq u.val u.property hq)

end AESConcrete.ShortenedPlaneGeometry
