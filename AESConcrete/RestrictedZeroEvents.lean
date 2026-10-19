import AESConcrete.ActualRestrictedDensity
import AESConcrete.RestrictedMDSCoordinates
import AESMixing.Finite

/-!
# Mass bounds for unnormalized restricted zero events

Two different input information sets of the same shortened source give a
Cauchy--Schwarz mass bound. Actual product-law collisions and point caps
then instantiate the high-zero cases. The source is never conditioned or
renormalized. Output-event identification and the complete activity table
remain separate caller obligations. Constructive mathematics only; no
attacks, manuscript changes or historical-source edits.
-/

noncomputable section
open scoped BigOperators
set_option maxRecDepth 100000

namespace AESConcrete.RestrictedZeroEvents
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordColumnGram (Byte Word inputColumn inputColumn_nonneg)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.RestrictedMDSCoordinates (actualInputEquiv)
open AESConcrete.ActualRestrictedDensity (inputLaw restrictedSource)

section GenericMass
variable {C X Y : Type*} [Fintype C] [Fintype X] [Fintype Y]

/-- The same source can be parametrized by different information sets.
The densities may be signed; the conclusion is an upper bound on mass. -/
theorem paired_mass_le (e : C ≃ X) (f : C ≃ Y) (a : X → ℝ) (b : Y → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (ha : (∑ x : X, a x ^ 2) ≤ R) (hb : (∑ y : Y, b y ^ 2) ≤ R) :
    (∑ c : C, a (e c) * b (f c)) ≤ R := by
  have ha' : (∑ c : C, a (e c) ^ 2) ≤ R := by
    rw [e.sum_comp (fun x => a x ^ 2)]
    exact ha
  have hb' : (∑ c : C, b (f c) ^ 2) ≤ R := by
    rw [f.sum_comp (fun y => b y ^ 2)]
    exact hb
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun c : C => a (e c)) (fun c : C => b (f c))
  have hp : (∑ c : C, a (e c) ^ 2) * (∑ c : C, b (f c) ^ 2) ≤ R ^ 2 := by
    have h := mul_le_mul ha' hb'
      (Finset.sum_nonneg (fun c _ => sq_nonneg (b (f c)))) hR
    nlinarith
  have habs : |∑ c : C, a (e c) * b (f c)| ≤ R :=
    (sq_le_sq₀ (abs_nonneg _) hR).mp (by
      simpa only [sq_abs] using hcs.trans hp)
  exact (le_abs_self _).trans habs

theorem dominated_paired_mass_le (e : C ≃ X) (f : C ≃ Y)
    (a : X → ℝ) (b : Y → ℝ) (g : C → ℝ) (scale R : ℝ)
    (hscale : 0 ≤ scale) (hR : 0 ≤ R)
    (ha : (∑ x : X, a x ^ 2) ≤ R) (hb : (∑ y : Y, b y ^ 2) ≤ R)
    (hdom : ∀ c, g c ≤ scale * a (e c) * b (f c)) :
    (∑ c : C, g c) ≤ scale * R := by
  calc
    _ ≤ ∑ c : C, scale * a (e c) * b (f c) :=
      Finset.sum_le_sum (fun c _ => hdom c)
    _ = scale * ∑ c : C, a (e c) * b (f c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (paired_mass_le e f a b R hR ha hb) hscale

end GenericMass

/-- Sectionwise Cauchy--Schwarz retains normalized conditioning weights,
without normalizing the restricted source itself. -/
theorem section_paired_mass_le {C S U Y : Type*}
    [Fintype C] [Fintype S] [Fintype U] [Fintype Y]
    (e : C ≃ S × U) (f : C ≃ S × Y)
    (hfirst : ∀ c, (f c).1 = (e c).1)
    (lambda : S → ℝ) (a : U → ℝ) (b : Y → ℝ) (g : C → ℝ) (R : ℝ)
    (hlambda : ∀ s, 0 ≤ lambda s) (hmass : (∑ s : S, lambda s) = 1)
    (hR : 0 ≤ R) (ha : (∑ u : U, a u ^ 2) ≤ R) (hb : (∑ y : Y, b y ^ 2) ≤ R)
    (hdom : ∀ c, g c ≤ lambda (e c).1 * a (e c).2 * b (f c).2) :
    (∑ c : C, g c) ≤ R := by
  let E : S → U ≃ Y := fun s => Equiv.ofBijective
    (fun u => (f (e.symm (s, u))).2)
    (RestrictedMDSCoordinates.section_bijective e f hfirst s)
  have hs (s : S) : (∑ u : U, a u * b ((f (e.symm (s, u))).2)) ≤ R :=
    paired_mass_le (Equiv.refl U) (E s) a b R hR ha hb
  calc
    _ = ∑ p : S × U, g (e.symm p) := (e.symm.sum_comp g).symm
    _ = ∑ s : S, ∑ u : U, g (e.symm (s, u)) := Fintype.sum_prod_type _
    _ ≤ ∑ s : S, lambda s * ∑ u : U, a u * b ((f (e.symm (s, u))).2) := by
      apply Finset.sum_le_sum
      intro s _
      calc
        _ ≤ ∑ u : U, lambda s * a u * b ((f (e.symm (s, u))).2) := by
          apply Finset.sum_le_sum
          intro u _
          simpa only [Equiv.apply_symm_apply] using hdom (e.symm (s, u))
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _
          ring
    _ ≤ ∑ s : S, lambda s * R := Finset.sum_le_sum (fun s _ =>
      mul_le_mul_of_nonneg_left (hs s) (hlambda s))
    _ = R := by rw [← Finset.sum_mul, hmass, one_mul]

private theorem disjoint_union_left (z u v : Fin 16)
    (h : MaskDisjoint z (maskUnion u v)) : MaskDisjoint z u := by
  intro i hz hu
  apply h i hz
  rw [maskUnion_bit, Bool.or_eq_true]
  exact Or.inl hu

private theorem disjoint_union_right (z u v : Fin 16)
    (h : MaskDisjoint z (maskUnion u v)) : MaskDisjoint z v := by
  intro i hz hv
  apply h i hz
  rw [maskUnion_bit, Bool.or_eq_true]
  exact Or.inr hv

/-- Unlike the response-energy parametrization, two complete information
sets may use more input coordinates than the shortened dimension. `aux`
counts exactly the remaining active probability factors. -/
theorem paired_source_domination (right : Orientation) (inverse : Bool) (a : Word)
    (r z aux u v : Fin 16) (huv : MaskDisjoint u v)
    (hzu : MaskDisjoint z (maskUnion u v))
    (hpart : maskSize aux + maskSize z + maskSize u + maskSize v = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event]
    (c : ShortenedGraph (byteDiffusionHom inverse) r z) :
    restrictedSource right inverse a r z event c ≤ (1 / 64 : ℝ) ^ maskSize aux *
      inputLaw right a u (fun i => c.val i.val) *
      inputLaw right a v (fun i => c.val i.val) := by
  have hevent : restrictedSource right inverse a r z event c ≤ inputColumn right a c.val := by
    unfold restrictedSource
    split_ifs
    · exact le_rfl
    · exact inputColumn_nonneg right a c.val
  apply hevent.trans
  apply ActualRestrictedDensity.product_partition_bound aux z u v huv hzu hpart
    (fun i => channel right (c.val i) (a i)) (1 / 64)
    (fun i => (channel_resources right).nonnegative _ _)
  · intro i hi
    rw [c.property.2 i hi, (ha i).mpr hi, (channel_resources right).zero_column]
    norm_num
  · intro i hi
    apply (channel_resources right).atom
    intro hzero
    exact hi ((ha i).mp hzero)

/-- Actual input laws, actual MDS input information sets and actual byte
point/collision constants discharge every analytic mass premise. -/
theorem actual_paired_restricted_mass_le
    (right : Orientation) (inverse : Bool) (a : Word)
    (r z aux u v : Fin 16) (huv : MaskDisjoint u v)
    (hzu : MaskDisjoint z (maskUnion u v))
    (hpart : maskSize aux + maskSize z + maskSize u + maskSize v = 4)
    (hinfo_u : maskSize r + maskSize z + maskSize u = 4)
    (hinfo_v : maskSize r + maskSize z + maskSize v = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ c, restrictedSource right inverse a r z event c) ≤
      (1 / 64 : ℝ) ^ maskSize aux * (65 / 8192 : ℝ) ^ maskSize u := by
  have hzu' := disjoint_union_left z u v hzu
  have hzv' := disjoint_union_right z u v hzu
  have hsame : maskSize u = maskSize v := by omega
  let e := actualInputEquiv inverse r z u hzu' hinfo_u
  let f := actualInputEquiv inverse r z v hzv' hinfo_v
  apply dominated_paired_mass_le e f (inputLaw right a u) (inputLaw right a v)
    (restrictedSource right inverse a r z event)
    ((1 / 64 : ℝ) ^ maskSize aux) ((65 / 8192 : ℝ) ^ maskSize u)
    (by positivity) (by positivity)
  · exact (ActualRestrictedDensity.inputLaw_energy right a z u ha hzu').le
  · rw [hsame]
    exact (ActualRestrictedDensity.inputLaw_energy right a z v ha hzv').le
  · intro c
    exact paired_source_domination right inverse a r z aux u v huv hzu hpart ha event c

/-- Enough prescribed zeros force the only shortened graph point to zero;
every actual nonzero-input source has zero density there. -/
theorem actual_restricted_mass_zero (right : Orientation) (inverse : Bool) (a : Word)
    (ha : a ≠ 0) (r z : Fin 16) (hhigh : 4 ≤ maskSize r + maskSize z)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ c, restrictedSource right inverse a r z event c) = 0 := by
  have hactive : ∃ i : Fin 4, a i ≠ 0 := by
    by_contra h
    push_neg at h
    apply ha
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hactive
  apply Finset.sum_eq_zero
  intro c _
  unfold restrictedSource
  split_ifs
  · have hc := mds_graph_zero_high (byteDiffusionHom inverse)
      (byteDiffusionHom_zeroMDS inverse) r z hhigh c.val c.property
    rw [hc]
    exact WordColumnGram.inputColumn_zero_of_active right a 0 i hi rfl
  · rfl

private theorem singleton_pair_masks : ∀ z : Fin 16, maskSize z ≤ 2 →
    ∃ u v : Fin 16, MaskDisjoint u v ∧ MaskDisjoint z (maskUnion u v) ∧
      maskSize u = 1 ∧ maskSize v = 1 := by decide

private theorem double_pair_masks : ∀ z : Fin 16, maskSize z = 0 →
    ∃ u v : Fin 16, MaskDisjoint u v ∧ MaskDisjoint z (maskUnion u v) ∧
      maskSize u = 2 ∧ maskSize v = 2 := by decide

/-- Two active inputs and one prescribed output zero. -/
theorem actual_two_active_one_zero_mass_le
    (right : Orientation) (inverse : Bool) (a : Word) (r z : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z = 2)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ c, restrictedSource right inverse a r z event c) ≤ (65 / 8192 : ℝ) := by
  obtain ⟨u, v, huv, hzu, hu, hv⟩ := singleton_pair_masks z (by omega)
  have haux : maskSize (0 : Fin 16) = 0 := by decide
  have h := actual_paired_restricted_mass_le right inverse a r z 0 u v huv hzu
    (by omega) (by omega) (by omega) ha event
  simpa only [haux, hu, pow_zero, pow_one, one_mul] using h

/-- Three active inputs and two prescribed output zeros. -/
theorem actual_three_active_two_zero_mass_le
    (right : Orientation) (inverse : Bool) (a : Word) (r z : Fin 16)
    (hr : maskSize r = 2) (hz : maskSize z = 1)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ c, restrictedSource right inverse a r z event c) ≤
      (1 / 64 : ℝ) * (65 / 8192 : ℝ) := by
  obtain ⟨u, v, huv, hzu, hu, hv⟩ := singleton_pair_masks z (by omega)
  have haux : maskSize (1 : Fin 16) = 1 := by decide
  have h := actual_paired_restricted_mass_le right inverse a r z 1 u v huv hzu
    (by omega) (by omega) (by omega) ha event
  simpa only [haux, hu, pow_one] using h

/-- Four active inputs and two prescribed output zeros. -/
theorem actual_four_active_two_zero_mass_le
    (right : Orientation) (inverse : Bool) (a : Word) (r z : Fin 16)
    (hr : maskSize r = 2) (hz : maskSize z = 0)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ c, restrictedSource right inverse a r z event c) ≤ (65 / 8192 : ℝ) ^ 2 := by
  obtain ⟨u, v, huv, hzu, hu, hv⟩ := double_pair_masks z hz
  have haux : maskSize (0 : Fin 16) = 0 := by decide
  have h := actual_paired_restricted_mass_le right inverse a r z 0 u v huv hzu
    (by omega) (by omega) (by omega) ha event
  simpa only [haux, hu, pow_zero, one_mul] using h

/-- Four active inputs and three prescribed output zeros. -/
theorem actual_four_active_three_zero_mass_le
    (right : Orientation) (inverse : Bool) (a : Word) (r z : Fin 16)
    (hr : maskSize r = 3) (hz : maskSize z = 0)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ c, restrictedSource right inverse a r z event c) ≤
      (1 / 64 : ℝ) ^ 2 * (65 / 8192 : ℝ) := by
  obtain ⟨u, v, huv, hzu, hu, hv⟩ := singleton_pair_masks z (by omega)
  have haux : maskSize (3 : Fin 16) = 2 := by decide
  have h := actual_paired_restricted_mass_le right inverse a r z 3 u v huv hzu
    (by omega) (by omega) (by omega) ha event
  simpa only [haux, hu, pow_one] using h

private theorem disjoint_union (z u v : Fin 16)
    (hzu : MaskDisjoint z u) (hzv : MaskDisjoint z v) :
    MaskDisjoint z (maskUnion u v) := by
  intro i hz huv
  rw [maskUnion_bit, Bool.or_eq_true] at huv
  rcases huv with hu | hv
  · exact hzu i hz hu
  · exact hzv i hz hv

theorem inputLaw_union_values (right : Orientation) (a : Word) (u v : Fin 16)
    (huv : MaskDisjoint u v) (x : Word) :
    inputLaw right a (maskUnion u v) (fun i => x i.val) =
      inputLaw right a u (fun i => x i.val) * inputLaw right a v (fun i => x i.val) := by
  let F : Fin 4 → ℝ := fun i => channel right (x i) (a i)
  change (∏ i : MaskCoordinates (maskUnion u v), F i.val) =
    (∏ i : MaskCoordinates u, F i.val) * (∏ i : MaskCoordinates v, F i.val)
  rw [← ActualRestrictedDensity.masked_product_eq (maskUnion u v) F,
    ← ActualRestrictedDensity.masked_product_eq u F,
    ← ActualRestrictedDensity.masked_product_eq v F, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hbit : maskBit (maskUnion u v) i = true ↔
      maskBit u i = true ∨ maskBit v i = true := by
    rw [maskUnion_bit, Bool.or_eq_true]
  by_cases hu : maskBit u i = true
  · have hv := huv i hu
    simp [hbit, hu, hv]
  · by_cases hv : maskBit v i = true <;> simp [hbit, hu, hv]

/-- Three groups cover every active input. The remaining group is a
normalized conditioning law, rather than a collection paid by point caps. -/
theorem three_group_source_domination
    (right : Orientation) (inverse : Bool) (a : Word) (r z s u v : Fin 16)
    (hsu : MaskDisjoint s u) (hsv : MaskDisjoint s v) (huv : MaskDisjoint u v)
    (hzall : MaskDisjoint z (maskUnion s (maskUnion u v)))
    (hpart : maskSize z + maskSize s + maskSize u + maskSize v = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event]
    (c : ShortenedGraph (byteDiffusionHom inverse) r z) :
    restrictedSource right inverse a r z event c ≤
      inputLaw right a s (fun i => c.val i.val) *
        inputLaw right a u (fun i => c.val i.val) *
          inputLaw right a v (fun i => c.val i.val) := by
  have hsize : maskSize (0 : Fin 16) + maskSize z + maskSize s +
      maskSize (maskUnion u v) = 4 := by
    rw [show maskSize (0 : Fin 16) = 0 by decide, maskUnion_size u v huv]
    omega
  have h := paired_source_domination right inverse a r z 0 s (maskUnion u v)
    (disjoint_union s u v hsu hsv) hzall hsize ha event c
  rw [inputLaw_union_values right a u v huv c.val] at h
  simpa only [show maskSize (0 : Fin 16) = 0 by decide, pow_zero, one_mul,
    mul_assoc] using h

theorem actual_section_restricted_mass_le
    (right : Orientation) (inverse : Bool) (a : Word) (r z s u v : Fin 16)
    (hsu : MaskDisjoint s u) (hsv : MaskDisjoint s v) (huv : MaskDisjoint u v)
    (hzall : MaskDisjoint z (maskUnion s (maskUnion u v)))
    (hpart : maskSize z + maskSize s + maskSize u + maskSize v = 4)
    (hinfo_u : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hinfo_v : maskSize r + maskSize z + maskSize s + maskSize v = 4)
    (hu : maskSize u = 1) (hv : maskSize v = 1)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ c, restrictedSource right inverse a r z event c) ≤ (65 / 8192 : ℝ) := by
  have hzs := disjoint_union_left z s (maskUnion u v) hzall
  have hzuv := disjoint_union_right z s (maskUnion u v) hzall
  have hzu := disjoint_union_left z u v hzuv
  have hzv := disjoint_union_right z u v hzuv
  let e := RestrictedMDSCoordinates.inputSplitEquiv
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) r z s u hsu
    (disjoint_union z s u hzs hzu) hinfo_u
  let f := RestrictedMDSCoordinates.inputSplitEquiv
    (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse) r z s v hsv
    (disjoint_union z s v hzs hzv) hinfo_v
  apply section_paired_mass_le e f (fun _ => rfl)
    (inputLaw right a s) (inputLaw right a u) (inputLaw right a v)
    (restrictedSource right inverse a r z event) (65 / 8192)
    (ActualRestrictedDensity.inputLaw_nonneg right a s)
    (ActualRestrictedDensity.inputLaw_mass right a s) (by norm_num)
  · have h := ActualRestrictedDensity.inputLaw_energy right a z u ha hzu
    rw [hu, pow_one] at h
    exact h.le
  · have h := ActualRestrictedDensity.inputLaw_energy right a z v ha hzv
    rw [hv, pow_one] at h
    exact h.le
  · intro c
    exact three_group_source_domination right inverse a r z s u v
      hsu hsv huv hzall hpart ha event c

private theorem mask_size_bound : ∀ z : Fin 16, maskSize z ≤ 4 := by decide

/-- Every actual one-zero row with at least two active input bytes. -/
theorem actual_one_zero_mass_le
    (right : Orientation) (inverse : Bool) (a : Word) (r z : Fin 16)
    (hr : maskSize r = 1) (hz : maskSize z ≤ 2)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ c, restrictedSource right inverse a r z event c) ≤ (65 / 8192 : ℝ) := by
  obtain ⟨u, v, huv, hzuv, hu, hv⟩ := singleton_pair_masks z hz
  let s := ActualRestrictedDensity.omittedMask z u v
  have hsbit (i : Fin 4) (hi : maskBit s i = true) :
      maskBit z i ≠ true ∧ maskBit u i ≠ true ∧ maskBit v i ≠ true :=
    (ActualRestrictedDensity.omittedMask_bit z u v i).mp hi
  have hsu : MaskDisjoint s u := fun i hs hi => (hsbit i hs).2.1 hi
  have hsv : MaskDisjoint s v := fun i hs hi => (hsbit i hs).2.2 hi
  have hzs : MaskDisjoint z s := fun i hi hs => (hsbit i hs).1 hi
  have hzall := disjoint_union z s (maskUnion u v) hzs hzuv
  have htotal : maskSize z + maskSize s + maskSize u + maskSize v = 4 := by
    have hc := maskComplement_size (maskUnion z (maskUnion u v))
    change maskSize s = 4 - maskSize (maskUnion z (maskUnion u v)) at hc
    have hb := mask_size_bound (maskUnion z (maskUnion u v))
    rw [maskUnion_size z (maskUnion u v) hzuv, maskUnion_size u v huv] at hc hb
    omega
  exact actual_section_restricted_mass_le right inverse a r z s u v
    hsu hsv huv hzall htotal (by omega) (by omega) hu hv ha event

end AESConcrete.RestrictedZeroEvents
