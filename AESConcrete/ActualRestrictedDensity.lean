import AESConcrete.WordColumnGram
import AESConcrete.RestrictedMDSCoordinates
import AESConcrete.RestrictedProductDensity
import AESConcrete.RestrictedMarginalEnergy

/-!
# Actual AES source densities on shortened MDS graphs

The output-zero mask is r, the input-zero mask is z, and s,u are
disjoint free input sets. The active factors omitted from those free sets
number exactly |r|. The actual first-substitution density is bounded by
their byte-channel point caps, with every event restriction retained.
Product collision and the actual MDS section bijections then supply source
and fewer-output marginal energies before any signed residual channel.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.ActualRestrictedDensity
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordColumnGram (Byte Word inputColumn inputColumn_nonneg)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_zeroMDS)
open AESConcrete.RestrictedMDSCoordinates (inputSplitEquiv actual_output_section_bijective)
open AESConcrete.RestrictedProductDensity (productDensity)

/-- Physical input factors on one marked set. -/
def inputLaw (right : Orientation) (a : Word) (m : Fin 16)
    (x : MaskCoordinates m → Byte) : ℝ :=
  productDensity (fun i v => channel right v (a i.val)) x

theorem inputLaw_nonneg (right : Orientation) (a : Word) (m : Fin 16)
    (x : MaskCoordinates m → Byte) : 0 ≤ inputLaw right a m x := by
  exact RestrictedProductDensity.productDensity_nonneg _
    (fun _ _ => (channel_resources right).nonnegative _ _) x

theorem inputLaw_mass (right : Orientation) (a : Word) (m : Fin 16) :
    (∑ x : MaskCoordinates m → Byte, inputLaw right a m x) = 1 := by
  exact RestrictedProductDensity.productDensity_mass_one _
    (fun _ => (channel_resources right).column_sum _)

/-- Only active input positions contribute the nonzero-byte collision. -/
theorem inputLaw_energy (right : Orientation) (a : Word) (z m : Fin 16)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true) (hzm : MaskDisjoint z m) :
    (∑ x : MaskCoordinates m → Byte, inputLaw right a m x ^ 2) =
      ((65 : ℝ)/8192) ^ maskSize m := by
  change (∑ x : MaskCoordinates m → Byte,
    productDensity (fun i v => channel right v (a i.val)) x ^ 2) = _
  rw [RestrictedProductDensity.productDensity_energy]
  calc
    _ = ∏ _ : MaskCoordinates m, (65 : ℝ)/8192 := by
      apply Finset.prod_congr rfl
      intro i _
      have hi : a i.val ≠ 0 := by
        intro hzero
        exact hzm i.val ((ha i.val).mp hzero) i.property
      exact (channel_resources right).collision_column _ hi
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, maskCoordinates_card]

/-- Input positions which are neither fixed zero nor chosen free. -/
def omittedMask (z s u : Fin 16) : Fin 16 :=
  maskComplement (maskUnion z (maskUnion s u))

theorem omittedMask_bit (z s u : Fin 16) (i : Fin 4) :
    maskBit (omittedMask z s u) i = true ↔
      maskBit z i ≠ true ∧ maskBit s i ≠ true ∧ maskBit u i ≠ true := by
  simp only [omittedMask, maskComplement_bit, maskUnion_bit]
  cases maskBit z i <;> cases maskBit s i <;> cases maskBit u i <;> decide

theorem omittedMask_size (r z s u : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4) :
    maskSize (omittedMask z s u) = maskSize r := by
  rw [omittedMask, maskComplement_size, maskUnion_size z (maskUnion s u) hzu,
    maskUnion_size s u hsu]
  omega

private theorem disjoint_union_left (z s u : Fin 16)
    (h : MaskDisjoint z (maskUnion s u)) : MaskDisjoint z s := by
  intro i hz hs
  apply h i hz
  rw [maskUnion_bit, Bool.or_eq_true]
  exact Or.inl hs

private theorem disjoint_union_right (z s u : Fin 16)
    (h : MaskDisjoint z (maskUnion s u)) : MaskDisjoint z u := by
  intro i hz hu
  apply h i hz
  rw [maskUnion_bit, Bool.or_eq_true]
  exact Or.inr hu

/-- A mask product is a product on its actual coordinate subtype. -/
theorem masked_product_eq (m : Fin 16) (F : Fin 4 → ℝ) :
    (∏ i : Fin 4, if maskBit m i = true then F i else 1) =
      ∏ i : MaskCoordinates m, F i.val := by
  classical
  calc
    _ = (∏ i : {i : Fin 4 // maskBit m i = true},
          if maskBit m i.val = true then F i.val else 1) *
        (∏ i : {i : Fin 4 // ¬ maskBit m i = true},
          if maskBit m i.val = true then F i.val else 1) :=
      (Fintype.prod_subtype_mul_prod_subtype
        (fun i : Fin 4 => maskBit m i = true)
        (fun i => if maskBit m i = true then F i else 1)).symm
    _ = (∏ i : MaskCoordinates m, F i.val) * 1 := by
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        exact if_pos i.property
      · apply Finset.prod_eq_one
        intro i _
        exact if_neg i.property
    _ = _ := mul_one _

/-- The omitted factors may depend arbitrarily on the free coordinates. -/
theorem product_partition_bound (r z s u : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (F : Fin 4 → ℝ) (p : ℝ) (hF : ∀ i, 0 ≤ F i)
    (hzero : ∀ i, maskBit z i = true → F i = 1)
    (hpoint : ∀ i, maskBit z i ≠ true → F i ≤ p) :
    (∏ i : Fin 4, F i) ≤ p ^ maskSize r *
      (∏ i : MaskCoordinates s, F i.val) * (∏ i : MaskCoordinates u, F i.val) := by
  classical
  have hp (i : Fin 4) : F i ≤
      (if maskBit s i = true then F i else 1) *
      (if maskBit u i = true then F i else 1) *
      (if maskBit (omittedMask z s u) i = true then p else 1) := by
    by_cases hs : maskBit s i = true
    · have hu : maskBit u i ≠ true := hsu i hs
      have ho : maskBit (omittedMask z s u) i ≠ true := by
        intro ho
        exact ((omittedMask_bit z s u i).mp ho).2.1 hs
      simp only [if_pos hs, if_neg hu, if_neg ho, mul_one, le_refl]
    · by_cases hu : maskBit u i = true
      · have ho : maskBit (omittedMask z s u) i ≠ true := by
          intro ho
          exact ((omittedMask_bit z s u i).mp ho).2.2 hu
        simp only [if_neg hs, if_pos hu, if_neg ho, one_mul, mul_one, le_refl]
      · by_cases hz : maskBit z i = true
        · have ho : maskBit (omittedMask z s u) i ≠ true := by
            intro ho
            exact ((omittedMask_bit z s u i).mp ho).1 hz
          simp only [if_neg hs, if_neg hu, if_neg ho, one_mul, hzero i hz, le_refl]
        · have ho : maskBit (omittedMask z s u) i = true :=
            (omittedMask_bit z s u i).mpr ⟨hz, hs, hu⟩
          simpa only [if_neg hs, if_neg hu, if_pos ho, one_mul] using hpoint i hz
  calc
    _ ≤ ∏ i : Fin 4,
        (if maskBit s i = true then F i else 1) *
        (if maskBit u i = true then F i else 1) *
        (if maskBit (omittedMask z s u) i = true then p else 1) :=
      Finset.prod_le_prod (fun i _ => hF i) (fun i _ => hp i)
    _ = (∏ i : Fin 4, if maskBit s i = true then F i else 1) *
        (∏ i : Fin 4, if maskBit u i = true then F i else 1) *
        (∏ i : Fin 4, if maskBit (omittedMask z s u) i = true then p else 1) := by
      simp only [Finset.prod_mul_distrib]
    _ = (∏ i : MaskCoordinates s, F i.val) * (∏ i : MaskCoordinates u, F i.val) *
        p ^ maskSize (omittedMask z s u) := by
      rw [masked_product_eq s F, masked_product_eq u F,
        masked_product_eq (omittedMask z s u) (fun _ => p)]
      simp only [Finset.prod_const, Finset.card_univ, maskCoordinates_card]
    _ = _ := by
      rw [omittedMask_size r z s u hsu hzu hsize]
      ring

/-- No event probability is divided out. -/
def restrictedSource (right : Orientation) (inverse : Bool) (a : Word) (r z : Fin 16)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event]
    (c : ShortenedGraph (byteDiffusionHom inverse) r z) : ℝ :=
  if event c then inputColumn right a c.val else 0

theorem restrictedSource_nonneg (right : Orientation) (inverse : Bool) (a : Word)
    (r z : Fin 16) (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop)
    [DecidablePred event] (c : ShortenedGraph (byteDiffusionHom inverse) r z) :
    0 ≤ restrictedSource right inverse a r z event c := by
  unfold restrictedSource
  split_ifs
  · exact inputColumn_nonneg right a c.val
  · exact le_rfl

/-- Actual byte-channel factors prove the density comparison. -/
theorem restrictedSource_domination (right : Orientation) (inverse : Bool) (a : Word)
    (r z s u : Fin 16) (hsu : MaskDisjoint s u)
    (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event]
    (c : ShortenedGraph (byteDiffusionHom inverse) r z) :
    restrictedSource right inverse a r z event c ≤ ((1 : ℝ)/64) ^ maskSize r *
      inputLaw right a s (fun i => c.val i.val) *
      inputLaw right a u (fun i => c.val i.val) := by
  have hevent : restrictedSource right inverse a r z event c ≤ inputColumn right a c.val := by
    unfold restrictedSource
    split_ifs
    · exact le_rfl
    · exact inputColumn_nonneg right a c.val
  apply hevent.trans
  change (∏ i : Fin 4, channel right (c.val i) (a i)) ≤ _
  have hzero (i : Fin 4) (hi : maskBit z i = true) :
      channel right (c.val i) (a i) = 1 := by
    rw [c.property.2 i hi, (ha i).mpr hi, (channel_resources right).zero_column]
    simp
  have hpoint (i : Fin 4) (hi : maskBit z i ≠ true) :
      channel right (c.val i) (a i) ≤ (1 : ℝ)/64 := by
    have hai : a i ≠ 0 := fun h => hi ((ha i).mp h)
    exact (channel_resources right).atom _ _ hai
  exact product_partition_bound r z s u hsu hzu hsize
    (fun i => channel right (c.val i) (a i)) ((1 : ℝ)/64)
    (fun _ => (channel_resources right).nonnegative _ _) hzero hpoint

/-- Source energy in the actual free input coordinates. -/
theorem restrictedSource_energy_le (right : Orientation) (inverse : Bool) (a : Word)
    (r z s u : Fin 16) (hsu : MaskDisjoint s u)
    (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ c : ShortenedGraph (byteDiffusionHom inverse) r z,
      restrictedSource right inverse a r z event c ^ 2) ≤
      ((1 : ℝ)/64) ^ (2 * maskSize r) *
        ((65 : ℝ)/8192) ^ (maskSize s + maskSize u) := by
  let e := inputSplitEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z s u hsu hzu hsize
  let scale : ℝ := ((1 : ℝ)/64) ^ maskSize r
  have hscale : 0 ≤ scale := pow_nonneg (by norm_num) _
  have hdom (c : ShortenedGraph (byteDiffusionHom inverse) r z) :
      restrictedSource right inverse a r z event c ≤
        scale * (inputLaw right a s (e c).1 * inputLaw right a u (e c).2) := by
    change restrictedSource right inverse a r z event c ≤
      ((1 : ℝ)/64) ^ maskSize r *
        (inputLaw right a s (fun i => c.val i.val) *
          inputLaw right a u (fun i => c.val i.val))
    simpa only [scale, mul_assoc] using
      restrictedSource_domination right inverse a r z s u hsu hzu hsize ha event c
  have hsquare (c : ShortenedGraph (byteDiffusionHom inverse) r z) :
      restrictedSource right inverse a r z event c ^ 2 ≤
        (scale * (inputLaw right a s (e c).1 * inputLaw right a u (e c).2)) ^ 2 :=
    (sq_le_sq₀ (restrictedSource_nonneg right inverse a r z event c)
      (mul_nonneg hscale (mul_nonneg (inputLaw_nonneg right a s _) (inputLaw_nonneg right a u _)))).mpr
        (hdom c)
  have henergy : (∑ p : (MaskCoordinates s → Byte) × (MaskCoordinates u → Byte),
      (inputLaw right a s p.1 * inputLaw right a u p.2)^2) =
        ((65 : ℝ)/8192) ^ (maskSize s + maskSize u) := by
    calc
      _ = (∑ x : MaskCoordinates s → Byte, inputLaw right a s x^2) *
          (∑ y : MaskCoordinates u → Byte, inputLaw right a u y^2) := by
        rw [Fintype.sum_prod_type]
        simp only [mul_pow]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        exact (Finset.mul_sum _ _ _).symm
      _ = _ := by
        rw [inputLaw_energy right a z s ha (disjoint_union_left z s u hzu),
          inputLaw_energy right a z u ha (disjoint_union_right z s u hzu), ← pow_add]
  calc
    _ ≤ ∑ c : ShortenedGraph (byteDiffusionHom inverse) r z,
        (scale * (inputLaw right a s (e c).1 * inputLaw right a u (e c).2))^2 :=
      Finset.sum_le_sum (fun c _ => hsquare c)
    _ = scale^2 * ∑ c : ShortenedGraph (byteDiffusionHom inverse) r z,
        (inputLaw right a s (e c).1 * inputLaw right a u (e c).2)^2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ = scale^2 * ∑ p : (MaskCoordinates s → Byte) × (MaskCoordinates u → Byte),
        (inputLaw right a s p.1 * inputLaw right a u p.2)^2 := by
      rw [Equiv.sum_comp e (fun p => (inputLaw right a s p.1 * inputLaw right a u p.2)^2)]
    _ = scale^2 * ((65 : ℝ)/8192) ^ (maskSize s + maskSize u) := by rw [henergy]
    _ = _ := by simp only [scale, ← pow_mul, Nat.mul_comm]

/-- The actual observed output tuple on a shortened source. -/
def outputCoordinates (inverse : Bool) (r z out : Fin 16)
    (c : ShortenedGraph (byteDiffusionHom inverse) r z) : MaskCoordinates out → Byte :=
  fun i => byteDiffusionOrientation inverse c.val i.val

/-- The fewer-output marginal is controlled before applying a signed channel. -/
theorem restrictedSource_marginal_energy_le (right : Orientation) (inverse : Bool) (a : Word)
    (r z s u out : Fin 16) (hsu : MaskDisjoint s u)
    (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : ShortenedGraph (byteDiffusionHom inverse) r z → Prop) [DecidablePred event] :
    (∑ y : MaskCoordinates out → Byte,
      RestrictedMarginalEnergy.marginal (outputCoordinates inverse r z out)
        (restrictedSource right inverse a r z event) y ^ 2) ≤
      ((1 : ℝ)/64) ^ (2 * maskSize r) * ((65 : ℝ)/8192) ^ maskSize out := by
  let e := inputSplitEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
    r z s u hsu hzu hsize
  have hsection (x : MaskCoordinates s → Byte) : Function.Bijective
      (fun y : MaskCoordinates u → Byte => outputCoordinates inverse r z out (e.symm (x,y))) := by
    change Function.Bijective (fun y : MaskCoordinates u → Byte =>
      fun i : MaskCoordinates out => byteDiffusionOrientation inverse
        ((inputSplitEquiv (byteDiffusionHom inverse) (byteDiffusionHom_zeroMDS inverse)
          r z s u hsu hzu hsize).symm (x,y)).val i.val)
    exact actual_output_section_bijective inverse r z s u out hsu hzu hsize hr
      (disjoint_union_left z s u hzu) hobs x
  have hdom (c : ShortenedGraph (byteDiffusionHom inverse) r z) :
      restrictedSource right inverse a r z event c ≤ ((1 : ℝ)/64) ^ maskSize r *
        inputLaw right a s (e c).1 * inputLaw right a u (e c).2 := by
    exact restrictedSource_domination right inverse a r z s u hsu hzu hsize ha event c
  have h := RestrictedMarginalEnergy.restricted_marginal_energy_le_of_bijective e
    (outputCoordinates inverse r z out) hsection (inputLaw right a s) (inputLaw right a u)
    (restrictedSource right inverse a r z event) (((1 : ℝ)/64) ^ maskSize r)
    (((65 : ℝ)/8192) ^ maskSize u) (inputLaw_nonneg right a s) (inputLaw_mass right a s)
    (inputLaw_nonneg right a u)
    (le_of_eq (inputLaw_energy right a z u ha (disjoint_union_right z s u hzu)))
    (pow_nonneg (by norm_num) _) (restrictedSource_nonneg right inverse a r z event) hdom
  have hcard : maskSize u = maskSize out := by omega
  simpa only [← pow_mul, Nat.mul_comm, hcard] using h

end AESConcrete.ActualRestrictedDensity
