import AESPaper.ActualZeroEvents
import AESConcrete.ActualRestrictedDensity

/-!
# Actual whole-word source sections after prescribed zeros

The shortened graph uses the checked forward boundary. Its source density
retains the original four word-law factors and any further event indicator.
Only solved active factors are capped. The free laws use whole-word point
and collision bounds; no byte response constant is reused as a word bound.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RestrictedSourceSections
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.ManySourceBounds (activeSourceMask activeSourceCount)
open AESConcrete.RestrictedProductDensity (productDensity)
open AESConcrete.RestrictedMDSCoordinates (inputSplitEquiv)

/-- The source tuple has prescribed output zeros and inactive input zeros. -/
abbrev Source (r z : Fin 16) :=
  ShortenedGraph GroupedRecurrence.boundary.toAddMonoidHom r z

/-- A finite mask calculation, with no hypothesis on source values. -/
theorem inactive_mask_size_of_bits : ∀ (a : Fin 4 → Bool) (z : Fin 16),
    (∀ i, maskBit z i = !(a i)) → maskSize z = 4-residualDegree a := by decide

/-- An actual input always has a mask recording exactly its inactive sources. -/
theorem inactive_mask_exists (b : AES.State) : ∃ z : Fin 16,
    (∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true) ∧
      maskSize z = 4-activeSourceCount b := by
  obtain ⟨z,hz,hsize⟩ := ActualZeroEvents.inactive_mask_exists (activeSourceMask b)
  refine ⟨z, ?_, hsize⟩
  intro i
  rw [hz i]
  simp [activeSourceMask]

/-- The caller's inactive-mask witness fixes its size uniquely. -/
theorem inactive_mask_size (b : AES.State) (z : Fin 16)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true) :
    maskSize z = 4-activeSourceCount b := by
  have hz (i : Fin 4) : maskBit z i = !(activeSourceMask b i) := by
    by_cases hi : sourceInput b i = 0
    · rw [(ha i).mp hi]
      simp [activeSourceMask, hi]
    · have hzfalse : maskBit z i = false := by
        cases he : maskBit z i
        · rfl
        · exact False.elim (hi ((ha i).mpr he))
      rw [hzfalse]
      simp [activeSourceMask, hi]
  exact inactive_mask_size_of_bits (activeSourceMask b) z hz

/-- The free input dimension is the active source count minus prescribed zeros. -/
theorem free_dimension (b : AES.State) (r z s u : Fin 16)
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true) :
    maskSize s + maskSize u = activeSourceCount b-maskSize r := by
  have hz := inactive_mask_size b z ha
  have hw := residualDegree_le (activeSourceMask b)
  change activeSourceCount b ≤ 4 at hw
  omega

/-- Every factor is an original whole-word source law. -/
def freeLaw (b : AES.State) (m : Fin 16) (x : MaskCoordinates m → AES.Word) : ℝ :=
  productDensity (fun i v => wordLaw (sourceInput b i.val) v) x

theorem freeLaw_nonneg (b : AES.State) (m : Fin 16)
    (x : MaskCoordinates m → AES.Word) : 0 ≤ freeLaw b m x :=
  RestrictedProductDensity.productDensity_nonneg _
    (fun _ _ => StartingWord.wordLaw_nonnegative _ _) x

theorem freeLaw_mass (b : AES.State) (m : Fin 16) :
    (∑ x : MaskCoordinates m → AES.Word, freeLaw b m x) = 1 :=
  RestrictedProductDensity.productDensity_mass_one _
    (fun _ => StartingWord.wordLaw_total _)

/-- The collision resource is for active whole-word factors. -/
theorem freeLaw_energy_le (b : AES.State) (z m : Fin 16)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (hzm : MaskDisjoint z m) :
    (∑ x : MaskCoordinates m → AES.Word, freeLaw b m x ^ 2) ≤
      (6/(5*q)) ^ maskSize m := by
  have hc (i : MaskCoordinates m) :
      (∑ v, wordLaw (sourceInput b i.val) v ^ 2) ≤ 6/(5*q) := by
    have hi : sourceInput b i.val ≠ 0 := by
      intro hzero
      exact hzm i.val ((ha i.val).mp hzero) i.property
    exact (StartingWord.wordLaw_collision_lt_six_fifths _ hi).le
  simpa only [freeLaw, maskCoordinates_card] using
    RestrictedProductDensity.productDensity_energy_le
      (fun (i : MaskCoordinates m) v => wordLaw (sourceInput b i.val) v) (6/(5*q)) hc

/-- No event probability is divided out. -/
def density (b : AES.State) (r z : Fin 16)
    (event : Source r z → Prop) [DecidablePred event] (c : Source r z) : ℝ :=
  if event c then ∏ i : Fin 4, wordLaw (sourceInput b i) (c.val i) else 0

theorem density_nonneg (b : AES.State) (r z : Fin 16)
    (event : Source r z → Prop) [DecidablePred event] (c : Source r z) :
    0 ≤ density b r z event c := by
  unfold density
  split_ifs
  · exact ActualZeroEvents.source_product_nonnegative b c.val
  · exact le_rfl

theorem disjoint_union_left (z s u : Fin 16)
    (h : MaskDisjoint z (maskUnion s u)) : MaskDisjoint z s := by
  intro i hz hs
  apply h i hz
  rw [maskUnion_bit, Bool.or_eq_true]
  exact Or.inl hs

theorem disjoint_union_right (z s u : Fin 16)
    (h : MaskDisjoint z (maskUnion s u)) : MaskDisjoint z u := by
  intro i hz hu
  apply h i hz
  rw [maskUnion_bit, Bool.or_eq_true]
  exact Or.inr hu

/-- At the inactive positions the exact delta factor is one. -/
theorem inactive_factor_eq_one (b : AES.State) (r z : Fin 16)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (c : Source r z) (i : Fin 4) (hi : maskBit z i = true) :
    wordLaw (sourceInput b i) (c.val i) = 1 := by
  rw [(ha i).mpr hi, c.property.2 i hi, OneSourceLaw.wordLaw_zero_input, if_pos rfl]

/-- Exactly |r| active factors are omitted; all other factors remain weighted. -/
theorem density_domination (b : AES.State) (r z s u : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : Source r z → Prop) [DecidablePred event] (c : Source r z) :
    density b r z event c ≤ (20/q) ^ maskSize r *
      freeLaw b s (fun i => c.val i.val) * freeLaw b u (fun i => c.val i.val) := by
  have hevent : density b r z event c ≤
      ∏ i : Fin 4, wordLaw (sourceInput b i) (c.val i) := by
    unfold density
    split_ifs
    · exact le_rfl
    · exact ActualZeroEvents.source_product_nonnegative b c.val
  apply hevent.trans
  have hpoint (i : Fin 4) (hi : maskBit z i ≠ true) :
      wordLaw (sourceInput b i) (c.val i) ≤ 20/q := by
    have hai : sourceInput b i ≠ 0 := fun h => hi ((ha i).mp h)
    exact (StartingWord.wordLaw_point_lt _ _ hai).le
  exact ActualRestrictedDensity.product_partition_bound r z s u hsu hzu hsize
    (fun i => wordLaw (sourceInput b i) (c.val i)) (20/q)
    (fun _ => StartingWord.wordLaw_nonnegative _ _)
    (inactive_factor_eq_one b r z ha c) hpoint

/-- The actual source split keeps two disjoint groups of free inputs. -/
def sourceSplit (r z s u : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4) :
    Source r z ≃ (MaskCoordinates s → AES.Word) × (MaskCoordinates u → AES.Word) :=
  inputSplitEquiv GroupedRecurrence.boundary.toAddMonoidHom
    ActivityKernel.aesBoundary_zeroMDS r z s u hsu hzu hsize

theorem sourceSplit_apply (r z s u : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (c : Source r z) :
    sourceSplit r z s u hsu hzu hsize c =
      (fun i => c.val i.val, fun i => c.val i.val) := rfl

/-- Marked outputs use the forward boundary, unlike inverse law relabeling. -/
def outputCoordinates (r z out : Fin 16) (c : Source r z) :
    MaskCoordinates out → AES.Word := fun i => GroupedRecurrence.boundary c.val i.val

/-- Each fixed complementary-input section has exactly one source per marked tuple. -/
theorem output_section_bijective (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (x : MaskCoordinates s → AES.Word) :
    Function.Bijective (fun y : MaskCoordinates u → AES.Word =>
      outputCoordinates r z out ((sourceSplit r z s u hsu hzu hsize).symm (x,y))) := by
  exact RestrictedMDSCoordinates.output_section_bijective
    GroupedRecurrence.boundary.toAddMonoidHom ActivityKernel.aesBoundary_zeroMDS
    r z s u out hsu hzu hsize hr (disjoint_union_left z s u hzu) hobs x

/-- A full marked information set identifies the shortened source itself. -/
theorem output_projection_bijective (r z out : Fin 16)
    (hr : MaskDisjoint r out)
    (hsize : maskSize r + maskSize z + maskSize out = 4) :
    Function.Bijective (outputCoordinates r z out) :=
  RestrictedMDSCoordinates.output_projection_bijective
    GroupedRecurrence.boundary.toAddMonoidHom ActivityKernel.aesBoundary_zeroMDS
    r z out hr hsize

/-- A chosen free input information set also identifies the shortened source. -/
theorem input_projection_bijective (r z inp : Fin 16)
    (hz : MaskDisjoint z inp)
    (hsize : maskSize r + maskSize z + maskSize inp = 4) :
    Function.Bijective (fun c : Source r z => fun i : MaskCoordinates inp => c.val i.val) :=
  RestrictedMDSCoordinates.input_projection_bijective
    GroupedRecurrence.boundary.toAddMonoidHom ActivityKernel.aesBoundary_zeroMDS
    r z inp hz hsize

/-- The actual marked-output bijection after fixing the complementary inputs. -/
def sectionEquiv (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (x : MaskCoordinates s → AES.Word) :
    (MaskCoordinates u → AES.Word) ≃ (MaskCoordinates out → AES.Word) :=
  Equiv.ofBijective (fun y =>
    outputCoordinates r z out ((sourceSplit r z s u hsu hzu hsize).symm (x,y)))
    (output_section_bijective r z s u out hsu hzu hsize hr hobs x)

/-- An exact sum of the original source weights, one point per fixed-input section. -/
theorem marginal_eq_section_sum (b : AES.State) (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (event : Source r z → Prop) [DecidablePred event]
    (y : MaskCoordinates out → AES.Word) :
    RestrictedMarginalEnergy.marginal (outputCoordinates r z out) (density b r z event) y =
      ∑ x : MaskCoordinates s → AES.Word,
        density b r z event ((sourceSplit r z s u hsu hzu hsize).symm
          (x, (sectionEquiv r z s u out hsu hzu hsize hr hobs x).symm y)) :=
  RestrictedMarginalEnergy.marginal_eq_section_sum
    (sourceSplit r z s u hsu hzu hsize) (outputCoordinates r z out)
    (sectionEquiv r z s u out hsu hzu hsize hr hobs) (fun _ _ => rfl)
    (density b r z event) y

/-- Domination retains both complementary-input weights in the actual mixture. -/
theorem marginal_le_scaled_mixture (b : AES.State) (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : Source r z → Prop) [DecidablePred event]
    (y : MaskCoordinates out → AES.Word) :
    RestrictedMarginalEnergy.marginal (outputCoordinates r z out) (density b r z event) y ≤
      (20/q) ^ maskSize r * RestrictedMarginalEnergy.sectionMixture
        (sectionEquiv r z s u out hsu hzu hsize hr hobs) (freeLaw b s) (freeLaw b u) y :=
  RestrictedMarginalEnergy.marginal_le_scaled_mixture
    (sourceSplit r z s u hsu hzu hsize) (outputCoordinates r z out)
    (sectionEquiv r z s u out hsu hzu hsize hr hobs) (fun _ _ => rfl)
    (freeLaw b s) (freeLaw b u) (density b r z event) ((20/q) ^ maskSize r)
    (density_domination b r z s u hsu hzu hsize ha event) y

/-- The source-energy branch pays two powers of the event point cap. -/
theorem density_energy_le (b : AES.State) (r z s u : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : Source r z → Prop) [DecidablePred event] :
    (∑ c : Source r z, density b r z event c ^ 2) ≤
      (20/q) ^ (2 * maskSize r) * (6/(5*q)) ^ (maskSize s + maskSize u) := by
  let e := sourceSplit r z s u hsu hzu hsize
  let scale : ℝ := (20/q) ^ maskSize r
  have hscale : 0 ≤ scale := pow_nonneg (by norm_num [q]) _
  have hdom (c : Source r z) : density b r z event c ≤
      scale * (freeLaw b s (e c).1 * freeLaw b u (e c).2) := by
    simpa only [scale, e, sourceSplit_apply, mul_assoc] using
      density_domination b r z s u hsu hzu hsize ha event c
  have hsquare (c : Source r z) : density b r z event c ^ 2 ≤
      (scale * (freeLaw b s (e c).1 * freeLaw b u (e c).2)) ^ 2 :=
    (sq_le_sq₀ (density_nonneg b r z event c)
      (mul_nonneg hscale (mul_nonneg (freeLaw_nonneg b s _) (freeLaw_nonneg b u _)))).mpr
      (hdom c)
  have he : (∑ p : (MaskCoordinates s → AES.Word) × (MaskCoordinates u → AES.Word),
      (freeLaw b s p.1 * freeLaw b u p.2)^2) ≤
      (6/(5*q)) ^ (maskSize s + maskSize u) := by
    calc
      _ = (∑ x : MaskCoordinates s → AES.Word, freeLaw b s x^2) *
          (∑ y : MaskCoordinates u → AES.Word, freeLaw b u y^2) := by
        rw [Fintype.sum_prod_type]
        simp only [mul_pow]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        exact (Finset.mul_sum _ _ _).symm
      _ ≤ (6/(5*q)) ^ maskSize s * (6/(5*q)) ^ maskSize u :=
        mul_le_mul (freeLaw_energy_le b z s ha (disjoint_union_left z s u hzu))
          (freeLaw_energy_le b z u ha (disjoint_union_right z s u hzu))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          (pow_nonneg (by norm_num [q]) _)
      _ = _ := (pow_add _ _ _).symm
  calc
    _ ≤ ∑ c : Source r z, (scale * (freeLaw b s (e c).1 * freeLaw b u (e c).2))^2 :=
      Finset.sum_le_sum (fun c _ => hsquare c)
    _ = scale^2 * ∑ c : Source r z, (freeLaw b s (e c).1 * freeLaw b u (e c).2)^2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ = scale^2 * ∑ p : (MaskCoordinates s → AES.Word) × (MaskCoordinates u → AES.Word),
        (freeLaw b s p.1 * freeLaw b u p.2)^2 := by
      rw [Equiv.sum_comp e (fun p => (freeLaw b s p.1 * freeLaw b u p.2)^2)]
    _ ≤ scale^2 * (6/(5*q)) ^ (maskSize s + maskSize u) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg scale)
    _ = _ := by simp only [scale, ← pow_mul, Nat.mul_comm]

/-- With fewer marked outputs, averaging exact sections preserves the product
collision bound. This is a nonnegative-marginal statement, before R acts. -/
theorem marginal_energy_le (b : AES.State) (r z s u out : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hr : MaskDisjoint r out)
    (hobs : maskSize r + maskSize z + maskSize out + maskSize s = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : Source r z → Prop) [DecidablePred event] :
    (∑ y : MaskCoordinates out → AES.Word,
      RestrictedMarginalEnergy.marginal (outputCoordinates r z out)
        (density b r z event) y ^ 2) ≤
      (20/q) ^ (2 * maskSize r) * (6/(5*q)) ^ maskSize out := by
  let e := sourceSplit r z s u hsu hzu hsize
  have hsection (x : MaskCoordinates s → AES.Word) : Function.Bijective
      (fun y : MaskCoordinates u → AES.Word => outputCoordinates r z out (e.symm (x,y))) :=
    output_section_bijective r z s u out hsu hzu hsize hr hobs x
  have hdom (c : Source r z) : density b r z event c ≤ (20/q) ^ maskSize r *
      freeLaw b s (e c).1 * freeLaw b u (e c).2 :=
    density_domination b r z s u hsu hzu hsize ha event c
  have h := RestrictedMarginalEnergy.restricted_marginal_energy_le_of_bijective e
    (outputCoordinates r z out) hsection (freeLaw b s) (freeLaw b u)
    (density b r z event) ((20/q) ^ maskSize r) ((6/(5*q)) ^ maskSize u)
    (freeLaw_nonneg b s) (freeLaw_mass b s) (freeLaw_nonneg b u)
    (freeLaw_energy_le b z u ha (disjoint_union_right z s u hzu))
    (pow_nonneg (by norm_num [q]) _) (density_nonneg b r z event) hdom
  have hcard : maskSize u = maskSize out := by omega
  simpa only [← pow_mul, Nat.mul_comm, hcard] using h

end AESPaper.RestrictedSourceSections
