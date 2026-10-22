import AESConcrete.ActivityMinorGeometry
import AESConcrete.RefinedChannelCommutation
import AESConcrete.PlaneFourierResponse
import AESConcrete.ActualMarkedUniform

/-!
# Exact contractions to retained physical coordinate minors

The contraction sums the omitted input coordinates and leaves an arbitrary
joint tensor response on the retained physical coordinates. Its normalization
is a cardinality ratio, before any MDS dimension or moment bound is applied.
Zero/full-uniform contractions are separate from the signed nonzero-uniform
expansion. No orthogonality of the expanded responses is asserted.

Independent uniform retained keys, whitening, omitted final MixColumns,
ordered-distinct pairs and 10/14/16 stay fixed. This adds no physical cap or
experiment linkage.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ActivityMinorContraction
open AESMixing
open AESConcrete.ActivityMinorGeometry
open AESConcrete.NonzeroUniformGraphCap (zeroUnit fullUniform nonzeroUniform)

attribute [local instance] Classical.propDecidable

section PartialResponse
variable {J V : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Retained outputs keep their original physical coordinate labels. -/
def minorKernel (L : J → Prop) (T : {j // L j} → V → V → ℝ)
    (w : {j // ¬ L j} → V → ℝ) (y : {j // L j} → V) (x : J → V) : ℝ :=
  (∏ j : {j // L j}, T j (y j) (x j.val)) *
    ∏ j : {j // ¬ L j}, w j (x j.val)

def minorResponse (L : J → Prop) (T : {j // L j} → V → V → ℝ)
    (w : {j // ¬ L j} → V → ℝ) (f : (J → V) → ℝ) :
    ({j // L j} → V) → ℝ :=
  action (minorKernel L T w) f

omit [AddCommGroup V] [DecidableEq V] in
/-- A rank-one omitted output contributes only its unit output vector.
The retained output remains an arbitrary joint response. -/
theorem coordinateKernel_rank_one_minor (L : J → Prop)
    (T : {j // L j} → V → V → ℝ) (w : {j // ¬ L j} → V → ℝ)
    (f : (J → V) → ℝ) (y : J → V) :
    action (coordinateKernel (fun j => if hj : L j then T ⟨j, hj⟩ else
      fun a b => w ⟨j, hj⟩ a * w ⟨j, hj⟩ b)) f y =
      (∏ j : {j // ¬ L j}, w j (y j.val)) *
        minorResponse L T w f (fun j => y j.val) := by
  unfold minorResponse minorKernel action coordinateKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Fintype.prod_subtype_mul_prod_subtype L]
  have hm (j : {j // L j}) :
      (if hj : L j.val then T ⟨j.val, hj⟩ else
        fun a b => w ⟨j.val, hj⟩ a * w ⟨j.val, hj⟩ b) (y j.val) (x j.val) =
        T j (y j.val) (x j.val) := by
    simp only [dif_pos j.property]
  have hu (j : {j // ¬ L j}) :
      (if hj : L j.val then T ⟨j.val, hj⟩ else
        fun a b => w ⟨j.val, hj⟩ a * w ⟨j.val, hj⟩ b) (y j.val) (x j.val) =
        w j (y j.val) * w j (x j.val) := by
    simp only [dif_neg j.property]
  simp_rw [hm, hu]
  rw [Finset.prod_mul_distrib]
  ring

omit [AddCommGroup V] [DecidableEq V] in
/-- Unit omitted output legs preserve exactly the retained response energy.
This gives no relation between distinct Boolean terms or output supports. -/
theorem coordinateKernel_rank_one_minor_energy (L : J → Prop)
    (T : {j // L j} → V → V → ℝ) (w : {j // ¬ L j} → V → ℝ)
    (hw : ∀ j, (∑ x : V, w j x ^ 2) = 1) (f : (J → V) → ℝ) :
    (∑ y, action (coordinateKernel (fun j => if hj : L j then T ⟨j, hj⟩ else
      fun a b => w ⟨j, hj⟩ a * w ⟨j, hj⟩ b)) f y ^ 2) =
      ∑ y, minorResponse L T w f y ^ 2 := by
  have he : action (coordinateKernel (fun j => if hj : L j then T ⟨j, hj⟩ else
      fun a b => w ⟨j, hj⟩ a * w ⟨j, hj⟩ b)) f =
      coordinateEmbedding L w (minorResponse L T w f) := by
    funext y
    rw [coordinateKernel_rank_one_minor]
    simp only [coordinateEmbedding, mul_comm]
  rw [he]
  exact coordinateEmbedding_isometry L w hw _

omit [AddCommGroup V] [DecidableEq V] in
/-- The singleton source coefficient is arbitrary and may be negative. -/
theorem minorResponse_scale (L : J → Prop) (T : {j // L j} → V → V → ℝ)
    (w : {j // ¬ L j} → V → ℝ) (a : ℝ) (f : (J → V) → ℝ) :
    minorResponse L T w (fun x => a * f x) = fun y => a * minorResponse L T w f y := by
  funext y
  unfold minorResponse action
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [AddCommGroup V] [DecidableEq V] in
theorem minorResponse_scale_energy (L : J → Prop)
    (T : {j // L j} → V → V → ℝ) (w : {j // ¬ L j} → V → ℝ)
    (a : ℝ) (f : (J → V) → ℝ) :
    (∑ y, minorResponse L T w (fun x => a * f x) y ^ 2) =
      a ^ 2 * ∑ y, minorResponse L T w f y ^ 2 := by
  rw [minorResponse_scale]
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]

theorem minorResponse_sub_div (L : J → Prop) (T : {j // L j} → V → V → ℝ)
    (w v : {j // ¬ L j} → V → ℝ) (a d : ℝ)
    (f : (J → V) → ℝ)
    (hweight : ∀ x : J → V,
      (∏ j : {j // ¬ L j}, w j (x j.val)) =
        (a * (∏ j : {j // ¬ L j}, v j (x j.val)) -
          ∏ j : {j // ¬ L j}, zeroUnit (x j.val)) / d) :
    minorResponse L T w f = fun y =>
      (a * minorResponse L T v f y -
        minorResponse L T (fun _ => zeroUnit) f y) / d := by
  funext y
  unfold minorResponse action minorKernel
  simp_rw [hweight]
  calc
    _ = ∑ x : J → V,
        (a * ((∏ j : {j // L j}, T j (y j) (x j.val)) *
          (∏ j : {j // ¬ L j}, v j (x j.val)) * f x) -
          (∏ j : {j // L j}, T j (y j) (x j.val)) *
          (∏ j : {j // ¬ L j}, zeroUnit (x j.val)) * f x) / d := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]

end PartialResponse

section ZeroUniform
variable {J V : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Omitted coordinates not fixed to zero contribute one unit full-uniform
input factor each. The count concerns physical coordinates, never codewords. -/
def uniformCount (L Z : J → Prop) : ℕ :=
  (Finset.univ.filter (fun j : {j // ¬ L j} => ¬ Z j.val)).card

def zeroUniformWeight (L Z : J → Prop) (j : {j // ¬ L j}) (x : V) : ℝ :=
  if Z j.val then zeroUnit x else fullUniform x

omit [DecidableEq J] in
/-- This finite-product identity is valid for any retained subset. The zero
constraints must be omitted coordinates, so no retained leg is accidentally
treated as an extra residual or as a scalar contraction. -/
theorem zeroUniformWeight_product (L Z : J → Prop)
    (hdisj : ∀ j, L j → ¬ Z j) (x : J → V) :
    (∏ j : {j // ¬ L j}, zeroUniformWeight L Z j (x j.val)) =
      if ∀ j, Z j → x j = 0 then
        1 / Real.sqrt (Fintype.card V : ℝ) ^ uniformCount L Z else 0 := by
  by_cases hz : ∀ j, Z j → x j = 0
  · rw [if_pos hz]
    have hf (j : {j // ¬ L j}) : zeroUniformWeight L Z j (x j.val) =
        if Z j.val then 1 else 1 / Real.sqrt (Fintype.card V : ℝ) := by
      by_cases hj : Z j.val
      · simp [zeroUniformWeight, hj, hz j.val hj, zeroUnit,
          supportConstant, identityKernel]
      · simp [zeroUniformWeight, hj, fullUniform]
    simp_rw [hf]
    rw [Finset.prod_ite]
    simp [uniformCount]
  · rw [if_neg hz]
    obtain ⟨j, hj, hx⟩ : ∃ j, Z j ∧ x j ≠ 0 := by simpa using hz
    have hn : ¬ L j := fun hL => hdisj j hL hj
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨j, hn⟩ : {j // ¬ L j}))
    simp [zeroUniformWeight, hj, zeroUnit, supportConstant, identityKernel, hx]

private theorem subgroup_sum_ite {X : Type*} [AddCommGroup X] [Fintype X]
    (C : AddSubgroup X) [Fintype C] (F : X → ℝ) :
    (∑ x : X, if x ∈ C then F x else 0) = ∑ c : C, F c.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- Raw normalized shortened-source sum, before any injective or surjective
restriction argument. Keeping this enumeration preserves every exact fiber. -/
theorem unitSubgroup_zeroUniform_raw_response
    (C : AddSubgroup (J → V)) [Fintype C] (L Z : J → Prop)
    (hdisj : ∀ j, L j → ¬ Z j)
    (T : {j // L j} → V → V → ℝ) (y : {j // L j} → V) :
    minorResponse L T (zeroUniformWeight L Z) (unitSubgroupIndicator C) y =
      ((∑ c : zeroSubgroup C Z, ∏ j : {j // L j}, T j (y j) (c.val j.val)) /
        Real.sqrt (Fintype.card C : ℝ)) /
        Real.sqrt (Fintype.card V : ℝ) ^ uniformCount L Z := by
  let F : (J → V) → ℝ := fun x => ∏ j : {j // L j}, T j (y j) (x j.val)
  have ht (x : J → V) :
      F x * (∏ j : {j // ¬ L j}, zeroUniformWeight L Z j (x j.val)) *
        unitSubgroupIndicator C x =
      ((if x ∈ zeroSubgroup C Z then F x else 0) /
        Real.sqrt (Fintype.card C : ℝ)) /
        Real.sqrt (Fintype.card V : ℝ) ^ uniformCount L Z := by
    rw [zeroUniformWeight_product L Z hdisj]
    by_cases hc : x ∈ C
    · by_cases hz : ∀ j, Z j → x j = 0
      · have hs : x ∈ zeroSubgroup C Z := ⟨hc, hz⟩
        simp only [unitSubgroupIndicator, if_pos hc, if_pos hz, if_pos hs]
        ring
      · have hs : x ∉ zeroSubgroup C Z := fun hs => hz hs.2
        simp only [unitSubgroupIndicator, if_pos hc, if_neg hz, if_neg hs,
          mul_zero, zero_mul, zero_div]
    · have hs : x ∉ zeroSubgroup C Z := fun hs => hc hs.1
      simp only [unitSubgroupIndicator, if_neg hc, if_neg hs, mul_zero, zero_div]
  unfold minorResponse action minorKernel
  change (∑ x : J → V, F x * _ * unitSubgroupIndicator C x) = _
  simp_rw [ht]
  rw [← Finset.sum_div, ← Finset.sum_div, subgroup_sum_ite]

/-- Exact normalization of arbitrary zero/full-uniform omitted legs. The
injectivity premise belongs to the actual shortened source restriction;
it is supplied by the geometry layer and is never inferred from cardinality.
No code-dimension or alphabet-power normalization is charged a second time. -/
theorem unitSubgroup_zeroUniform_response
    (C : AddSubgroup (J → V)) [Fintype C] (L Z : J → Prop)
    (hdisj : ∀ j, L j → ¬ Z j)
    (hinj : Function.Injective
      (fun c : zeroSubgroup C Z => restrictHom L c.val))
    (T : {j // L j} → V → V → ℝ) (y : {j // L j} → V) :
    minorResponse L T (zeroUniformWeight L Z) (unitSubgroupIndicator C) y =
      (Real.sqrt (Fintype.card (minorCode C Z L) : ℝ) /
        (Real.sqrt (Fintype.card C : ℝ) *
          Real.sqrt (Fintype.card V : ℝ) ^ uniformCount L Z)) *
        action (coordinateKernel T) (unitSubgroupIndicator (minorCode C Z L)) y := by
  let F : (J → V) → ℝ := fun x => ∏ j : {j // L j}, T j (y j) (x j.val)
  have hs : minorResponse L T (zeroUniformWeight L Z) (unitSubgroupIndicator C) y =
      ((∑ c : zeroSubgroup C Z, F c.val) / Real.sqrt (Fintype.card C : ℝ)) /
        Real.sqrt (Fintype.card V : ℝ) ^ uniformCount L Z :=
    unitSubgroup_zeroUniform_raw_response C L Z hdisj T y
  let e := minorSourceEquiv C Z L hinj
  have hr : (∑ c : zeroSubgroup C Z, F c.val) =
      ∑ c : minorCode C Z L, coordinateKernel T y c.val := by
    have h := e.sum_comp (fun c : minorCode C Z L => coordinateKernel T y c.val)
    have hc (c : zeroSubgroup C Z) : coordinateKernel T y (e c).val = F c.val := by
      change coordinateKernel T y (minorSourceEquiv C Z L hinj c).val = F c.val
      rw [minorSourceEquiv_val]
      rfl
    simpa only [hc] using h
  rw [hs, hr, PlaneFourierResponse.action_unitSubgroupIndicator]
  have hp : (0 : ℝ) < Fintype.card (minorCode C Z L) := by
    exact_mod_cast Fintype.card_pos
  have hn : Real.sqrt (Fintype.card (minorCode C Z L) : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hp)
  have hpC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hnC : Real.sqrt (Fintype.card C : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpC)
  have hpV : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hnV : Real.sqrt (Fintype.card V : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpV)
  field_simp [hn, hnC, hnV]

omit [AddCommGroup V] [DecidableEq V] in
private theorem sqrt_card_pow (n : ℕ) :
    Real.sqrt ((Fintype.card V : ℝ) ^ n) =
      Real.sqrt (Fintype.card V : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg _) n), ih, pow_succ]

/-- The cardinality ratio simplifies to one square-root alphabet factor per
zero constraint and per omitted full-uniform leg. The code dimension cancels;
it must not be charged as an extra `q^t` in a later moment bound. -/
theorem unitSubgroup_zeroUniform_response_of_cards
    (C : AddSubgroup (J → V)) [Fintype C] (L Z : J → Prop)
    (hdisj : ∀ j, L j → ¬ Z j)
    (hinj : Function.Injective
      (fun c : zeroSubgroup C Z => restrictHom L c.val))
    (t z : ℕ) (hzt : z ≤ t)
    (hC : Fintype.card C = Fintype.card V ^ t)
    (hD : Fintype.card (minorCode C Z L) = Fintype.card V ^ (t-z))
    (T : {j // L j} → V → V → ℝ) (y : {j // L j} → V) :
    minorResponse L T (zeroUniformWeight L Z) (unitSubgroupIndicator C) y =
      (1 / Real.sqrt (Fintype.card V : ℝ) ^ (z + uniformCount L Z)) *
        action (coordinateKernel T) (unitSubgroupIndicator (minorCode C Z L)) y := by
  rw [unitSubgroup_zeroUniform_response C L Z hdisj hinj]
  have hc : Real.sqrt (Fintype.card C : ℝ) =
      Real.sqrt (Fintype.card V : ℝ) ^ t := by
    rw [hC, Nat.cast_pow, sqrt_card_pow]
  have hd : Real.sqrt (Fintype.card (minorCode C Z L) : ℝ) =
      Real.sqrt (Fintype.card V : ℝ) ^ (t-z) := by
    rw [hD, Nat.cast_pow, sqrt_card_pow]
  rw [hc, hd]
  congr 1
  have hv : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hn : Real.sqrt (Fintype.card V : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hv)
  have ht : Real.sqrt (Fintype.card V : ℝ) ^ t =
      Real.sqrt (Fintype.card V : ℝ) ^ (t-z) *
        Real.sqrt (Fintype.card V : ℝ) ^ z := by
    rw [← pow_add]
    congr 1
    omega
  rw [ht, pow_add]
  field_simp [hn]

/-- A surjective actual shortened-source restriction has equal additive-map
fibers. One retained zero row sum therefore kills the response, including
the full-dimensional puncturing endpoint where restriction is not injective. -/
theorem unitSubgroup_zeroUniform_response_of_surjective
    (C : AddSubgroup (J → V)) [Fintype C] (L Z : J → Prop)
    (hdisj : ∀ j, L j → ¬ Z j)
    (hsurj : Function.Surjective
      (fun c : zeroSubgroup C Z => restrictHom L c.val))
    (T : {j // L j} → V → V → ℝ) (k : {j // L j})
    (hrow : ∀ y : V, (∑ x : V, T k y x) = 0) :
    minorResponse L T (zeroUniformWeight L Z) (unitSubgroupIndicator C) = 0 := by
  funext y
  rw [unitSubgroup_zeroUniform_raw_response C L Z hdisj T y]
  let r : zeroSubgroup C Z →+ ({j // L j} → V) :=
    (restrictHom L).comp (zeroSubgroup C Z).subtype
  have hs := ActualMarkedUniform.sum_comp_uniform r hsurj
    (fun v : {j // L j} → V => ∏ j : {j // L j}, T j (y j) (v j))
  have hraw : (∑ c : zeroSubgroup C Z,
      ∏ j : {j // L j}, T j (y j) (c.val j.val)) = 0 := by
    calc
      _ = (Fintype.card r.ker : ℝ) *
          ∑ v : {j // L j} → V, ∏ j : {j // L j}, T j (y j) (v j) := hs
      _ = 0 := by
        rw [← Fintype.prod_sum]
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (hrow (y k)), mul_zero]
  simp only [hraw, zero_div, Pi.zero_apply]

/-- The other raw-source endpoint uses the actual zero shortened source.
It also needs no injective restriction premise or minor normalization. -/
theorem unitSubgroup_zeroUniform_response_of_zero_source
    (C : AddSubgroup (J → V)) [Fintype C] (L Z : J → Prop)
    (hdisj : ∀ j, L j → ¬ Z j)
    (hsource : ∀ x : J → V, x ∈ zeroSubgroup C Z ↔ x = 0)
    (T : {j // L j} → V → V → ℝ) (k : {j // L j})
    (hzero : ∀ y : V, T k y 0 = 0) :
    minorResponse L T (zeroUniformWeight L Z) (unitSubgroupIndicator C) = 0 := by
  funext y
  rw [unitSubgroup_zeroUniform_raw_response C L Z hdisj T y]
  have hraw : (∑ c : zeroSubgroup C Z,
      ∏ j : {j // L j}, T j (y j) (c.val j.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    have hc : c.val = 0 := (hsource c.val).mp c.property
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [hc]
    exact hzero (y k)
  simp only [hraw, zero_div, Pi.zero_apply]

end ZeroUniform

section NonzeroExpansion
variable {J V : Type*} [Fintype J] [DecidableEq J]
  [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The active omitted coordinates are the only Boolean choices. In
particular, the later one- and two-output-leg applications have one and
two such coordinates, respectively; existing zero legs are never expanded. -/
abbrev UniformOmitted (L Z : J → Prop) := {j : {j // ¬ L j} // ¬ Z j.val}

def nonzeroWeight (L Z : J → Prop) (j : {j // ¬ L j}) (x : V) : ℝ :=
  if Z j.val then zeroUnit x else nonzeroUniform x

def choiceWeight (L Z : J → Prop) (σ : UniformOmitted L Z → Bool)
    (j : {j // ¬ L j}) (x : V) : ℝ :=
  if hj : Z j.val then zeroUnit x
  else if σ ⟨j, hj⟩ then fullUniform x else zeroUnit x

def choiceCoefficient (L Z : J → Prop) (σ : UniformOmitted L Z → Bool) : ℝ :=
  ∏ j : UniformOmitted L Z,
    (if σ j then Real.sqrt (Fintype.card V : ℝ) else -1) /
      Real.sqrt ((Fintype.card V : ℝ) - 1)

/-- Expanded zero constraints are still predicates on the original physical
labels. This definition does not constrain any retained output coordinate. -/
def choiceZeros (L Z : J → Prop) (σ : UniformOmitted L Z → Bool) (j : J) : Prop :=
  Z j ∨ ∃ (hL : ¬ L j) (hZ : ¬ Z j), σ ⟨⟨j, hL⟩, hZ⟩ = false

omit [Fintype J] [DecidableEq J] in
theorem choiceZeros_disjoint (L Z : J → Prop) (hdisj : ∀ j, L j → ¬ Z j)
    (σ : UniformOmitted L Z → Bool) : ∀ j, L j → ¬ choiceZeros L Z σ j := by
  intro j hj hzero
  rcases hzero with hZ | ⟨hL, _, _⟩
  · exact hdisj j hj hZ
  · exact hL hj

omit [Fintype J] [DecidableEq J] in
/-- Every Boolean term is exactly one zero/full-uniform contraction of an
actual minor. This is the bridge from the signed expansion to normalization. -/
theorem choiceWeight_eq_zeroUniform (L Z : J → Prop)
    (σ : UniformOmitted L Z → Bool) :
    choiceWeight (V := V) L Z σ = zeroUniformWeight L (choiceZeros L Z σ) := by
  funext j x
  by_cases hZ : Z j.val
  · simp [choiceWeight, zeroUniformWeight, choiceZeros, hZ]
  · cases hs : σ ⟨j, hZ⟩
    · simp [choiceWeight, zeroUniformWeight, choiceZeros, hZ, hs, j.property]
    · simp [choiceWeight, zeroUniformWeight, choiceZeros, hZ, hs]

private theorem nonzero_choice_sum (hn : 1 < Fintype.card V) (x : V) :
    nonzeroUniform x = ∑ b : Bool,
      ((if b then Real.sqrt (Fintype.card V : ℝ) else -1) /
        Real.sqrt ((Fintype.card V : ℝ) - 1)) *
      (if b then fullUniform x else zeroUnit x) := by
  rw [AESConcrete.NonzeroUniformGraphCap.nonzeroUniform_decomposition hn]
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true]
  ring

omit [DecidableEq J] in
private theorem nonzeroWeight_product_split (L Z : J → Prop) (x : J → V) :
    (∏ j : {j // ¬ L j}, nonzeroWeight L Z j (x j.val)) =
      (∏ j : {j : {j // ¬ L j} // Z j.val}, zeroUnit (x j.val.val)) *
        ∏ j : UniformOmitted L Z, nonzeroUniform (x j.val.val) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun j : {j // ¬ L j} => Z j.val)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    exact if_pos j.property
  · apply Finset.prod_congr rfl
    intro j _
    exact if_neg j.property

omit [DecidableEq J] in
private theorem choiceWeight_product_split (L Z : J → Prop)
    (σ : UniformOmitted L Z → Bool) (x : J → V) :
    (∏ j : {j // ¬ L j}, choiceWeight L Z σ j (x j.val)) =
      (∏ j : {j : {j // ¬ L j} // Z j.val}, zeroUnit (x j.val.val)) *
        ∏ j : UniformOmitted L Z,
          if σ j then fullUniform (x j.val.val) else zeroUnit (x j.val.val) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (fun j : {j // ¬ L j} => Z j.val)]
  congr 1
  · apply Finset.prod_congr rfl
    intro j _
    exact dif_pos j.property
  · apply Finset.prod_congr rfl
    intro j _
    exact dif_neg j.property

/-- Exact signed subset expansion on any number of omitted active legs.
There is no norm loss and no orthogonality premise in this identity. -/
theorem nonzeroWeight_product_expansion (hn : 1 < Fintype.card V)
    (L Z : J → Prop) (x : J → V) :
    (∏ j : {j // ¬ L j}, nonzeroWeight L Z j (x j.val)) =
      ∑ σ : UniformOmitted L Z → Bool,
        choiceCoefficient (V := V) L Z σ *
          ∏ j : {j // ¬ L j}, choiceWeight L Z σ j (x j.val) := by
  rw [nonzeroWeight_product_split]
  simp_rw [nonzero_choice_sum hn]
  rw [Fintype.prod_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib, choiceWeight_product_split]
  unfold choiceCoefficient
  ring

/-- One theorem handles one or two nonzero-uniform output legs, mixed with
any omitted zero legs. All terms share the same signed source function. -/
theorem minorResponse_nonzero_expansion (hn : 1 < Fintype.card V)
    (L Z : J → Prop) (T : {j // L j} → V → V → ℝ)
    (f : (J → V) → ℝ) :
    minorResponse L T (nonzeroWeight L Z) f = fun y =>
      ∑ σ : UniformOmitted L Z → Bool,
        choiceCoefficient (V := V) L Z σ *
          minorResponse L T (zeroUniformWeight L (choiceZeros L Z σ)) f y := by
  funext y
  unfold minorResponse action minorKernel
  simp_rw [nonzeroWeight_product_expansion hn]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro x _
  rw [← choiceWeight_eq_zeroUniform]
  ring

/-- The normalized signed expansion after every term's actual source-to-minor
equivalence. This formula can be specialized to one or two omitted active
legs before applying any triangle inequality or moment estimate. -/
theorem unitSubgroup_nonzero_response (hn : 1 < Fintype.card V)
    (C : AddSubgroup (J → V)) [Fintype C] (L Z : J → Prop)
    (hdisj : ∀ j, L j → ¬ Z j)
    (hinj : ∀ σ : UniformOmitted L Z → Bool, Function.Injective
      (fun c : zeroSubgroup C (choiceZeros L Z σ) => restrictHom L c.val))
    (T : {j // L j} → V → V → ℝ) (y : {j // L j} → V) :
    minorResponse L T (nonzeroWeight L Z) (unitSubgroupIndicator C) y =
      ∑ σ : UniformOmitted L Z → Bool,
        choiceCoefficient (V := V) L Z σ *
          (Real.sqrt (Fintype.card (minorCode C (choiceZeros L Z σ) L) : ℝ) /
            (Real.sqrt (Fintype.card C : ℝ) * Real.sqrt (Fintype.card V : ℝ) ^
              uniformCount L (choiceZeros L Z σ))) *
          action (coordinateKernel T)
            (unitSubgroupIndicator (minorCode C (choiceZeros L Z σ) L)) y := by
  rw [minorResponse_nonzero_expansion hn]
  apply Finset.sum_congr rfl
  intro σ _
  rw [unitSubgroup_zeroUniform_response C L (choiceZeros L Z σ)
    (choiceZeros_disjoint L Z hdisj σ) (hinj σ)]
  ring

end NonzeroExpansion

section ResidualEndpoints
variable {K V : Type*} [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Fintype V]

/-- A zero-dimensional retained minor is the zero point and is killed by
any one retained zero column. This statement needs a retained coordinate. -/
theorem subgroup_zero_response (C : AddSubgroup (K → V)) [Fintype C]
    (hC : ∀ x : K → V, x ∈ C ↔ x = 0)
    (T : K → V → V → ℝ) (k : K) (hzero : ∀ y, T k y 0 = 0) :
    action (coordinateKernel T) (unitSubgroupIndicator C) = 0 := by
  funext y
  have ht (x : K → V) : coordinateKernel T y x * unitSubgroupIndicator C x = 0 := by
    by_cases hx : x = 0
    · subst x
      have hp : coordinateKernel T y 0 = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ k)
        exact hzero (y k)
      rw [hp, zero_mul]
    · simp [unitSubgroupIndicator, hC, hx]
  simp only [action, ht, Finset.sum_const_zero, Pi.zero_apply]

/-- A full retained minor is constant and is killed by one retained zero
row sum. No puncturing injectivity is used at the full-space endpoint. -/
theorem subgroup_full_response (C : AddSubgroup (K → V)) [Fintype C]
    (hC : ∀ x : K → V, x ∈ C)
    (T : K → V → V → ℝ) (k : K)
    (hrow : ∀ y, (∑ x : V, T k y x) = 0) :
    action (coordinateKernel T) (unitSubgroupIndicator C) = 0 := by
  funext y
  unfold action
  simp only [unitSubgroupIndicator, hC, if_true, mul_one_div]
  rw [← Finset.sum_div]
  change (∑ x : K → V, ∏ i : K, T i (y i) (x i)) / _ = 0
  rw [← Fintype.prod_sum (fun i x => T i (y i) x)]
  have hp : (∏ i : K, ∑ x : V, T i (y i) x) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact hrow (y k)
  rw [hp, zero_div]

end ResidualEndpoints
end AESConcrete.ActivityMinorContraction
