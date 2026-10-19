import AESPaper.ActivityMDSCounts
import AESPaper.BoundaryZeros
import AESConcrete.RefinedWordProjection
import AESConcrete.DegreeCentering
import AESMixing.SupportRepresentation
import AESMixing.PointedProducts

/-!
# The actual word-activity kernel for the fixed v9 AES target
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace AESPaper.ActivityKernel
open AESMixing
open AESConcrete.RefinedWordProjection
open AESConcrete.DegreeCentering (globalUniformKernel distinguishedState)
open AESPaper.ActivityMDSCounts (supportCount supportCount_zero supportCount_small)

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/- Fresh projection algebra: the newer completeness module is not imported. -/
theorem refined_compose (z : V) (hn : 1 < Fintype.card V) (d a : Fin 5) :
    kernelCompose (refinedKernel z d a) (refinedKernel z d a) =
      refinedKernel z d a := by
  funext y x
  unfold refinedKernel kernelCompose
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  have hterm (r : SupportIndex d.val) :
      (∑ v,
        (if AES.maskSize r.val.2 + a.val = 4 then supportIndexKernel z r y v else 0) *
        (if AES.maskSize p.val.2 + a.val = 4 then supportIndexKernel z p v x else 0)) =
        if r = p then
          (if AES.maskSize p.val.2 + a.val = 4 then supportIndexKernel z p y x else 0)
        else 0 := by
    by_cases hp : AES.maskSize p.val.2 + a.val = 4
    · by_cases hr : AES.maskSize r.val.2 + a.val = 4
      · simp only [hp, hr, if_true]
        change kernelCompose (supportIndexKernel z r) (supportIndexKernel z p) y x = _
        rw [supportIndexKernel_compose z hn]
        by_cases he : r = p
        · subst r
          simp
        · simp [he, Ne.symm he]
      · by_cases he : r = p
        · subst r
          exact (hr hp).elim
        · simp [hr, he]
    · simp [hp]
  simp_rw [hterm]
  simp

theorem refined_sum_active (z : V) (d : Fin 5) :
    (fun y x => ∑ a : Fin 5, refinedKernel z d a y x) = degreeKernel z d := by
  rw [← supportIndexKernel_sum z d]
  funext y x
  unfold refinedKernel
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have hs := disjoint_mask_size_le_four p.val.2 p.val.1 p.property.1
  let active : Fin 5 := ⟨4 - AES.maskSize p.val.2, by omega⟩
  have hselect (a : Fin 5) : AES.maskSize p.val.2 + a.val = 4 ↔ a = active := by
    rw [Fin.ext_iff]
    change AES.maskSize p.val.2 + a.val = 4 ↔ a.val = 4 - AES.maskSize p.val.2
    omega
  simp_rw [hselect]
  simp

def omittedSupport : SupportIndex 0 := ⟨(0,15), by decide⟩

theorem omitted_support_unique : ∀ p : SupportIndex 0,
    AES.maskSize p.val.2 = 4 ↔ p = omittedSupport := by decide

theorem zeroMatrix_tensor (z : V) (y x : Fin 4 → V) :
    (∏ i : Fin 4, zeroMatrix z (y i) (x i)) =
      zeroMatrix (distinguishedState z) y x := by
  by_cases hy : y = distinguishedState z
  · subst y
    by_cases hx : x = distinguishedState z
    · subst x
      simp [zeroMatrix, identityKernel, distinguishedState]
    · have hex : ∃ i, x i ≠ z := by
        by_contra hn
        push Not at hn
        exact hx (funext hn)
      obtain ⟨i, hi⟩ := hex
      simp only [zeroMatrix, identityKernel, hx, if_false, mul_zero]
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
  · have hex : ∃ i, y i ≠ z := by
      by_contra hn
      push Not at hn
      exact hy (funext hn)
    obtain ⟨i, hi⟩ := hex
    simp only [zeroMatrix, identityKernel, hy, if_false, zero_mul]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

theorem refined_zero_zero (z : V) :
    refinedKernel z 0 0 = zeroMatrix (distinguishedState z) := by
  have h0 : AES.maskBit 0 = fun _ : Fin 4 => false := by decide
  have h15 : AES.maskBit 15 = fun _ : Fin 4 => true := by decide
  funext y x
  unfold refinedKernel
  simp only [Fin.val_zero, Nat.add_zero, omitted_support_unique]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  change supportProduct z (AES.maskBit 0) (AES.maskBit 15) y x = _
  rw [h0, h15]
  simpa only [supportProduct, supportPiece, Bool.false_eq_true, if_false, if_true]
    using zeroMatrix_tensor z y x

theorem mask_has_active : ∀ m : Fin 16, AES.maskSize m < 4 →
    ∃ i : Fin 4, AES.maskBit m i = false := by decide

theorem supportPiece_active_zero (z x : V) (marked : Bool) :
    supportPiece z marked false z x = 0 := by
  cases marked <;> by_cases hx : x = z <;>
    simp [supportPiece, residualProjection, constantMatrix, zeroMatrix,
      activityMatrix, identityKernel, hx, eq_comm] <;> exact Ne.symm hx

theorem refined_at_zero (z : V) (d a : Fin 5) (ha : a ≠ 0)
    (x : Fin 4 → V) : refinedKernel z d a (distinguishedState z) x = 0 := by
  unfold refinedKernel
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    have hpos : a.val ≠ 0 := by simpa using ha
    obtain ⟨i, hi⟩ := mask_has_active p.val.2 (by omega)
    unfold supportIndexKernel supportProduct
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change supportPiece z (AES.maskBit p.val.1 i) (AES.maskBit p.val.2 i) z (x i) = 0
    rw [hi]
    exact supportPiece_active_zero z (x i) _
  · simp only [hp, if_false]

/-- The exact active-count indicator, obtained from the existing projection. -/
def activityIndicator (a : Fin 5) : (Fin 4 → V) → ℝ :=
  action (refinedKernel (0 : V) 0 a) (fun _ => 1)

def activityMass (q : ℝ) (a : Fin 5) : ℝ :=
  (Nat.choose 4 a.val : ℝ) * (q-1)^a.val

theorem supportConstant_sq (b : Bool) (x : V) :
    supportConstant b x ^ 2 = supportConstant b x := by
  cases b <;> by_cases hx : x = 0 <;> simp [supportConstant, identityKernel, hx]

theorem supportConstant_sum (b : Bool) :
    (∑ x : V, supportConstant b x) =
      if b then 1 else (Fintype.card V : ℝ)-1 := by
  simpa only [supportConstant_sq] using (supportConstant_energy (V := V) b)

theorem supportDualConstant_sum (hn : 1 < Fintype.card V) (b : Bool) :
    (∑ x : V, supportDualConstant b x) = 1 := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  unfold supportDualConstant
  rw [← Finset.sum_div, supportConstant_sum]
  cases b <;> simp [ne_of_gt (show 0 < (Fintype.card V : ℝ)-1 by linarith)]

theorem unmarked_row_sum (hn : 1 < Fintype.card V) (b : Bool) (y : V) :
    (∑ x : V, supportPiece (0 : V) false b y x) = supportConstant b y := by
  simp_rw [supportPiece_unmarked]
  rw [← Finset.mul_sum, supportDualConstant_sum hn, mul_one]

theorem zero_degree_mask : ∀ p : SupportIndex 0,
    AES.maskBit p.val.1 = (fun _ : Fin 4 => false) := by decide

theorem inactive_complement_count : ∀ r : Fin 16,
    (Finset.univ.filter (fun i : Fin 4 => ¬ AES.maskBit r i = true)).card =
      4-AES.maskSize r := by decide

def supportIndicator (r : Fin 16) (y : Fin 4 → V) : ℝ :=
  ∏ i, supportConstant (AES.maskBit r i) (y i)

theorem supportIndicator_sum (r : Fin 16) :
    (∑ y : Fin 4 → V, supportIndicator r y) =
      ((Fintype.card V : ℝ)-1)^(4-AES.maskSize r) := by
  unfold supportIndicator
  rw [← Fintype.prod_sum (fun i x => supportConstant (AES.maskBit r i) x)]
  simp_rw [supportConstant_sum]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
  rw [inactive_complement_count]

theorem supportIndex_row_sum (hn : 1 < Fintype.card V)
    (p : SupportIndex 0) (y : Fin 4 → V) :
    (∑ x, supportIndexKernel (0 : V) p y x) = supportIndicator p.val.2 y := by
  unfold supportIndexKernel supportProduct
  rw [zero_degree_mask]
  rw [← Fintype.prod_sum (fun i x => supportPiece (0 : V) false (AES.maskBit p.val.2 i) (y i) x)]
  simp_rw [unmarked_row_sum hn]
  rfl

theorem activityIndicator_formula (hn : 1 < Fintype.card V) (a : Fin 5)
    (y : Fin 4 → V) :
    activityIndicator a y =
      ∑ p : SupportIndex 0, if AES.maskSize p.val.2 + a.val = 4 then
        supportIndicator p.val.2 y else 0 := by
  unfold activityIndicator action refinedKernel
  simp only [mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    exact supportIndex_row_sum hn p y
  · simp only [hp, if_false, Finset.sum_const_zero]

/-- Exact counting factor, with no enumeration of alphabet states. -/
theorem activityIndicator_sum (hn : 1 < Fintype.card V) (a : Fin 5) :
    (∑ y : Fin 4 → V, activityIndicator a y) = activityMass (Fintype.card V) a := by
  simp_rw [activityIndicator_formula hn]
  rw [Finset.sum_comm]
  have hselect (p : SupportIndex 0) :
      AES.maskSize p.val.2 + a.val = 4 ↔ supportIndexSize p = a := by
    have hs := supportIndexSize_eq p
    have hb := disjoint_mask_size_le_four p.val.2 p.val.1 p.property.1
    have hz := p.property.2
    constructor
    · intro h
      apply Fin.ext
      omega
    · intro h
      rw [h] at hs
      omega
  have hterm (p : SupportIndex 0) :
      (∑ y : Fin 4 → V, if AES.maskSize p.val.2 + a.val = 4 then
        supportIndicator p.val.2 y else 0) =
      if supportIndexSize p = a then ((Fintype.card V : ℝ)-1)^a.val else 0 := by
    by_cases hp : AES.maskSize p.val.2 + a.val = 4
    · rw [if_pos ((hselect p).mp hp)]
      simp only [hp, if_true]
      rw [supportIndicator_sum]
      congr 1
      omega
    · simp only [hp, if_false, Finset.sum_const_zero,
        if_neg (fun h => hp ((hselect p).mpr h))]
  simp_rw [hterm]
  calc
    _ = ∑ u : Fin 5, (Nat.choose 4 0 * Nat.choose 4 u.val : ℕ) *
        (if u = a then ((Fintype.card V : ℝ)-1)^a.val else 0) :=
      supportIndex_sum_by_size (0 : Fin 5)
        (fun u => if u = a then ((Fintype.card V : ℝ)-1)^a.val else 0)
    _ = _ := by simp [activityMass, mul_ite]

/-- Symmetric idempotence converts the projected-one mass to its energy. -/
theorem activityIndicator_energy (hn : 1 < Fintype.card V) (a : Fin 5) :
    (∑ y : Fin 4 → V, activityIndicator a y ^ 2) =
      activityMass (Fintype.card V) a := by
  have hfix : action (refinedKernel (0 : V) 0 a) (activityIndicator a) =
      activityIndicator a := by
    unfold activityIndicator
    rw [← kernelCompose_action, refined_compose (0 : V) hn]
  calc
    _ = ∑ y : Fin 4 → V,
        (∑ x, refinedKernel (0 : V) 0 a y x) * activityIndicator a y := by
      apply Finset.sum_congr rfl
      intro y _
      simp [activityIndicator, action, pow_two]
    _ = ∑ y : Fin 4 → V, ∑ x,
        refinedKernel (0 : V) 0 a y x * activityIndicator a y := by
      simp_rw [Finset.sum_mul]
    _ = ∑ x : Fin 4 → V, action (refinedKernel (0 : V) 0 a) (activityIndicator a) x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      unfold action
      apply Finset.sum_congr rfl
      intro y _
      rw [refinedKernel_symmetric (0 : V) 0 a y x]
    _ = ∑ x : Fin 4 → V, activityIndicator a x := by rw [hfix]
    _ = _ := activityIndicator_sum hn a

/-- Each unmarked exact-support projection averages on its actual support. -/
theorem supportIndex_zero_rank_one (p : SupportIndex 0) (y x : Fin 4 → V) :
    supportIndexKernel (0 : V) p y x =
      supportIndicator p.val.2 y * supportIndicator p.val.2 x /
        ((Fintype.card V : ℝ)-1)^(4-AES.maskSize p.val.2) := by
  have hden : (∏ i : Fin 4, if AES.maskBit p.val.2 i then (1 : ℝ)
      else (Fintype.card V : ℝ)-1) =
      ((Fintype.card V : ℝ)-1)^(4-AES.maskSize p.val.2) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    rw [inactive_complement_count]
  unfold supportIndexKernel supportProduct
  rw [zero_degree_mask]
  simp_rw [supportPiece_unmarked, supportDualConstant]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, hden]
  change supportIndicator p.val.2 y *
      (supportIndicator p.val.2 x / ((Fintype.card V : ℝ)-1)^(4-AES.maskSize p.val.2)) = _
  ring

/-- All selected masks have the same exact support averaging denominator. -/
theorem refined_activity_kernel (a : Fin 5) (y x : Fin 4 → V) :
    refinedKernel (0 : V) 0 a y x =
      ∑ p : SupportIndex 0, if AES.maskSize p.val.2 + a.val = 4 then
        supportIndicator p.val.2 y * supportIndicator p.val.2 x /
          ((Fintype.card V : ℝ)-1)^a.val else 0 := by
  unfold refinedKernel
  change (∑ p : SupportIndex 0, if AES.maskSize p.val.2 + a.val = 4 then
      supportIndexKernel (0 : V) p y x else 0) =
    ∑ p : SupportIndex 0, if AES.maskSize p.val.2 + a.val = 4 then
      supportIndicator p.val.2 y * supportIndicator p.val.2 x /
        ((Fintype.card V : ℝ)-1)^a.val else 0
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : AES.maskSize p.val.2 + a.val = 4
  · simp only [hp, if_true]
    have hexp : 4-AES.maskSize p.val.2 = a.val := by omega
    simpa only [hexp] using (supportIndex_zero_rank_one (V := V) p y x)
  · simp only [hp, if_false]

theorem support_graph_sum (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 16) (a b : Fin 5)
    (ha : AES.maskSize r + a.val = 4) (hb : AES.maskSize s + b.val = 4) :
    (∑ z, supportIndicator r (L z) * supportIndicator s z) =
      supportCount (Fintype.card V) (a.val+b.val) := by
  simpa only [supportIndicator, ActivityMDSCounts.supportWeight] using
    ActivityMDSCounts.supportWeight_graph_sum_of_active_sizes L hL r s a b ha hb

/-- The diffusion sandwich is computed from exact graph-support counts. -/
theorem diffusion_activity_rank_one (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (a b : Fin 5) :
    kernelCompose (fun y z => refinedKernel (0 : V) 0 a y (L z))
      (refinedKernel (0 : V) 0 b) =
      fun y x => supportCount (Fintype.card V) (a.val+b.val) /
        ((Fintype.card V : ℝ)-1)^(a.val+b.val) *
          activityIndicator a y * activityIndicator b x := by
  funext y x
  let c : ℝ := supportCount (Fintype.card V) (a.val+b.val) /
    ((Fintype.card V : ℝ)-1)^(a.val+b.val)
  have hpair (p q : SupportIndex 0) :
      (∑ z : Fin 4 → V,
        (if AES.maskSize p.val.2 + a.val = 4 then
          supportIndicator p.val.2 y * supportIndicator p.val.2 (L z) /
            ((Fintype.card V : ℝ)-1)^a.val else 0) *
        (if AES.maskSize q.val.2 + b.val = 4 then
          supportIndicator q.val.2 z * supportIndicator q.val.2 x /
            ((Fintype.card V : ℝ)-1)^b.val else 0)) =
        c * (if AES.maskSize p.val.2 + a.val = 4 then supportIndicator p.val.2 y else 0) *
          (if AES.maskSize q.val.2 + b.val = 4 then supportIndicator q.val.2 x else 0) := by
    by_cases hp : AES.maskSize p.val.2 + a.val = 4
    · by_cases hq : AES.maskSize q.val.2 + b.val = 4
      · simp only [hp, hq, if_true]
        calc
          _ = (supportIndicator p.val.2 y * supportIndicator q.val.2 x /
              ((Fintype.card V : ℝ)-1)^(a.val+b.val)) *
              ∑ z, supportIndicator p.val.2 (L z) * supportIndicator q.val.2 z := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            rw [pow_add]
            ring
          _ = _ := by
            rw [support_graph_sum L hL p.val.2 q.val.2 a b hp hq]
            dsimp [c]
            ring
      · simp [hp, hq]
    · simp [hp]
  change (∑ z, refinedKernel (0 : V) 0 a y (L z) *
    refinedKernel (0 : V) 0 b z x) = _
  simp_rw [refined_activity_kernel, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ p : SupportIndex 0, ∑ q : SupportIndex 0,
        c * (if AES.maskSize p.val.2 + a.val = 4 then supportIndicator p.val.2 y else 0) *
          (if AES.maskSize q.val.2 + b.val = 4 then supportIndicator q.val.2 x else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      exact hpair p q
    _ = c * (∑ p : SupportIndex 0,
        if AES.maskSize p.val.2 + a.val = 4 then supportIndicator p.val.2 y else 0) *
        (∑ q : SupportIndex 0,
        if AES.maskSize q.val.2 + b.val = 4 then supportIndicator q.val.2 x else 0) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      rw [← activityIndicator_formula hn a,
        ← activityIndicator_formula hn b]


theorem refined_cross_compose (hn : 1 < Fintype.card V) (a b : Fin 5) (hab : a ≠ b) :
    kernelCompose (refinedKernel (0 : V) 0 a) (refinedKernel (0 : V) 0 b) = 0 := by
  funext y x
  have hterm (p q : SupportIndex 0) :
      (∑ v : Fin 4 → V,
        (if AES.maskSize p.val.2 + a.val = 4 then supportIndexKernel (0 : V) p y v else 0) *
        (if AES.maskSize q.val.2 + b.val = 4 then supportIndexKernel (0 : V) q v x else 0)) = 0 := by
    by_cases hp : AES.maskSize p.val.2 + a.val = 4
    · by_cases hq : AES.maskSize q.val.2 + b.val = 4
      · have hpq : p ≠ q := by
          intro he
          subst q
          apply hab
          apply Fin.ext
          omega
        simp only [hp, hq, if_true]
        change kernelCompose (supportIndexKernel (0 : V) p)
          (supportIndexKernel (0 : V) q) y x = 0
        rw [supportIndexKernel_compose (0 : V) hn, if_neg hpq]
        rfl
      · simp [hq]
    · simp [hp]
  unfold kernelCompose refinedKernel
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro q _
  exact hterm q p

/-- The indicator Gram comes from the actual orthogonal support projections. -/
theorem activityIndicator_gram (hn : 1 < Fintype.card V) (a b : Fin 5) :
    (∑ y : Fin 4 → V, activityIndicator a y * activityIndicator b y) =
      if a = b then activityMass (Fintype.card V) a else 0 := by
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    simpa only [pow_two] using activityIndicator_energy hn a
  · rw [if_neg hab]
    unfold activityIndicator
    rw [kernel_bilinear]
    have hc (x w : Fin 4 → V) :
        (∑ y, refinedKernel (0 : V) 0 a y x * refinedKernel (0 : V) 0 b y w) = 0 := by
      simp_rw [refinedKernel_symmetric (0 : V) 0 a _ x]
      change kernelCompose (refinedKernel (0 : V) 0 a) (refinedKernel (0 : V) 0 b) x w = 0
      rw [refined_cross_compose hn a b hab]
      rfl
    simp_rw [hc, mul_zero, Finset.sum_const_zero]

theorem activityIndicator_zero (y : Fin 4 → V) :
    activityIndicator (0 : Fin 5) y = identityKernel y 0 := by
  unfold activityIndicator
  rw [refined_zero_zero, zeroMatrix_action]
  have hz : distinguishedState (0 : V) = (0 : Fin 4 → V) := rfl
  simp only [zeroPart, hz, identityKernel]

theorem activityIndicator_at_zero (a : Fin 5) (ha : a ≠ 0) :
    activityIndicator a (0 : Fin 4 → V) = 0 := by
  unfold activityIndicator action
  apply Finset.sum_eq_zero
  intro x _
  have h := refined_at_zero (0 : V) 0 a ha x
  have hz : distinguishedState (0 : V) = (0 : Fin 4 → V) := rfl
  simpa only [hz, mul_one] using h

theorem activityIndicator_partition (hn : 1 < Fintype.card V) (y : Fin 4 → V) :
    (∑ a : Fin 5, activityIndicator a y) = 1 := by
  have hp := (degree_zero_pointed (0 : V) hn).row_sum y
  calc
    _ = ∑ x : Fin 4 → V, ∑ a : Fin 5, refinedKernel (0 : V) 0 a y x := by
      simp only [activityIndicator, action, mul_one]
      exact Finset.sum_comm
    _ = ∑ x : Fin 4 → V, degreeKernel (0 : V) 0 y x := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrFun (congrFun (refined_sum_active (0 : V) 0) y) x
    _ = 1 := hp

theorem activityIndicator_positive_partition (hn : 1 < Fintype.card V)
    (y : Fin 4 → V) :
    (∑ a : Fin 4, activityIndicator a.succ y) = if y = 0 then 0 else 1 := by
  have h := activityIndicator_partition hn y
  rw [Fin.sum_univ_succ, activityIndicator_zero] at h
  by_cases hy : y = 0
  · simp only [identityKernel, hy, if_true] at h ⊢
    linarith
  · simp only [identityKernel, hy, if_false] at h ⊢
    linarith

theorem activityMass_positive (hn : 1 < Fintype.card V) (a : Fin 4) :
    0 < activityMass (Fintype.card V) a.succ := by
  have hq : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hQ : 0 < (Fintype.card V : ℝ)-1 := sub_pos.mpr hq
  unfold activityMass
  apply mul_pos
  · have hc : 0 < Nat.choose 4 a.succ.val := by fin_cases a <;> decide
    exact_mod_cast hc
  · exact pow_pos hQ _

def normalizedIndicator (a : Fin 4) (y : Fin 4 → V) : ℝ :=
  activityIndicator a.succ y / Real.sqrt (activityMass (Fintype.card V) a.succ)

/-- Exactly the orthonormality interface required by the finite matrix lift. -/
theorem normalizedIndicator_gram (hn : 1 < Fintype.card V) (a b : Fin 4) :
    (∑ x : Fin 4 → V, normalizedIndicator a x * normalizedIndicator b x) =
      if a = b then 1 else 0 := by
  simp only [normalizedIndicator, div_mul_div_comm, ← Finset.sum_div]
  rw [activityIndicator_gram hn a.succ b.succ]
  by_cases hab : a = b
  · subst b
    simp only [if_true]
    rw [Real.mul_self_sqrt (activityMass_positive hn a).le]
    exact div_self (ne_of_gt (activityMass_positive hn a))
  · have hs : a.succ ≠ b.succ := by
      intro h
      apply hab
      apply Fin.ext
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ] at hv
      omega
    simp only [hab, hs, if_false, zero_div]

/-- The scalar centered coefficient in the four-weight compression. -/
def activityCoefficient (q : ℝ) (a b : Fin 5) : ℝ :=
  supportCount q (a.val+b.val) / (q-1)^(a.val+b.val) - 1/(q^4-1)

/-- Full activity sandwich for forward execution by L; laws use L inverse. -/
def rawKernel (L : (Fin 4 → V) →+ (Fin 4 → V)) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  kernelCompose (fun y z => degreeKernel (0 : V) 0 y (L z))
    (degreeKernel (0 : V) 0)

/-- Generic transport keeps the input function opaque while checking the
permutation change of variables. Specialize only after this proof is checked. -/
theorem kernel_equiv_transport {W : Type*} [Fintype W]
    (e : Equiv.Perm W) (K : W → W → ℝ) (g : W → ℝ) :
    action (fun y z => K y (e z)) g = action K (fun x => g (e.symm x)) := by
  funext y
  change (∑ z, K y (e z) * g z) = ∑ x, K y x * g (e.symm x)
  simpa only [Equiv.symm_apply_apply] using
    Equiv.sum_comp e (fun x => K y x * g (e.symm x))

/-- This is the actual degree-zero diffusion transfer, in law orientation. -/
theorem rawKernel_action (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (f : (Fin 4 → V) → ℝ) :
    action (rawKernel L.toAddMonoidHom) f =
      degreeComponent (0 : V) 0
        (fun x => degreeComponent (0 : V) 0 f (L.symm x)) := by
  rw [rawKernel, kernelCompose_action, degreeKernel_action]
  -- Editorial: do not ask simp to identify AddEquiv and Equiv inverse
  -- coercions underneath the degree projection; use an explicit input equality.
  have ht := kernel_equiv_transport L.toEquiv (degreeKernel (0 : V) 0)
    (degreeComponent (0 : V) 0 f)
  have hi :
      (fun x => degreeComponent (0 : V) 0 f (L.toEquiv.symm x)) =
      (fun x => degreeComponent (0 : V) 0 f (L.symm x)) := by
    funext x
    exact congrArg (degreeComponent (0 : V) 0 f)
      (rfl : L.toEquiv.symm x = L.symm x)
  have ho :
      action (degreeKernel (0 : V) 0)
        (fun x => degreeComponent (0 : V) 0 f (L.toEquiv.symm x)) =
      action (degreeKernel (0 : V) 0)
        (fun x => degreeComponent (0 : V) 0 f (L.symm x)) :=
    congrArg (action (degreeKernel (0 : V) 0)) hi
  have hp := degreeKernel_action (0 : V) 0
    (fun x => degreeComponent (0 : V) 0 f (L.symm x))
  exact ht.trans (ho.trans hp)

/-- Exact five-weight kernel, including the distinguished zero-state cell. -/
theorem rawKernel_formula (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (y x : Fin 4 → V) :
    rawKernel L y x = ∑ a : Fin 5, ∑ b : Fin 5,
      supportCount (Fintype.card V) (a.val+b.val) /
        ((Fintype.card V : ℝ)-1)^(a.val+b.val) *
          activityIndicator a y * activityIndicator b x := by
  have hd (u v : Fin 4 → V) : degreeKernel (0 : V) 0 u v =
      ∑ a : Fin 5, refinedKernel (0 : V) 0 a u v :=
    (congrFun (congrFun (refined_sum_active (0 : V) 0) u) v).symm
  unfold rawKernel kernelCompose
  simp_rw [hd, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact congrFun (congrFun (diffusion_activity_rank_one hn L hL a b) y) x

/-- Isolate the unique zero-state cell before global nonzero centering. -/
theorem rawKernel_positive_formula (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (y x : Fin 4 → V) :
    rawKernel L y x = zeroMatrix (0 : Fin 4 → V) y x +
      ∑ a : Fin 4, ∑ b : Fin 4,
        supportCount (Fintype.card V) (a.succ.val+b.succ.val) /
          ((Fintype.card V : ℝ)-1)^(a.succ.val+b.succ.val) *
            activityIndicator a.succ y * activityIndicator b.succ x := by
  have hs (a : Fin 4) : supportCount (Fintype.card V) a.succ.val = 0 :=
    supportCount_small _ a.succ (by simp)
  rw [rawKernel_formula hn L hL, Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Nat.zero_add, Nat.add_zero,
    supportCount_zero, pow_zero, div_one, one_mul, hs, zero_div, zero_mul,
    Finset.sum_const_zero, zero_add, add_zero, activityIndicator_zero, zeroMatrix]

theorem globalUniformKernel_indicator (hn : 1 < Fintype.card V) (y x : Fin 4 → V) :
    globalUniformKernel (0 : V) y x =
      (∑ a : Fin 4, activityIndicator a.succ y) *
        (∑ b : Fin 4, activityIndicator b.succ x) / ((Fintype.card V : ℝ)^4-1) := by
  rw [activityIndicator_positive_partition hn y, activityIndicator_positive_partition hn x]
  have hz : distinguishedState (0 : V) = (0 : Fin 4 → V) := rfl
  by_cases hy : y = 0 <;> by_cases hx : x = 0 <;>
    simp [globalUniformKernel, hz, hy, hx, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]

/-- Remove both stationary directions on the full counting-measure space. -/
def centeredKernel (L : (Fin 4 → V) →+ (Fin 4 → V)) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  rawKernel L - zeroMatrix (0 : Fin 4 → V) - globalUniformKernel (0 : V)

/-- The actual centered activity kernel has exactly four support weights. -/
theorem centeredKernel_formula (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (y x : Fin 4 → V) :
    centeredKernel L y x = ∑ a : Fin 4, ∑ b : Fin 4,
      activityCoefficient (Fintype.card V) a.succ b.succ *
        activityIndicator a.succ y * activityIndicator b.succ x := by
  have hu :
      (∑ a : Fin 4, activityIndicator a.succ y) *
        (∑ b : Fin 4, activityIndicator b.succ x) / ((Fintype.card V : ℝ)^4-1) =
      ∑ a : Fin 4, ∑ b : Fin 4,
        (1 / ((Fintype.card V : ℝ)^4-1)) *
          activityIndicator a.succ y * activityIndicator b.succ x := by
    -- Keep the output weight outermost; applying both product rules in one
    -- simp pass chooses the opposite summation order.
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  unfold centeredKernel
  change rawKernel L y x - zeroMatrix (0 : Fin 4 → V) y x -
    globalUniformKernel (0 : V) y x = _
  rw [rawKernel_positive_formula hn L hL, add_sub_cancel_left,
    globalUniformKernel_indicator hn, hu, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  unfold activityCoefficient
  ring

/-- Both removed kernels annihilate a centered input; this is a proved
identity for the actual diffusion transfer, not a new analytic premise. -/
theorem centeredKernel_action (L : (Fin 4 → V) ≃+ (Fin 4 → V))
    (f : (Fin 4 → V) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    action (centeredKernel L.toAddMonoidHom) f =
      degreeComponent (0 : V) 0
        (fun x => degreeComponent (0 : V) 0 f (L.symm x)) := by
  have hzero : zeroPart (0 : Fin 4 → V) f = 0 := by
    funext x
    simp [zeroPart, hz]
  have hu : action (globalUniformKernel (0 : V)) f = 0 :=
    AESConcrete.DegreeCentering.globalUniformKernel_action_eq_zero (0 : V) f hz hs
  rw [centeredKernel, kernel_action_sub, kernel_action_sub, zeroMatrix_action,
    hzero, hu, sub_zero, sub_zero, rawKernel_action]

theorem normalized_kernel_term (hn : 1 < Fintype.card V) (a b : Fin 4)
    (y x : Fin 4 → V) :
    activityCoefficient (Fintype.card V) a.succ b.succ *
        activityIndicator a.succ y * activityIndicator b.succ x =
      (activityCoefficient (Fintype.card V) a.succ b.succ *
        Real.sqrt (activityMass (Fintype.card V) a.succ *
          activityMass (Fintype.card V) b.succ)) *
            normalizedIndicator a y * normalizedIndicator b x := by
  have ha := ne_of_gt (Real.sqrt_pos.2 (activityMass_positive hn a))
  have hb := ne_of_gt (Real.sqrt_pos.2 (activityMass_positive hn b))
  unfold normalizedIndicator
  rw [Real.sqrt_mul (activityMass_positive hn a).le]
  field_simp [ha, hb]

/-- The finite Euclidean matrix uses orthonormalized actual indicators. -/
theorem centeredKernel_normalized_formula (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (y x : Fin 4 → V) :
    centeredKernel L y x = ∑ a : Fin 4, ∑ b : Fin 4,
      (activityCoefficient (Fintype.card V) a.succ b.succ *
        Real.sqrt (activityMass (Fintype.card V) a.succ *
          activityMass (Fintype.card V) b.succ)) *
            normalizedIndicator a y * normalizedIndicator b x := by
  rw [centeredKernel_formula hn L hL]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact normalized_kernel_term hn a b y x

/-- The exact boundary fixed by the physical grouped-law recurrence. -/
def aesKernel : AES.WordState → AES.WordState → ℝ :=
  centeredKernel AESPaper.GroupedRecurrence.boundary.toAddMonoidHom

theorem aesBoundary_zeroMDS : ZeroMDS AESPaper.GroupedRecurrence.boundary := by
  rw [AESPaper.BoundaryZeros.boundary_eq_wordMixAddEquiv]
  exact AESConcrete.WordCrossZero.wordMixAddEquiv_zeroMDS

/-- The concrete centered kernel acts as P0 Pi P0 on the same word space. -/
theorem aesKernel_action (f : AESPaper.ProfileSpace.State)
    (hf : AESPaper.ProfileSpace.Centered f) :
    action aesKernel (fun x => f x) =
      degreeComponent (0 : AES.Word) 0
        (AESPaper.GroupedRecurrence.Pi (degreeComponent (0 : AES.Word) 0 (fun x => f x))) := by
  have h := centeredKernel_action AESPaper.GroupedRecurrence.boundary
    (fun x => f x) hf.1 hf.2
  have hp :
      (fun x => degreeComponent (0 : AES.Word) 0 (fun y => f y)
        (AESPaper.GroupedRecurrence.boundary.symm x)) =
      AESPaper.GroupedRecurrence.Pi (degreeComponent (0 : AES.Word) 0 (fun y => f y)) := rfl
  exact h.trans (congrArg (degreeComponent (0 : AES.Word) 0) hp)

theorem aesKernel_normalized_formula (y x : AES.WordState) :
    aesKernel y x = ∑ a : Fin 4, ∑ b : Fin 4,
      (activityCoefficient ((2 : ℝ)^32) a.succ b.succ *
        Real.sqrt (activityMass ((2 : ℝ)^32) a.succ *
          activityMass ((2 : ℝ)^32) b.succ)) *
            normalizedIndicator a y * normalizedIndicator b x := by
  simpa only [aesKernel, AES.word_card, Nat.cast_pow, Nat.cast_ofNat] using
    centeredKernel_normalized_formula AESPaper.ProfileSpace.word_card_gt_one
      AESPaper.GroupedRecurrence.boundary.toAddMonoidHom aesBoundary_zeroMDS y x

end AESPaper.ActivityKernel
