/- Module role: Symbolic two-step contraction, actual memory assembly and explicit remaining interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Estimates.Source.Startup
import AES8.Recurrence.SupportEvolution
import AES8.Reductions.Support.TransferZeros
import AESConcrete.DegreeCentering
import AESMixing.DegreeMatrixNorm
import Mathlib.Tactic.FieldSimp

/-!
# Assembly of centered physical block caps

`PhysicalCaps` asks for individual counting-norm bounds for the centered
physical word step, the two-step high return, and the first high remainder.
The coefficients are obtained from the existing `L` and `M` on coordinate
basis vectors; their numerical tables are not copied into another interface.
`physicalCoeff r i j b` includes precisely `omega41^r * d i / d j`.

The centering correction must remain on separate activity components.
It vanishes on complete actual errors, and on the complete low/high parts
used in `SupportEvolution.actual_memory`.  Thus the assembly retains the
actual `H Pi` evolution and the intermediate high projection.  It does not
postulate either target profile recurrence.

The conclusion is conditional on `PhysicalCaps`.  No numerical cap witness,
old/new projection-mask bridge, or Hilbert/counting-norm bridge is supplied
here.  In particular, this module does not discharge the AES transfer
estimates or the final AES mixing theorem.  Constructive proofs only;
no attacks, predecessor edits, or manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000
set_option linter.constructorNameAsVariable false

noncomputable section
open scoped BigOperators

namespace AES8.TransferAssembly
open AESMixing AESMixing.AES
open AESPaper.GroupedLaw (error)
open AESPaper.GroupedRecurrence (step)
open AES8.SupportEvolution (lowPart highPart)

section ComponentAlgebra

/-- Support components commute with finite sums of arbitrary joint functions. -/
theorem component_sum {J : Type*} [Fintype J]
    (f : J → WordState → ℝ) (c : Fin 14) :
    SupportProfile.component (fun x => ∑ j, f j x) c =
      fun x => ∑ j, SupportProfile.component (f j) c x := by
  funext x
  have hraw (p : SupportProfile.Label) :
      SupportProfile.raw p (fun y => ∑ j, f j y) x =
        ∑ j, SupportProfile.raw p (f j) x :=
    congrFun (action_sum_family
      (supportProduct (0 : AES.Word) (maskBit p.1) (maskBit p.2)) f) x
  change (∑ p : SupportProfile.Label, if SupportProfile.coord p = c.succ then
      SupportProfile.raw p (fun y => ∑ j, f j y) x else 0) =
    ∑ j, ∑ p : SupportProfile.Label, if SupportProfile.coord p = c.succ then
      SupportProfile.raw p (f j) x else 0
  simp_rw [hraw]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : SupportProfile.coord p = c.succ <;>
    simp only [hp, if_true, if_false, Finset.sum_const_zero]

theorem component_add (f g : WordState → ℝ) (c : Fin 14) :
    SupportProfile.component (f + g) c =
      SupportProfile.component f c + SupportProfile.component g c := by
  funext x
  have hraw (p : SupportProfile.Label) :
      SupportProfile.raw p (f + g) x =
        SupportProfile.raw p f x + SupportProfile.raw p g x := by
    unfold SupportProfile.raw action
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  change (∑ p : SupportProfile.Label, if SupportProfile.coord p = c.succ then
      SupportProfile.raw p (f + g) x else 0) =
    (∑ p : SupportProfile.Label, if SupportProfile.coord p = c.succ then
      SupportProfile.raw p f x else 0) +
    ∑ p : SupportProfile.Label, if SupportProfile.coord p = c.succ then
      SupportProfile.raw p g x else 0
  simp_rw [hraw]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : SupportProfile.coord p = c.succ <;>
    simp only [hp, if_true, if_false, zero_add]

/-- The componentwise finite triangle inequality uses the existing counting norm. -/
theorem profile_sum_le {J : Type*} [Fintype J]
    (f : J → WordState → ℝ) (i : Fin 14) :
    SupportProfile.profile (fun x => ∑ j, f j x) i ≤
      ∑ j, SupportProfile.profile (f j) i := by
  classical
  unfold SupportProfile.profile
  rw [component_sum]
  exact l2_finset_sum_le Finset.univ (fun j => SupportProfile.component (f j) i)

theorem profile_add_le (f g : WordState → ℝ) (i : Fin 14) :
    SupportProfile.profile (f + g) i ≤
      SupportProfile.profile f i + SupportProfile.profile g i := by
  unfold SupportProfile.profile
  rw [component_add]
  exact l2_add_le _ _

theorem highPart_family {J : Type*} [Fintype J] (f : J → WordState → ℝ) :
    highPart (fun x => ∑ j, f j x) = fun x => ∑ j, highPart (f j) x := by
  funext x
  unfold highPart
  simp only [component_sum]
  exact Finset.sum_comm

end ComponentAlgebra

section Centering

/-- Action adapter for the physical word step minus the global uniform kernel.
The old centered kernel has this exact expression; no raw activity cap is used. -/
def centeredStep (f : WordState → ℝ) : WordState → ℝ :=
  action (AESConcrete.WordStepZeros.wordStepKernel -
    AESConcrete.DegreeCentering.globalUniformKernel (0 : AES.Word)) f

theorem centeredStep_formula (f : WordState → ℝ) :
    centeredStep f = step f -
      action (AESConcrete.DegreeCentering.globalUniformKernel (0 : AES.Word)) f := by
  unfold centeredStep
  rw [kernel_action_sub]
  change TransferZeros.physicalWordStep f - _ = _
  rw [TransferZeros.physicalWordStep_eq_step]

/-- Only complete zero-extended, zero-mass vectors lose the correction here. -/
theorem centeredStep_eq_step (f : WordState → ℝ) (hz : f 0 = 0)
    (hs : (∑ x, f x) = 0) : centeredStep f = step f := by
  have hg := AESConcrete.DegreeCentering.globalUniformKernel_action_eq_zero
    (0 : AES.Word) f (by exact hz) hs
  rw [centeredStep_formula, hg, sub_zero]

theorem centeredStep_add (f g : WordState → ℝ) :
    centeredStep (f + g) = centeredStep f + centeredStep g := by
  have h := action_sub
    (AESConcrete.WordStepZeros.wordStepKernel -
      AESConcrete.DegreeCentering.globalUniformKernel (0 : AES.Word)) (f + g) g
  rw [add_sub_cancel_right] at h
  exact sub_eq_iff_eq_add.mp h.symm

theorem centeredStep_sum {J : Type*} [Fintype J] (f : J → WordState → ℝ) :
    centeredStep (fun x => ∑ j, f j x) = fun x => ∑ j, centeredStep (f j) x :=
  action_sum_family _ f

theorem lowPart_zero (f : WordState → ℝ) : lowPart f 0 = 0 := by
  simp only [lowPart, SupportProfile.component_at_zero, Finset.sum_const_zero]

theorem highPart_zero (f : WordState → ℝ) : highPart f 0 = 0 := by
  simp only [highPart, SupportProfile.component_at_zero, Finset.sum_const_zero]

/-- Positive residual degree forces each of the three high components to have zero mass. -/
theorem highPart_mass (f : WordState → ℝ) : (∑ x, highPart f x) = 0 := by
  unfold highPart
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro c _
  have hc : SupportDegree.degree (Fin.natAdd 11 c) ≠ 0 := by
    intro he
    have hv := congrArg Fin.val he
    change SupportProfile.residualDegree (Fin.natAdd 11 c) = 0 at hv
    have hd := SupportEvolution.high_degree c
    omega
  have hm := AESConcrete.DegreeCentering.degreeComponent_sum_zero
    (0 : AES.Word) SupportProfile.word_card_gt_one
    (SupportDegree.degree (Fin.natAdd 11 c)) hc
    (SupportProfile.component f (Fin.natAdd 11 c))
  rw [TransferZeros.degree_component] at hm
  exact hm

theorem lowPart_mass (f : WordState → ℝ) (hz : f 0 = 0)
    (hs : (∑ x, f x) = 0) : (∑ x, lowPart f x) = 0 := by
  have he := congrArg (fun v : WordState → ℝ => ∑ x, v x)
    (SupportEvolution.split f hz)
  simp only [Pi.add_apply, Finset.sum_add_distrib] at he
  rw [hs, highPart_mass] at he
  linarith

theorem centeredStep_low_eq_step (f : WordState → ℝ) (hz : f 0 = 0)
    (hs : (∑ x, f x) = 0) : centeredStep (lowPart f) = step (lowPart f) :=
  centeredStep_eq_step _ (lowPart_zero f) (lowPart_mass f hz hs)

theorem centeredStep_high_eq_step (f : WordState → ℝ) :
    centeredStep (highPart f) = step (highPart f) :=
  centeredStep_eq_step _ (highPart_zero f) (highPart_mass f)

/-- The intermediate high projection remains between the two centered physical steps. -/
def highReturn (f : WordState → ℝ) : WordState → ℝ :=
  centeredStep (highPart (centeredStep f))

theorem highReturn_sum {J : Type*} [Fintype J] (f : J → WordState → ℝ) :
    highReturn (fun x => ∑ j, f j x) = fun x => ∑ j, highReturn (f j) x := by
  unfold highReturn
  rw [centeredStep_sum, highPart_family, centeredStep_sum]

/-- This is the existing physical memory identity with its justified centering adapter. -/
theorem centered_actual_memory (j : ℕ) (a : AES.State) (ha : a ≠ 0) :
    error (j + 3) a = centeredStep (lowPart (error (j + 2) a)) +
      highReturn (error (j + 1) a) := by
  rw [SupportEvolution.actual_memory j a ha]
  unfold highReturn
  rw [centeredStep_low_eq_step _ (AESPaper.GroupedLaw.error_zero _ a ha)
      (AESPaper.GroupedLaw.error_sum _ a), centeredStep_high_eq_step,
    centeredStep_eq_step _ (AESPaper.GroupedLaw.error_zero _ a ha)
      (AESPaper.GroupedLaw.error_sum _ a)]

theorem centered_actual_first (a : AES.State) (ha : a ≠ 0) :
    error 2 a = centeredStep (lowPart (error 1 a)) +
      centeredStep (highPart (error 1 a)) := by
  rw [AESPaper.GroupedRecurrence.error_step 1 a,
    SupportEvolution.step_split _ (AESPaper.GroupedLaw.error_zero 1 a ha)]
  rw [centeredStep_low_eq_step _ (AESPaper.GroupedLaw.error_zero 1 a ha)
      (AESPaper.GroupedLaw.error_sum 1 a), centeredStep_high_eq_step]

end Centering

section ComparisonCoefficients

/-- Coordinate basis for the existing fourteen-dimensional comparison maps. -/
def basis (j : Fin 14) : Profile := fun i => if i = j then 1 else 0

private theorem L_add (x y : Profile) : L (x + y) = L x + L y := by
  have hs : lowSum (x + y) = lowSum x + lowSum y := by
    simp only [lowSum, Pi.add_apply, Finset.sum_add_distrib]
  funext i
  fin_cases i <;> simp only [L, L0, vec14_apply, Pi.add_apply, hs] <;> ring

private theorem M_add (x y : Profile) : M (x + y) = M x + M y := by
  have hs : allSum (x + y) = allSum x + allSum y := by
    simp only [allSum, Pi.add_apply, Finset.sum_add_distrib]
  funext i
  fin_cases i <;> simp only [M, M0, vec14_apply, Pi.add_apply, hs] <;> ring

private theorem comparison_expansion (T : Profile → Profile)
    (hadd : ∀ x y, T (x + y) = T x + T y)
    (hscale : ∀ a x, T (scale a x) = scale a (T x))
    (v : Profile) (i : Fin 14) :
    T v i = ∑ j : Fin 14, T (basis j) i * v j := by
  let Tlin : Profile →ₗ[ℝ] Profile := {
    toFun := T
    map_add' := hadd
    map_smul' := hscale
  }
  have hb : (∑ j : Fin 14, (v j) • basis j) = v := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basis,
      mul_ite, _root_.mul_one, mul_zero]
    simp
  have he := congrFun
    (map_sum Tlin (fun j : Fin 14 => (v j) • basis j) Finset.univ) i
  rw [hb] at he
  have h : T v i = ∑ j : Fin 14, v j * T (basis j) i := by
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
    change T v i = ∑ j : Fin 14, v j * T (basis j) i at he
    exact he
  exact h.trans (Finset.sum_congr rfl (fun j _ => _root_.mul_comm _ _))

/-- Low input columns of the authoritative `L`. -/
def lowCoeff (i : Fin 14) (j : Fin 11) : ℝ := L (basis (Fin.castAdd 3 j)) i

/-- All input columns of the authoritative `M`. -/
def returnCoeff (i j : Fin 14) : ℝ := M (basis j) i

private theorem L_high_basis (j : Fin 3) (i : Fin 14) :
    L (basis (Fin.natAdd 11 j)) i = 0 := by
  have hz (c : Fin 11) : basis (Fin.natAdd 11 j) (Fin.castAdd 3 c) = 0 := by
    unfold basis
    apply if_neg
    intro he
    have hv := congrArg Fin.val he
    change c.val = 11 + j.val at hv
    omega
  have hs : lowSum (basis (Fin.natAdd 11 j)) = 0 :=
    Finset.sum_eq_zero (fun c _ => hz c)
  -- Match the numeral indices used by L0, rather than retaining castAdd syntax.
  have h0 : basis (Fin.natAdd 11 j) (0 : Fin 14) = 0 := hz 0
  have h1 : basis (Fin.natAdd 11 j) (1 : Fin 14) = 0 := hz 1
  have h2 : basis (Fin.natAdd 11 j) (2 : Fin 14) = 0 := hz 2
  have h3 : basis (Fin.natAdd 11 j) (3 : Fin 14) = 0 := hz 3
  have h4 : basis (Fin.natAdd 11 j) (4 : Fin 14) = 0 := hz 4
  have h5 : basis (Fin.natAdd 11 j) (5 : Fin 14) = 0 := hz 5
  have h6 : basis (Fin.natAdd 11 j) (6 : Fin 14) = 0 := hz 6
  have h7 : basis (Fin.natAdd 11 j) (7 : Fin 14) = 0 := hz 7
  have h8 : basis (Fin.natAdd 11 j) (8 : Fin 14) = 0 := hz 8
  have h9 : basis (Fin.natAdd 11 j) (9 : Fin 14) = 0 := hz 9
  have h10 : basis (Fin.natAdd 11 j) (10 : Fin 14) = 0 := hz 10
  fin_cases i <;>
    simp only [L, L0, vec14_apply, hs, h0, h1, h2, h3, h4, h5, h6, h7, h8,
      h9, h10] <;> ring

theorem L_low_expansion (v : Profile) (i : Fin 14) :
    L v i = ∑ j : Fin 11, lowCoeff i j * v (Fin.castAdd 3 j) := by
  have he := comparison_expansion L L_add L_scale v i
  rw [Fin.sum_univ_add (a := 11) (b := 3)
    (fun j : Fin 14 => L (basis j) i * v j)] at he
  simpa only [L_high_basis, zero_mul, Finset.sum_const_zero, add_zero, lowCoeff]
    using he

theorem M_expansion (v : Profile) (i : Fin 14) :
    M v i = ∑ j : Fin 14, returnCoeff i j * v j :=
  comparison_expansion M M_add M_scale v i

/-- A normalized comparison entry expressed in physical counting-norm units. -/
def physicalCoeff (r : ℕ) (i j : Fin 14) (b : ℝ) : ℝ :=
  omega41 ^ r * d i / d j * b

theorem factor_shift (j r : ℕ) :
    NormalizedProfile.factor (j + r) * omega41 ^ r = NormalizedProfile.factor j := by
  have hj : omega41 ^ j ≠ 0 := (pow_pos omega41_pos j).ne'
  have hr : omega41 ^ r ≠ 0 := (pow_pos omega41_pos r).ne'
  unfold NormalizedProfile.factor
  rw [pow_add]
  field_simp [hj, hr] <;> ring

/-- Exact coefficient conversion; no operator inequality is assumed. -/
theorem normalized_coefficient (j r : ℕ) (i k : Fin 14) (b x : ℝ) :
    (NormalizedProfile.factor (j + r) / d i) * (physicalCoeff r i k b * x) =
      b * (NormalizedProfile.factor j * x / d k) := by
  have hi : d i ≠ 0 := (NormalizedProfile.diagonal_pos i).ne'
  have hk : d k ≠ 0 := (NormalizedProfile.diagonal_pos k).ne'
  calc
    (NormalizedProfile.factor (j + r) / d i) * (physicalCoeff r i k b * x) =
        (NormalizedProfile.factor (j + r) * omega41 ^ r) * (b * (x / d k)) := by
      unfold physicalCoeff
      field_simp [hi, hk] <;> ring
    _ = b * (NormalizedProfile.factor j * x / d k) := by
      rw [factor_shift]
      ring

theorem normalized_sum {J : Type*} [Fintype J] (source : J → Fin 14)
    (b : J → ℝ) (v : Profile) (j r : ℕ) (i : Fin 14) :
    (NormalizedProfile.factor (j + r) / d i) *
        (∑ k : J, physicalCoeff r i (source k) (b k) * v (source k)) =
      ∑ k : J, b k * (NormalizedProfile.factor j * v (source k) / d (source k)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => normalized_coefficient j r i (source k) _ _)

end ComparisonCoefficients

/-- The genuinely analytic premises.  Each field is an individual physical
cap or the first high remainder; none is the desired profile recurrence. -/
structure PhysicalCaps : Prop where
  low : ∀ (f : WordState → ℝ) (i : Fin 14) (k : Fin 11),
    SupportProfile.profile (centeredStep (SupportProfile.component f (Fin.castAdd 3 k))) i ≤
      physicalCoeff 1 i (Fin.castAdd 3 k) (lowCoeff i k) *
        SupportProfile.profile f (Fin.castAdd 3 k)
  high : ∀ (f : WordState → ℝ) (i k : Fin 14),
    SupportProfile.profile (highReturn (SupportProfile.component f k)) i ≤
      physicalCoeff 2 i k (returnCoeff i k) * SupportProfile.profile f k
  firstHigh : ∀ (a : AES.State), a ≠ 0 → ∀ i : Fin 14,
    SupportProfile.profile (centeredStep (highPart (error 1 a))) i ≤
      (d i / NormalizedProfile.factor 1) * (1000 * g i)

section Assembly

theorem low_profile_le (h : PhysicalCaps) (f : WordState → ℝ) (i : Fin 14) :
    SupportProfile.profile (centeredStep (lowPart f)) i ≤
      ∑ k : Fin 11, physicalCoeff 1 i (Fin.castAdd 3 k) (lowCoeff i k) *
        SupportProfile.profile f (Fin.castAdd 3 k) := by
  change SupportProfile.profile (centeredStep
    (fun x => ∑ k : Fin 11, SupportProfile.component f (Fin.castAdd 3 k) x)) i ≤ _
  rw [centeredStep_sum]
  exact (profile_sum_le _ i).trans (Finset.sum_le_sum (fun k _ => h.low f i k))

theorem high_profile_le (h : PhysicalCaps) (f : WordState → ℝ) (hz : f 0 = 0)
    (i : Fin 14) :
    SupportProfile.profile (highReturn f) i ≤
      ∑ k : Fin 14, physicalCoeff 2 i k (returnCoeff i k) *
        SupportProfile.profile f k := by
  have hf : f = fun x => ∑ k : Fin 14, SupportProfile.component f k x :=
    funext (fun x => (SupportProfile.component_decomposition f hz x).symm)
  have he : highReturn f =
      fun x => ∑ k : Fin 14, highReturn (SupportProfile.component f k) x := by
    calc
      highReturn f = highReturn (fun x => ∑ k : Fin 14, SupportProfile.component f k x) :=
        congrArg highReturn hf
      _ = _ := highReturn_sum _
  rw [he]
  exact (profile_sum_le _ i).trans (Finset.sum_le_sum (fun k _ => h.high f i k))

theorem normalized_low_le (h : PhysicalCaps) (f : WordState → ℝ)
    (j : ℕ) (i : Fin 14) :
    (NormalizedProfile.factor (j + 1) / d i) *
        SupportProfile.profile (centeredStep (lowPart f)) i ≤
      L (fun k => NormalizedProfile.factor j * SupportProfile.profile f k / d k) i := by
  have hs : 0 ≤ NormalizedProfile.factor (j + 1) / d i :=
    div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
  calc
    _ ≤ (NormalizedProfile.factor (j + 1) / d i) *
        (∑ k : Fin 11, physicalCoeff 1 i (Fin.castAdd 3 k) (lowCoeff i k) *
          SupportProfile.profile f (Fin.castAdd 3 k)) :=
      mul_le_mul_of_nonneg_left (low_profile_le h f i) hs
    _ = ∑ k : Fin 11, lowCoeff i k *
        (NormalizedProfile.factor j * SupportProfile.profile f (Fin.castAdd 3 k) /
          d (Fin.castAdd 3 k)) :=
      normalized_sum (Fin.castAdd 3) (lowCoeff i) (SupportProfile.profile f) j 1 i
    _ = _ := (L_low_expansion
      (fun k => NormalizedProfile.factor j * SupportProfile.profile f k / d k) i).symm

theorem normalized_high_le (h : PhysicalCaps) (f : WordState → ℝ) (hz : f 0 = 0)
    (j : ℕ) (i : Fin 14) :
    (NormalizedProfile.factor (j + 2) / d i) * SupportProfile.profile (highReturn f) i ≤
      M (fun k => NormalizedProfile.factor j * SupportProfile.profile f k / d k) i := by
  have hs : 0 ≤ NormalizedProfile.factor (j + 2) / d i :=
    div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
  calc
    _ ≤ (NormalizedProfile.factor (j + 2) / d i) *
        (∑ k : Fin 14, physicalCoeff 2 i k (returnCoeff i k) * SupportProfile.profile f k) :=
      mul_le_mul_of_nonneg_left (high_profile_le h f hz i) hs
    _ = ∑ k : Fin 14, returnCoeff i k *
        (NormalizedProfile.factor j * SupportProfile.profile f k / d k) :=
      normalized_sum (fun k => k) (returnCoeff i) (SupportProfile.profile f) j 2 i
    _ = _ := (M_expansion _ i).symm

theorem normalized_firstHigh_le (h : PhysicalCaps) (a : AES.State) (ha : a ≠ 0)
    (i : Fin 14) :
    (NormalizedProfile.factor 1 / d i) *
      SupportProfile.profile (centeredStep (highPart (error 1 a))) i ≤ 1000 * g i := by
  have hs : 0 ≤ NormalizedProfile.factor 1 / d i :=
    div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
  have hi : d i ≠ 0 := (NormalizedProfile.diagonal_pos i).ne'
  have hf : NormalizedProfile.factor 1 ≠ 0 := (NormalizedProfile.factor_pos 1).ne'
  calc
    _ ≤ (NormalizedProfile.factor 1 / d i) *
        ((d i / NormalizedProfile.factor 1) * (1000 * g i)) :=
      mul_le_mul_of_nonneg_left (h.firstHigh a ha i) hs
    _ = 1000 * g i := by field_simp [hi, hf] <;> ring

/-- Physical block caps assemble into the existing actual-profile interface. -/
theorem transferEstimates (h : PhysicalCaps) : Startup.TransferEstimates where
  first := by
    intro a ha i
    have ht := profile_add_le (centeredStep (lowPart (error 1 a)))
      (centeredStep (highPart (error 1 a))) i
    rw [← centered_actual_first a ha] at ht
    have hl := normalized_low_le h (error 1 a) 0 i
    change _ ≤ L (NormalizedProfile.actual a 0) i at hl
    have hh := normalized_firstHigh_le h a ha i
    have hs : 0 ≤ NormalizedProfile.factor 1 / d i :=
      div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
    change NormalizedProfile.factor 1 * SupportProfile.profile (error 2 a) i / d i ≤ _
    calc
      _ = (NormalizedProfile.factor 1 / d i) * SupportProfile.profile (error 2 a) i := by ring
      _ ≤ (NormalizedProfile.factor 1 / d i) *
          (SupportProfile.profile (centeredStep (lowPart (error 1 a))) i +
            SupportProfile.profile (centeredStep (highPart (error 1 a))) i) :=
        mul_le_mul_of_nonneg_left ht hs
      _ = (NormalizedProfile.factor 1 / d i) *
            SupportProfile.profile (centeredStep (lowPart (error 1 a))) i +
          (NormalizedProfile.factor 1 / d i) *
            SupportProfile.profile (centeredStep (highPart (error 1 a))) i := by ring
      _ ≤ _ := add_le_add hl hh
  step := by
    intro a ha j i
    have ht := profile_add_le (centeredStep (lowPart (error (j + 2) a)))
      (highReturn (error (j + 1) a)) i
    rw [← centered_actual_memory j a ha] at ht
    have hl : (NormalizedProfile.factor (j + 2) / d i) *
        SupportProfile.profile (centeredStep (lowPart (error (j + 2) a))) i ≤
        L (NormalizedProfile.actual a (j + 1)) i := by
      have hl0 := normalized_low_le h (error (j + 2) a) (j + 1) i
      have hindex : (j + 1) + 1 = j + 2 := by omega
      rw [hindex] at hl0
      have hactual :
          (fun k => NormalizedProfile.factor (j + 1) *
            SupportProfile.profile (error (j + 2) a) k / d k) =
          NormalizedProfile.actual a (j + 1) := by
        funext k
        simp only [NormalizedProfile.actual, SupportProfile.actual, hindex]
      rw [hactual] at hl0
      exact hl0
    have hh := normalized_high_le h (error (j + 1) a)
      (AESPaper.GroupedLaw.error_zero _ a ha) j i
    change _ ≤ M (NormalizedProfile.actual a j) i at hh
    have hs : 0 ≤ NormalizedProfile.factor (j + 2) / d i :=
      div_nonneg (NormalizedProfile.factor_pos _).le (NormalizedProfile.diagonal_pos i).le
    change NormalizedProfile.factor (j + 2) *
      SupportProfile.profile (error (j + 3) a) i / d i ≤ _
    calc
      _ = (NormalizedProfile.factor (j + 2) / d i) *
          SupportProfile.profile (error (j + 3) a) i := by ring
      _ ≤ (NormalizedProfile.factor (j + 2) / d i) *
          (SupportProfile.profile (centeredStep (lowPart (error (j + 2) a))) i +
            SupportProfile.profile (highReturn (error (j + 1) a)) i) :=
        mul_le_mul_of_nonneg_left ht hs
      _ = (NormalizedProfile.factor (j + 2) / d i) *
            SupportProfile.profile (centeredStep (lowPart (error (j + 2) a))) i +
          (NormalizedProfile.factor (j + 2) / d i) *
            SupportProfile.profile (highReturn (error (j + 1) a)) i := by ring
      _ ≤ _ := add_le_add hl hh

end Assembly

end AES8.TransferAssembly
