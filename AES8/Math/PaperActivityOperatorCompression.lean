import AES8.Math.PaperActivitySpectrum
import AESConcrete.ActivityFullStep
import AES8.Math.PaperFiniteOrthonormalCompression
import Mathlib.Analysis.Matrix.Spectrum

/-! Generic activity compression, in the counting-measure Euclidean norm.
The actual support-pattern sandwich is reduced using the proved MDS kernel,
not an assumed four-dimensional operator identity. Constructive proofs only.
This leaf is a separate candidate; the spectrum leaf remains byte-frozen.
-/
noncomputable section
open scoped BigOperators Matrix
namespace AES8.PaperActivityOperatorCompression
open AESMixing AESConcrete.RefinedWordProjection
open AESConcrete.ActivityRankOneStep (activityIndicator activityMass)
open AESConcrete.ActivityFullStep
open PaperKernelBounds
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- The four nonzero activity sizes, in the paper's order. -/
def weight (a : Fin 4) : Fin 5 := ⟨a.val+1, by omega⟩

theorem weight_injective : Function.Injective weight := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [weight] using this

theorem weight_ne_zero (a : Fin 4) : weight a ≠ 0 := by
  intro h
  have hh := congrArg Fin.val h
  change a.val+1 = 0 at hh
  omega

/-- Orthogonality of the actual refined projections at distinct weights. -/
theorem refined_cross (hn : 1 < Fintype.card V) (a b : Fin 5) (hab : a ≠ b) :
    kernelCompose (refinedKernel (0 : V) 0 a) (refinedKernel 0 0 b) = 0 := by
  funext y x
  unfold refinedKernel kernelCompose
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hp : AES.maskSize p.val.2 + b.val = 4
  · by_cases hr : AES.maskSize r.val.2 + a.val = 4
    · simp only [hp, hr, if_true]
      change kernelCompose (supportIndexKernel (0 : V) r)
        (supportIndexKernel 0 p) y x = 0
      rw [supportIndexKernel_compose (0 : V) hn]
      have hpr : r ≠ p := by
        intro he
        subst r
        apply hab
        apply Fin.ext
        omega
      rw [if_neg hpr]
      rfl
    · simp [hr]
  · simp [hp]

/-- The activity indicators are orthogonal, with their actual cardinalities. -/
theorem indicator_inner (hn : 1 < Fintype.card V) (a b : Fin 5) :
    (∑ x : Fin 4 → V, activityIndicator a x * activityIndicator b x) =
      if a = b then activityMass (Fintype.card V) a else 0 := by
  by_cases hab : a = b
  · subst b
    simpa [pow_two] using AESConcrete.ActivityRankOneStep.activityIndicator_energy hn a
  · rw [if_neg hab]
    have hc : action (refinedKernel (0 : V) 0 b) (activityIndicator a) = 0 := by
      unfold activityIndicator
      rw [← kernelCompose_action, refined_cross hn b a (Ne.symm hab)]
      ext x
      simp [action]
    have hb (y : Fin 4 → V) : activityIndicator b y =
        ∑ x : Fin 4 → V, refinedKernel (0 : V) 0 b y x := by
      simp [activityIndicator, action]
    calc
      _ = ∑ y : Fin 4 → V,
          (∑ x : Fin 4 → V, refinedKernel (0 : V) 0 b y x) * activityIndicator a y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [hb y, mul_comm]
      _ = ∑ y : Fin 4 → V, ∑ x : Fin 4 → V,
          refinedKernel (0 : V) 0 b y x * activityIndicator a y := by
        simp only [Finset.sum_mul]
      _ = ∑ x : Fin 4 → V, action (refinedKernel (0 : V) 0 b)
          (activityIndicator a) x := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        unfold action
        apply Finset.sum_congr rfl
        intro y _
        rw [refinedKernel_symmetric (0 : V) 0 b y x]
      _ = 0 := by simp [hc]

/-- Weight-class cardinality. -/
def mass (m : ℝ) (a : Fin 4) : ℝ :=
  activityMass m (weight a)

def scale (m : ℝ) (a : Fin 4) : ℝ := Real.sqrt (mass m a)

theorem mass_pos (m : ℝ) (hm : 1 < m) (a : Fin 4) : 0 < mass m a := by
  have hc : 0 < (Nat.choose 4 (a.val+1) : ℝ) := by
    fin_cases a <;> norm_num [Nat.choose]
  exact mul_pos hc (pow_pos (sub_pos.mpr hm) _)

theorem scale_pos (m : ℝ) (hm : 1 < m) (a : Fin 4) : 0 < scale m a :=
  Real.sqrt_pos.mpr (mass_pos m hm a)

theorem scale_sq (m : ℝ) (hm : 1 < m) (a : Fin 4) : scale m a ^ 2 = mass m a :=
  Real.sq_sqrt (mass_pos m hm a).le

/-- The orthonormal columns are the actual activity indicators. -/
def indicatorUnit (a : Fin 4) (x : Fin 4 → V) : ℝ :=
  activityIndicator (weight a) x / scale (Fintype.card V) a

theorem unit_inner (hn : 1 < Fintype.card V) (a b : Fin 4) :
    (∑ x : Fin 4 → V, indicatorUnit a x * indicatorUnit b x) =
      if a = b then 1 else 0 := by
  have hm : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have ha := ne_of_gt (scale_pos (Fintype.card V) hm a)
  have hb := ne_of_gt (scale_pos (Fintype.card V) hm b)
  simp only [indicatorUnit, div_mul_div_comm, ← Finset.sum_div, indicator_inner hn]
  by_cases hab : a = b
  · subst b
    simp only [if_true]
    rw [← pow_two, scale_sq (Fintype.card V) hm a]
    exact div_self (ne_of_gt (mass_pos (Fintype.card V) hm a))
  · have hw : weight a ≠ weight b := fun h => hab (weight_injective h)
    simp [hab, hw]

/-- Exact MDS coefficient before summing weight classes. -/
def coefficient (m : ℝ) (a b : Fin 4) : ℝ :=
  AESPaper.ActivityMDSCounts.supportCount m (a.val+b.val+2) /
    (m-1)^(a.val+b.val+2)

/-- Counting-measure orthonormal compression, before centering. -/
def compressedMatrix (m : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun a b => coefficient m a b * scale m a * scale m b

theorem compressed_symmetric (m : ℝ) : (compressedMatrix m).IsHermitian := by
  change (compressedMatrix m).conjTranspose = compressedMatrix m
  ext a b
  simp only [Matrix.conjTranspose_apply, star_trivial, compressedMatrix]
  have he : coefficient m b a = coefficient m a b := by
    unfold coefficient
    rw [Nat.add_comm b.val a.val]
  rw [he]
  ring

/-- Literal nonzero part of the support-pattern diffusion sandwich. -/
def actualKernel (L : (Fin 4 → V) →+ (Fin 4 → V)) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  fun y x => ∑ a : Fin 4, ∑ b : Fin 4,
    kernelCompose (fun y z => refinedKernel (0 : V) 0 (weight a) y (L z))
      (refinedKernel (0 : V) 0 (weight b)) y x

/-- MDS counts give the entire actual kernel, rather than a presumed matrix. -/
theorem actualKernel_factor (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (y x : Fin 4 → V) :
    actualKernel L y x = ∑ a : Fin 4, ∑ b : Fin 4,
      coefficient (Fintype.card V) a b * activityIndicator (weight a) y *
        activityIndicator (weight b) x := by
  unfold actualKernel
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h := congrFun (congrFun (diffusion_activity_rank_one hn L hL (weight a) (weight b)) y) x
  simpa [coefficient, weight, AESPaper.ActivityMDSCounts.supportCount,
    AESConcrete.ActivityMDSCounts.supportCount, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using h

/-- The four orthonormal coordinates reconstruct the actual nonzero sandwich. -/
theorem actualKernel_orthonormal_factor (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (y x : Fin 4 → V) :
    actualKernel L y x = ∑ a : Fin 4, ∑ b : Fin 4,
      indicatorUnit a y * compressedMatrix (Fintype.card V) a b * indicatorUnit b x := by
  rw [actualKernel_factor hn L hL]
  have hm : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  unfold indicatorUnit compressedMatrix
  field_simp [ne_of_gt (scale_pos (Fintype.card V) hm a),
    ne_of_gt (scale_pos (Fintype.card V) hm b)]
  <;> ring

/-- In particular every zero-total within-weight input is killed. -/
theorem kills_weight_totals (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (f : (Fin 4 → V) → ℝ)
    (hf : ∀ b : Fin 4, (∑ x, activityIndicator (weight b) x * f x) = 0) :
    kernelAction (actualKernel L) f = 0 := by
  funext y
  simp only [kernelAction, actualKernel_factor hn L hL, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro b _
  calc
    _ = coefficient (Fintype.card V) a b * activityIndicator (weight a) y *
        ∑ x, activityIndicator (weight b) x * f x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = 0 := by rw [hf b, mul_zero]

/-- The printed total-mass matrix uses the same kernel coefficient. -/
theorem massMatrix_eq_coefficient (m : ℝ) (hm : 1 < m) (a b : Fin 4) :
    PaperActivitySpectrum.massMatrix m a b = mass m a * coefficient m a b := by
  have hn : m-1 ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  unfold PaperActivitySpectrum.massMatrix mass activityMass weight coefficient
  simp only
  rw [show a.val+b.val+2 = (a.val+1)+(b.val+1) by omega, pow_add]
  field_simp [hn]
  <;> ring

/-- Entrywise form of D⁻¹ C D, with no claimed identity as a premise. -/
theorem weighted_conjugation (m : ℝ) (hm : 1 < m) (a b : Fin 4) :
    compressedMatrix m a b =
      (scale m a)⁻¹ * PaperActivitySpectrum.massMatrix m a b * scale m b := by
  rw [massMatrix_eq_coefficient m hm a b, ← scale_sq m hm a]
  unfold compressedMatrix
  field_simp [ne_of_gt (scale_pos m hm a)]
  <;> ring

/-- Specialization of reusable finite orthonormal-column synthesis. -/
abbrev synthesize (v : Fin 4 → ℝ) : (Fin 4 → V) → ℝ :=
  PaperFiniteOrthonormalCompression.synthesize indicatorUnit v

abbrev analyze (f : (Fin 4 → V) → ℝ) : Fin 4 → ℝ :=
  PaperFiniteOrthonormalCompression.analyze indicatorUnit f

theorem analyze_synthesize (hn : 1 < Fintype.card V) (v : Fin 4 → ℝ) :
    analyze (synthesize (V := V) v) = v :=
  PaperFiniteOrthonormalCompression.analyze_synthesize (unit_inner hn) v

theorem synthesis_energy (hn : 1 < Fintype.card V) (v : Fin 4 → ℝ) :
    (∑ x : Fin 4 → V, synthesize v x ^ 2) = ∑ a : Fin 4, v a ^ 2 :=
  PaperFiniteOrthonormalCompression.synthesis_energy (unit_inner hn) v

/-- The actual operator factors through the four orthonormal coordinates. -/
theorem action_compression (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (f : (Fin 4 → V) → ℝ) :
    kernelAction (actualKernel L) f =
      synthesize ((compressedMatrix (Fintype.card V)).mulVec (analyze f)) := by
  funext y
  simp only [kernelAction, actualKernel_orthonormal_factor hn L hL,
    synthesize, PaperFiniteOrthonormalCompression.synthesize, Matrix.mulVec, dotProduct, analyze, PaperFiniteOrthonormalCompression.analyze, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro x _
  ring


/-- Exact-support total-mass transition matrix, before grouping equal sizes. -/
def patternMatrix (L : (Fin 4 → V) →+ (Fin 4 → V)) : Matrix (Fin 16) (Fin 16) ℝ :=
  fun r s => (∑ x : Fin 4 → V,
      AESPaper.ActivityMDSCounts.supportWeight r (L x) *
        AESPaper.ActivityMDSCounts.supportWeight s x) /
    ((Fintype.card V : ℝ)-1)^(4-AES.maskSize s)

theorem patternMatrix_entry (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 16) :
    patternMatrix L r s =
      AESPaper.ActivityMDSCounts.supportCount (Fintype.card V)
        ((4-AES.maskSize r)+(4-AES.maskSize s)) /
      ((Fintype.card V : ℝ)-1)^(4-AES.maskSize s) := by
  unfold patternMatrix
  rw [AESPaper.ActivityMDSCounts.supportWeight_graph_sum L hL]
  rfl

/-- Equal-size exact-support columns coincide in total-mass coordinates. -/
theorem pattern_columns_equal (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 16) (hrs : AES.maskSize r = AES.maskSize s) (t : Fin 16) :
    patternMatrix L t r = patternMatrix L t s := by
  simp only [patternMatrix_entry L hL, hrs]

/-- Thus every same-size difference of exact support-pattern masses is killed. -/
theorem same_size_difference_killed (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r s : Fin 16) (hrs : AES.maskSize r = AES.maskSize s) :
    (patternMatrix L).mulVec (Pi.single r 1-Pi.single s 1) = 0 := by
  ext t
  simp only [Matrix.mulVec_sub, Pi.sub_apply, Matrix.mulVec_single_one, Pi.zero_apply]
  exact sub_eq_zero.mpr (pattern_columns_equal L hL r s hrs t)

/-- The generic finite-column kernel, specialized to activity. -/
abbrev liftMatrix (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  PaperFiniteOrthonormalCompression.liftMatrix indicatorUnit A

theorem lift_norm (hn : 1 < Fintype.card V) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    ‖kernelOperator (liftMatrix (V := V) A)‖ = ‖kernelOperator A‖ :=
  PaperFiniteOrthonormalCompression.lift_norm (unit_inner hn) A

theorem lift_square_sum (hn : 1 < Fintype.card V) (A : Matrix (Fin 4) (Fin 4) ℝ) :
    (∑ y : Fin 4 → V, ∑ x : Fin 4 → V, liftMatrix A y x ^ 2) =
      ∑ a : Fin 4, ∑ b : Fin 4, A a b ^ 2 :=
  PaperFiniteOrthonormalCompression.lift_square_sum (unit_inner hn) A

/-- Removal of the uniform nonzero direction in orthonormal coordinates. -/
def centeredMatrix (m : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun a b => (coefficient m a b-1/(m^4-1)) * scale m a * scale m b

/-- The actual centered support sandwich on its nonzero block. -/
def centeredKernel (L : (Fin 4 → V) →+ (Fin 4 → V)) :
    (Fin 4 → V) → (Fin 4 → V) → ℝ :=
  fun y x => ∑ a : Fin 4, ∑ b : Fin 4,
    (kernelCompose (fun y z => refinedKernel (0 : V) 0 (weight a) y (L z))
      (refinedKernel (0 : V) 0 (weight b)) y x -
    kernelCompose (refinedKernel (0 : V) 0 (weight a))
      (kernelCompose (AESConcrete.DegreeCentering.globalUniformKernel 0)
        (refinedKernel (0 : V) 0 (weight b))) y x)

theorem centered_factor (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) :
    centeredKernel L = liftMatrix (centeredMatrix (Fintype.card V)) := by
  funext y x
  have hm : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  unfold centeredKernel liftMatrix PaperFiniteOrthonormalCompression.liftMatrix
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [diffusion_activity_rank_one hn L hL]
  rw [AESConcrete.ActivityRankOneStep.uniform_sandwich (weight a) (weight b)
    (weight_ne_zero a) (weight_ne_zero b)]
  simp only [indicatorUnit, centeredMatrix, coefficient, weight]
  change (AESPaper.ActivityMDSCounts.supportCount (Fintype.card V) _ / _ * _ * _)-_ = _
  have ha := ne_of_gt (scale_pos (Fintype.card V) hm a)
  have hb := ne_of_gt (scale_pos (Fintype.card V) hm b)
  have hn0 : (Fintype.card V : ℝ)-1 ≠ 0 := ne_of_gt (sub_pos.mpr hm)
  have hm2 : 1 < (Fintype.card V : ℝ)^2 := by nlinarith
  have hN : (Fintype.card V : ℝ)^4-1 ≠ 0 := by
    have hpos : 0 < (Fintype.card V : ℝ)^4-1 := by
      nlinarith [sq_nonneg ((Fintype.card V : ℝ)^2-1)]
    exact ne_of_gt hpos
  simp only [AESPaper.ActivityMDSCounts.supportCount, AESConcrete.ActivityMDSCounts.supportCount]
  have he : a.val+1+(b.val+1) = a.val+b.val+2 := by omega
  rw [he]
  field_simp [ha, hb, hn0, hN]
  <;> ring

theorem centered_symmetric (m : ℝ) : (centeredMatrix m).IsHermitian := by
  change (centeredMatrix m).conjTranspose = centeredMatrix m
  ext a b
  simp only [Matrix.conjTranspose_apply, star_trivial, centeredMatrix]
  have he : coefficient m b a = coefficient m a b := by
    unfold coefficient
    rw [Nat.add_comm b.val a.val]
  rw [he]
  ring

/-- The actual centered operator and its proved four-dimensional compression
have precisely the same Euclidean norm. -/
theorem centered_norm_transfer (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) :
    ‖kernelOperator (centeredKernel L)‖ =
      ‖kernelOperator (centeredMatrix (Fintype.card V))‖ := by
  rw [centered_factor hn L hL]
  exact lift_norm hn _

theorem centered_trace_transfer (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) :
    (∑ y : Fin 4 → V, ∑ x : Fin 4 → V, centeredKernel L y x ^ 2) =
      Matrix.trace (centeredMatrix (Fintype.card V)^2) := by
  rw [centered_factor hn L hL, lift_square_sum hn]
  simp only [Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he := congrFun (congrFun (centered_symmetric (Fintype.card V)) a) b
  simp only [Matrix.conjTranspose_apply, star_trivial] at he
  rw [he]

end AES8.PaperActivityOperatorCompression
