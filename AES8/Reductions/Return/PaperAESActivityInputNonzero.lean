import AES8.Reductions.Return.PaperAESActivityInputNorm
import AESConcrete.DegreeCentering
import AESConcrete.CenteredWordStepZeros

/-! Literal centered activity input on the nonzero word-state domain.
The ambient full-space estimate is restricted only after proving the exact
kernel identity with P_i T (P_0-U). No centered norm premise is assumed. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputNonzero
open AESMixing PaperKernelBounds PaperAESActivityIdentification PaperAESActivityInputNorm
open AESConcrete.DegreeCentering AESConcrete.CenteredWordStepZeros
open AESConcrete.WordCrossZero (wordMixAddEquiv)
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

abbrev NonzeroWordState := {x : AES.WordState // x ≠ 0}

private theorem distinguishedState_zero :
    distinguishedState (0 : AES.Word) = (0 : AES.WordState) := by
  funext k
  rfl

def restrict (K : AES.WordState → AES.WordState → ℝ) :
    NonzeroWordState → NonzeroWordState → ℝ := fun y x => K y.val x.val

theorem actualStep_pointed (adjoint : Bool) : PointedBistochastic (actualStep adjoint) 0 := by
  let D := coordinateKernel (fun _ : Fin 4 => channel adjoint)
  have hD : PointedBistochastic D 0 :=
    coordinateKernel_pointed _ _ (fun _ => channel_pointed adjoint)
  refine ⟨fun y x => hD.nonnegative y (wordMixAddEquiv x),?_,?_,
    fun x => hD.column_sum (wordMixAddEquiv x),?_⟩
  · intro x
    change D 0 (wordMixAddEquiv x) = _
    rw [hD.zero_row]
    have he : wordMixAddEquiv x = 0 ↔ x = 0 := by
      constructor
      · intro h
        apply wordMixAddEquiv.injective
        rw [h,wordMixAddEquiv.map_zero]
      · intro h
        rw [h,wordMixAddEquiv.map_zero]
    simp only [he]
  · intro y
    change D y (wordMixAddEquiv 0) = _
    rw [wordMixAddEquiv.map_zero,hD.zero_column]
  · intro y
    change (∑ x, D y (wordMixAddEquiv x)) = 1
    exact (wordMixAddEquiv.toEquiv.sum_comp (fun x => D y x)).trans (hD.row_sum y)

/-- Pointed bistochasticity fixes the global uniform-nonzero kernel. -/
theorem pointed_global {D : AES.WordState → AES.WordState → ℝ}
    (hD : PointedBistochastic D 0) :
    kernelCompose D (globalUniformKernel (0 : AES.Word)) = globalUniformKernel 0 := by
  funext y x
  by_cases hx : x = 0
  · simp [kernelCompose,globalUniformKernel,distinguishedState_zero,hx]
  · have he (a : AES.WordState) : D y a * globalUniformKernel (0 : AES.Word) a x =
        (D y a - if a = 0 then D y 0 else 0) /
          (Fintype.card AES.WordState - 1 : ℝ) := by
      by_cases ha : a = 0 <;>
        simp [globalUniformKernel,distinguishedState_zero,hx,ha,div_eq_mul_inv,mul_comm]
    unfold kernelCompose
    simp_rw [he]
    rw [← Finset.sum_div,Finset.sum_sub_distrib,hD.row_sum]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,hD.zero_column]
    by_cases hy : y = 0 <;> simp [globalUniformKernel,distinguishedState_zero,hx,hy]

def centeredActivityFull : AES.WordState → AES.WordState → ℝ :=
  degreeKernel 0 0 - globalUniformKernel (0 : AES.Word)

def centeredInputKernel (i : Fin 5) (adjoint : Bool) : AES.WordState → AES.WordState → ℝ :=
  kernelCompose (degreeKernel 0 i) (kernelCompose (actualStep adjoint) centeredActivityFull)

/-- Positive output degree kills the stationary correction after the step. -/
theorem centeredInput_eq (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool) :
    centeredInputKernel i adjoint = activityInputKernel i adjoint := by
  simp only [centeredInputKernel,centeredActivityFull,compose_sub_right,
    pointed_global (actualStep_pointed adjoint),
    degreeKernel_compose_globalUniformKernel 0 AESConcrete.AES.word_card_gt_one i hi,
    sub_zero,activityInputKernel]

theorem positive_degree_zero_column (i : Fin 5) (hi : i ≠ 0) (y : AES.WordState) :
    degreeKernel (0 : AES.Word) i y 0 = 0 := by
  rw [degreeKernel_symmetric]
  have h := degreeComponent_at_distinguishedState (0 : AES.Word)
    AESConcrete.AES.word_card_gt_one i hi (fun z : AES.WordState => if z = y then 1 else 0)
  rw [distinguishedState_zero] at h
  rw [← degreeKernel_action] at h
  simpa only [action,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    using h

/-- Dropping the zero intermediate state is exact when the left column is zero. -/
theorem restrict_compose (K L : AES.WordState → AES.WordState → ℝ)
    (hK : ∀ y : NonzeroWordState, K y.val 0 = 0) :
    restrict (kernelCompose K L) = kernelCompose (restrict K) (restrict L) := by
  funext y x
  unfold restrict kernelCompose
  apply Finset.sum_congr_set {z : AES.WordState | z ≠ 0}
  · intro z _
    rfl
  · intro z hz
    have he : z = 0 := not_not.mp hz
    subst z
    rw [hK,zero_mul]

def nonzeroDegree (i : Fin 5) := restrict (degreeKernel (0 : AES.Word) i)
def nonzeroStep (adjoint : Bool) := restrict (actualStep adjoint)

theorem nonzeroStep_ordinary : nonzeroStep false =
    restrict AESConcrete.WordStepZeros.wordStepKernel := rfl

def nonzeroActivity (y x : NonzeroWordState) : ℝ :=
  degreeKernel (0 : AES.Word) 0 y.val x.val - 1/(Fintype.card AES.WordState - 1 : ℝ)

theorem restrict_centeredActivity : restrict centeredActivityFull = nonzeroActivity := by
  funext y x
  simp only [restrict,centeredActivityFull,Pi.sub_apply,nonzeroActivity,
    globalUniformKernel,distinguishedState_zero,if_neg y.property,if_neg x.property]

def nonzeroBlock (i : Fin 5) (adjoint : Bool) :
    NonzeroWordState → NonzeroWordState → ℝ :=
  kernelCompose (nonzeroDegree i) (kernelCompose (nonzeroStep adjoint) nonzeroActivity)

/-- The literal paper-domain P_i T (P_0-U), with both composition sums over
nonzero word states, equals the restriction of the bounded ambient kernel. -/
theorem nonzeroBlock_eq (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool) :
    nonzeroBlock i adjoint = restrict (activityInputKernel i adjoint) := by
  rw [← centeredInput_eq i hi adjoint]
  unfold centeredInputKernel
  rw [restrict_compose _ _ (fun y => positive_degree_zero_column i hi y.val)]
  rw [restrict_compose _ _ (fun y => by
    have h := (actualStep_pointed adjoint).zero_column y.val
    simpa only [if_neg y.property] using h)]
  rw [restrict_centeredActivity]
  rfl

def zeroExtend (f : NonzeroWordState → ℂ) (x : AES.WordState) : ℂ :=
  if hx : x ≠ 0 then f ⟨x,hx⟩ else 0

theorem zeroExtend_energy (f : NonzeroWordState → ℂ) :
    (∑ x, ‖zeroExtend f x‖^2) = ∑ x, ‖f x‖^2 := by
  apply Finset.sum_congr_set {x : AES.WordState | x ≠ 0}
  · intro x hx
    change x ≠ 0 at hx
    simp only [zeroExtend,dif_pos hx]
    rfl
  · intro x hx
    change ¬(x ≠ 0) at hx
    simp only [zeroExtend,dif_neg hx,norm_zero,zero_pow (by decide : 2 ≠ 0)]

theorem restrict_action (K : AES.WordState → AES.WordState → ℝ)
    (f : NonzeroWordState → ℂ) (y : NonzeroWordState) :
    kernelAction (fun y x => (K y x : ℂ)) (zeroExtend f) y.val =
      kernelAction (fun y x => (restrict K y x : ℂ)) f y := by
  unfold kernelAction restrict
  apply Finset.sum_congr_set {x : AES.WordState | x ≠ 0}
  · intro x hx
    change x ≠ 0 at hx
    simp only [zeroExtend,dif_pos hx]
    rfl
  · intro x hx
    change ¬(x ≠ 0) at hx
    simp only [zeroExtend,dif_neg hx,mul_zero]

theorem restrict_energy_le (g : AES.WordState → ℂ) :
    (∑ y : NonzeroWordState, ‖g y.val‖^2) ≤ ∑ y, ‖g y‖^2 := by
  have he : (∑ y : AES.WordState, if y ≠ 0 then ‖g y‖^2 else 0) =
      ∑ y : NonzeroWordState, ‖g y.val‖^2 := by
    apply Finset.sum_congr_set {y : AES.WordState | y ≠ 0}
    · intro y hy
      exact if_pos hy
    · intro y hy
      exact if_neg hy
  rw [← he]
  apply Finset.sum_le_sum
  intro y _
  split_ifs <;> first | exact le_rfl | exact sq_nonneg _

theorem nonzeroBlock_energy (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool)
    (f : NonzeroWordState → ℂ) :
    (∑ y, ‖kernelAction (fun y x => (nonzeroBlock i adjoint y x : ℂ)) f y‖^2) ≤
      energyCap i * ∑ x, ‖f x‖^2 := by
  rw [nonzeroBlock_eq i hi adjoint]
  simp_rw [← restrict_action]
  have h := (restrict_energy_le (kernelAction
    (fun y x => (activityInputKernel i adjoint y x : ℂ)) (zeroExtend f))).trans
    (activityInput_complex_energy i hi adjoint (zeroExtend f))
  simpa only [zeroExtend_energy] using h

/-- The activity-input lemma on the exact nonzero domain and centered input. -/
theorem nonzeroBlock_scaled_norm (i : Fin 5) (hi : i ≠ 0) (adjoint : Bool) :
    PaperAESActivityInputResponse.wordQ^2 *
      ‖kernelOperator (fun y x => (nonzeroBlock i adjoint y x : ℂ))‖ ≤ decimal i := by
  have h := operator_norm_sq_le_of_energy
    (fun y x => (nonzeroBlock i adjoint y x : ℂ)) (energyCap i)
    (energyCap_nonneg i) (nonzeroBlock_energy i hi adjoint)
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (decimal_nonneg i)).mp
  calc
    _ = PaperAESActivityInputResponse.wordQ^4 *
        ‖kernelOperator (fun y x => (nonzeroBlock i adjoint y x : ℂ))‖^2 := by ring
    _ ≤ PaperAESActivityInputResponse.wordQ^4*energyCap i :=
      mul_le_mul_of_nonneg_left h (by norm_num [PaperAESActivityInputResponse.wordQ])
    _ ≤ _ := decimal_square i

/-- Frozen-paper `lem:aesasm-activity-input`, in ordinary Euclidean norm on
the nonzero word states. Here `false` is the actual grouped AES step H Pi. -/
theorem activity_input_paper :
    (∀ i : Fin 5, i ≠ 0 →
      PaperAESActivityInputResponse.wordQ^2 *
        ‖kernelOperator (fun y x => (nonzeroBlock i false y x : ℂ))‖ ≤ decimal i) ∧
    decimal 1 = 0 ∧ decimal 2 = (389/10000 : ℝ) ∧
    decimal 3 = (134/10000 : ℝ) ∧ decimal 4 = (1728/1000000 : ℝ) := by
  exact ⟨fun i hi => nonzeroBlock_scaled_norm i hi false,rfl,rfl,rfl,rfl⟩

end AES8.PaperAESActivityInputNonzero
