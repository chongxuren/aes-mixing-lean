import AESMixing.PhysicalLawOps

/-! A physical SubBytes--MixColumns--SubBytes layer acts as four independent
word kernels in column coordinates. This is an operator identity for every
joint input law; it does not assume that the input columns are independent. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem coordinateKernel_relabel_output {I V : Type*}
    [Fintype I] [DecidableEq I] [Fintype V]
    (e : I → Equiv.Perm V) (D : I → V → V → ℝ) (f : (I → V) → ℝ) :
    lawRelabel (Equiv.piCongrRight e) (action (coordinateKernel D) f) =
      action (coordinateKernel (fun i y x => D i ((e i).symm y) x)) f := rfl

theorem coordinate_superbox_action {I V : Type*}
    [Fintype I] [DecidableEq I] [Fintype V]
    (e : I → Equiv.Perm V) (D : I → V → V → ℝ) (f : (I → V) → ℝ) :
    action (coordinateKernel D)
        (lawRelabel (Equiv.piCongrRight e) (action (coordinateKernel D) f)) =
      action (coordinateKernel (fun i =>
        kernelCompose (D i) (fun y x => D i ((e i).symm y) x))) f := by
  rw [coordinateKernel_relabel_output, ← kernelCompose_action, coordinateKernel_compose]

theorem three_laws_reindex {A B : Type*} (e : B → A)
    (S M : (A → ℝ) → (A → ℝ)) (s m : (B → ℝ) → (B → ℝ))
    (hS : ∀ f b, S f (e b) = s (fun a => f (e a)) b)
    (hM : ∀ f b, M f (e b) = m (fun a => f (e a)) b)
    (f : A → ℝ) (b : B) :
    S (M (S f)) (e b) = s (m (s (fun a => f (e a)))) b := by
  rw [hS]
  apply congrArg (fun g => s g b)
  funext a
  rw [hM]
  apply congrArg (fun g => m g a)
  funext c
  exact hS f c

theorem coordinate_superbox_action_apply {I V : Type*}
    [Fintype I] [DecidableEq I] [Fintype V]
    (e : I → Equiv.Perm V) (D : I → V → V → ℝ)
    (f : (I → V) → ℝ) (b : I → V) :
    action (coordinateKernel D)
      (fun x => action (coordinateKernel D) f ((Equiv.piCongrRight e).symm x)) b =
      action (coordinateKernel (fun i =>
        kernelCompose (D i) (fun y x => D i ((e i).symm y) x))) f b := by
  exact congrFun (coordinate_superbox_action e D f) b

namespace AES

def columnSubstitutionKernel : WordState → WordState → ℝ :=
  coordinateKernel (fun _ : Fin 4 => substitutionKernel aesByteChannel)

def parallelColumnDiffusion : Equiv.Perm WordState :=
  Equiv.piCongrRight (fun _ : Fin 4 => byteDiffusionEquiv)

def wordSuperboxKernel : Word → Word → ℝ :=
  kernelCompose (substitutionKernel aesByteChannel)
    (fun y x => substitutionKernel aesByteChannel (byteDiffusionEquiv.symm y) x)

def parallelSuperboxKernel : WordState → WordState → ℝ :=
  coordinateKernel (fun _ : Fin 4 => wordSuperboxKernel)

theorem substitution_column_kernel (b a : WordState) :
    differenceChannel subBytesPerm (transposeState b) (transposeState a) =
      columnSubstitutionKernel b a := by
  rw [subBytes_difference_channel]
  change (∏ row, ∏ col, aesByteChannel (b col row) (a col row)) =
    ∏ col, ∏ row, aesByteChannel (b col row) (a col row)
  exact Finset.prod_comm

theorem substituteLaw_columns (f : State → ℝ) (b : WordState) :
    substituteLaw f (transposeState b) =
      action columnSubstitutionKernel (fun a => f (transposeState a)) b := by
  have h := Equiv.sum_comp transposeState.toEquiv
    (fun a => differenceChannel subBytesPerm (transposeState b) a * f a)
  simp only [AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    substitution_column_kernel] at h
  exact h.symm

theorem mixColumns_transpose (b : WordState) :
    mixColumnsEquiv (transposeState b) = transposeState (parallelColumnDiffusion b) := by
  funext row col
  exact congrFun (mixColumns_column (transposeState b) col) row

theorem mixColumns_transpose_inverse (b : WordState) :
    mixColumnsEquiv.toEquiv.symm (transposeState b) =
      transposeState (parallelColumnDiffusion.symm b) := by
  exact mixColumnsEquiv.toEquiv.symm_apply_eq.mpr
    ((mixColumns_transpose (parallelColumnDiffusion.symm b)).trans
      (congrArg transposeState (parallelColumnDiffusion.apply_symm_apply b))).symm

theorem mixLaw_columns (f : State → ℝ) (b : WordState) :
    mixLaw f (transposeState b) = f (transposeState (parallelColumnDiffusion.symm b)) := by
  unfold mixLaw lawRelabel
  rw [mixColumns_transpose_inverse]

-- Name the conversion steps so the kernel need not normalize a whole
-- concrete state action while checking one large composite proof term.
set_option maxHeartbeats 10000 in
theorem superbox_columns_factor (f : State → ℝ) (b : WordState) :
    substituteLaw (mixLaw (substituteLaw f)) (transposeState b) =
      action columnSubstitutionKernel
        (fun x => action columnSubstitutionKernel
          (fun a => f (transposeState a)) (parallelColumnDiffusion.symm x)) b := by
  exact three_laws_reindex (fun x => transposeState x) substituteLaw mixLaw
    (action columnSubstitutionKernel) (fun g x => g (parallelColumnDiffusion.symm x))
    substituteLaw_columns mixLaw_columns f b

set_option maxHeartbeats 10000 in
theorem parallel_superbox_factor (g : WordState → ℝ) (b : WordState) :
    action columnSubstitutionKernel
      (fun x => action columnSubstitutionKernel g (parallelColumnDiffusion.symm x)) b =
      action parallelSuperboxKernel g b := by
  delta columnSubstitutionKernel parallelColumnDiffusion
    parallelSuperboxKernel wordSuperboxKernel
  exact coordinate_superbox_action_apply
    (fun _ : Fin 4 => byteDiffusionEquiv)
    (fun _ : Fin 4 => substitutionKernel aesByteChannel) g b

theorem superboxLaw_apply (f : State → ℝ) :
    superboxLaw f = substituteLaw (mixLaw (substituteLaw f)) := by
  unfold superboxLaw
  rw [Function.comp_apply, Function.comp_apply]

set_option maxHeartbeats 10000 in
theorem superboxLaw_columns (f : State → ℝ) (b : WordState) :
    superboxLaw f (transposeState b) =
      action parallelSuperboxKernel (fun a => f (transposeState a)) b := by
  rw [superboxLaw_apply, superbox_columns_factor, parallel_superbox_factor]

end AES
end AESMixing
