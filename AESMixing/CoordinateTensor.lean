import AESMixing.ProductProjection
import Mathlib.Algebra.BigOperators.Fin

/-! Operator bounds on four byte positions in the paper's function indexing. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def fourTupleEquiv (V : Type*) : (Fin 4 → V) ≃ PairFour V where
  toFun x := ((x 0,x 1),(x 2,x 3))
  invFun x i := if i = 0 then x.1.1 else if i = 1 then x.1.2 else if i = 2 then x.2.1 else x.2.2
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

def reindexKernel {A B : Type*} (e : A ≃ B) (K : B → B → ℝ) : A → A → ℝ :=
  fun y x => K (e y) (e x)

theorem reindexKernel_action {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (K : B → B → ℝ) (f : A → ℝ) (x : A) :
    action (reindexKernel e K) f x = action K (f ∘ e.symm) (e x) := by
  simpa only [action, reindexKernel, Function.comp_apply, e.symm_apply_apply] using
    e.sum_comp (fun z => K (e x) z * f (e.symm z))

theorem reindexKernel_energy {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (K : B → B → ℝ) (s : ℝ)
    (h : ∀ f, (∑ y, action K f y^2) ≤ s^2 * ∑ x, f x^2) (f : A → ℝ) :
    (∑ y, action (reindexKernel e K) f y^2) ≤ s^2 * ∑ x, f x^2 := by
  simp_rw [reindexKernel_action]
  rw [e.sum_comp (fun y => action K (f ∘ e.symm) y^2)]
  have hb := h (f ∘ e.symm)
  have he : (∑ x, (f ∘ e.symm) x^2) = ∑ x, f x^2 :=
    e.symm.sum_comp (fun x => f x^2)
  rw [he] at hb
  exact hb

def coordinateKernel {I V : Type*} [Fintype I] (A : I → V → V → ℝ)
    (y x : I → V) : ℝ := ∏ i, A i (y i) (x i)

theorem coordinateKernel_compose {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V]
    (A B : I → V → V → ℝ) :
    kernelCompose (coordinateKernel A) (coordinateKernel B) =
      coordinateKernel (fun i => kernelCompose (A i) (B i)) := by
  funext y x
  unfold kernelCompose coordinateKernel
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i v => A i (y i) v * B i v (x i))).symm

theorem four_coordinate_kernel {V : Type*} (A : Fin 4 → V → V → ℝ) :
    coordinateKernel A = reindexKernel (fourTupleEquiv V) (tensorFour (A 0) (A 1) (A 2) (A 3)) := by
  funext y x
  simp only [coordinateKernel, reindexKernel, tensorFour, tensorKernel, fourTupleEquiv,
    Equiv.coe_fn_mk, Fin.prod_univ_four]
  ring

theorem four_coordinate_energy {V : Type*} [Fintype V]
    (A : Fin 4 → V → V → ℝ) (s : Fin 4 → ℝ)
    (h : ∀ i f, (∑ y, action (A i) f y^2) ≤ (s i)^2 * ∑ x, f x^2)
    (f : (Fin 4 → V) → ℝ) :
    (∑ y, action (coordinateKernel A) f y^2) ≤ (∏ i, s i)^2 * ∑ x, f x^2 := by
  rw [four_coordinate_kernel]
  have he := reindexKernel_energy (fourTupleEquiv V)
    (tensorFour (A 0) (A 1) (A 2) (A 3)) (s 0*s 1*(s 2*s 3))
    (tensorFour_energy _ _ _ _ _ _ _ _ (h 0) (h 1) (h 2) (h 3)) f
  convert he using 1
  simp only [Fin.prod_univ_four]
  ring

theorem four_coordinate_byte_piece_energy {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (a : Fin 4 → Bool) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ y, action (coordinateKernel (fun i => bytePiece D (a i))) f y^2) ≤
      (∏ i, bytePieceBound (a i))^2 * ∑ x, f x^2 :=
  four_coordinate_energy _ _ (fun i => bytePiece_energy h (a i)) f

end AESMixing
