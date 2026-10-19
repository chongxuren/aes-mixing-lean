import AESMixing.ProductFourier

/-!
# Rectangular counting-energy transport by product Fourier

The input and output tuple types may differ. A bound means a counting-energy
inequality for every real signed input, with no source independence premise.
The matrix Fourier transform is F_out M F_in^T: the input factor is explicitly
transposed before symmetry identifies its action with F_in. Reshaping is an
exact equivalence of physical positions, retaining all counting normalizations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RectangularFourier
open AESMixing

section Rectangular
variable {Y X : Type*} [Fintype Y] [Fintype X]

/-- Counting-measure action of a rectangular real matrix. -/
def rectAction (M : Y → X → ℝ) (f : X → ℝ) (y : Y) : ℝ :=
  ∑ x : X, M y x * f x

/-- The coefficient is squared; all real signed joint input functions occur. -/
def EnergyBound (M : Y → X → ℝ) (c : ℝ) : Prop :=
  ∀ f : X → ℝ, (∑ y : Y, rectAction M f y ^ 2) ≤ c ^ 2 * ∑ x : X, f x ^ 2

end Rectangular

section Fourier
variable {O I V : Type*} [Fintype O] [DecidableEq O]
  [Fintype I] [DecidableEq I] [AddCommGroup V] [Fintype V]

/-- Product Fourier on the vectorized matrix, with the input leg transposed. -/
def fourierTransform (B : CharacterPairing V)
    (M : (O → V) → (I → V) → ℝ) : (O → V) → (I → V) → ℝ :=
  fun y x => ∑ v : O → V, ∑ w : I → V,
    pairingFourier (B.product O) y v * pairingFourier (B.product I) x w * M v w

/-- Coordinatewise exponent two supplies the involution premise on any tuple. -/
theorem tuple_add_self {K : Type*} (hchar : ∀ x : V, x + x = 0) (x : K → V) :
    x + x = 0 := by
  funext k
  exact hchar (x k)

/-- The right Fourier matrix enters the action through its transpose. Its
symmetry is proved by the pairing API, rather than assumed for a residual. -/
theorem fourierTransform_action (B : CharacterPairing V)
    (M : (O → V) → (I → V) → ℝ) (f : (I → V) → ℝ) :
    rectAction (fourierTransform B M) f =
      action (pairingFourier (B.product O))
        (rectAction M (action (pairingFourier (B.product I)) f)) := by
  funext y
  unfold rectAction fourierTransform action
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro x _
  rw [pairingFourier_symmetric (B.product I) x w]
  ring

/-- The output Fourier isometry removes only the output factor. The input
remains Fourier transformed, as required for arbitrary-input norm transport. -/
theorem fourierTransform_energy (B : CharacterPairing V)
    (hchar : ∀ x : V, x + x = 0)
    (M : (O → V) → (I → V) → ℝ) (f : (I → V) → ℝ) :
    (∑ y : O → V, rectAction (fourierTransform B M) f y ^ 2) =
      ∑ y : O → V,
        rectAction M (action (pairingFourier (B.product I)) f) y ^ 2 := by
  rw [fourierTransform_action]
  exact pairingFourier_energy (B.product O) (tuple_add_self hchar) _

/-- Two real Fourier isometries preserve every signed-input energy bound. -/
theorem energyBound_fourierTransform (B : CharacterPairing V)
    (hchar : ∀ x : V, x + x = 0)
    (M : (O → V) → (I → V) → ℝ) (c : ℝ) (hM : EnergyBound M c) :
    EnergyBound (fourierTransform B M) c := by
  intro f
  rw [fourierTransform_energy B hchar]
  have h := hM (action (pairingFourier (B.product I)) f)
  rw [pairingFourier_energy (B.product I) (tuple_add_self hchar)] at h
  exact h

/-- Equivalence, rather than just one implication: input involution supplies
every original signed vector as a Fourier-transformed signed vector. -/
theorem energyBound_fourierTransform_iff (B : CharacterPairing V)
    (hchar : ∀ x : V, x + x = 0)
    (M : (O → V) → (I → V) → ℝ) (c : ℝ) :
    EnergyBound (fourierTransform B M) c ↔ EnergyBound M c := by
  constructor
  · intro h f
    have h' := h (action (pairingFourier (B.product I)) f)
    rw [fourierTransform_energy B hchar,
      pairingFourier_twice (B.product I) (tuple_add_self hchar),
      pairingFourier_energy (B.product I) (tuple_add_self hchar)] at h'
    exact h'
  · exact energyBound_fourierTransform B hchar M c

end Fourier

section Reshape
variable {O I K V : Type*} [Fintype O] [DecidableEq O]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

/-- Joining follows the supplied physical output/input position equivalence. -/
def join (idx : O ⊕ I ≃ K) (y : O → V) (x : I → V) : K → V :=
  fun k => Sum.elim y x (idx.symm k)

@[simp] theorem join_inl (idx : O ⊕ I ≃ K) (y : O → V) (x : I → V) (i : O) :
    join idx y x (idx (Sum.inl i)) = y i := by
  simp only [join, Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem join_inr (idx : O ⊕ I ≃ K) (y : O → V) (x : I → V) (i : I) :
    join idx y x (idx (Sum.inr i)) = x i := by
  simp only [join, Equiv.symm_apply_apply, Sum.elim_inr]

/-- The tuple equivalence certifies the reindexing of both matrix dimensions. -/
def tupleEquiv (idx : O ⊕ I ≃ K) : (K → V) ≃ (O → V) × (I → V) where
  toFun v := (fun i => v (idx (Sum.inl i)), fun i => v (idx (Sum.inr i)))
  invFun v := join idx v.1 v.2
  left_inv v := by
    funext k
    change Sum.elim (fun i => v (idx (Sum.inl i)))
      (fun i => v (idx (Sum.inr i))) (idx.symm k) = v k
    have he (p : O ⊕ I) : Sum.elim (fun i => v (idx (Sum.inl i)))
        (fun i => v (idx (Sum.inr i))) p = v (idx p) := by
      cases p <;> rfl
    rw [he, idx.apply_symm_apply]
  right_inv v := by
    apply Prod.ext <;> funext i <;> simp only [join_inl, join_inr]

def reshape (idx : O ⊕ I ≃ K) (v : (K → V) → ℝ) : (O → V) → (I → V) → ℝ :=
  fun y x => v (join idx y x)

variable [Fintype V]

theorem sum_tuples (idx : O ⊕ I ≃ K) (f : (K → V) → ℝ) :
    (∑ v : K → V, f v) =
      ∑ y : O → V, ∑ x : I → V, f (join idx y x) := by
  calc
    _ = ∑ yx : (O → V) × (I → V), f ((tupleEquiv idx).symm yx) :=
      ((tupleEquiv idx).symm.sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      rfl

theorem coordinateKernel_join (idx : O ⊕ I ≃ K)
    (T : K → V → V → ℝ) (y v : O → V) (x w : I → V) :
    coordinateKernel T (join idx y x) (join idx v w) =
      coordinateKernel (fun i => T (idx (Sum.inl i))) y v *
        coordinateKernel (fun i => T (idx (Sum.inr i))) x w := by
  unfold coordinateKernel
  rw [← idx.prod_comp (fun k => T k (join idx y x k) (join idx v w k)),
    Fintype.prod_sum_type]
  simp only [join_inl, join_inr]

variable [AddCommGroup V]

/-- The product normalization factors exactly across the physical split. -/
theorem pairingFourier_join (idx : O ⊕ I ≃ K) (B : CharacterPairing V)
    (y v : O → V) (x w : I → V) :
    pairingFourier (B.product K) (join idx y x) (join idx v w) =
      pairingFourier (B.product O) y v * pairingFourier (B.product I) x w := by
  rw [productPairing_fourier, coordinateKernel_join,
    ← productPairing_fourier, ← productPairing_fourier]

/-- Exact reshape/product-Fourier identity F_out M F_in^T, for an arbitrary
physical position equivalence. It is stronger than total vector energy. -/
theorem reshape_fourier (idx : O ⊕ I ≃ K) (B : CharacterPairing V)
    (v : (K → V) → ℝ) :
    reshape idx (action (pairingFourier (B.product K)) v) =
      fourierTransform B (reshape idx v) := by
  funext y x
  unfold reshape action fourierTransform
  rw [sum_tuples idx]
  simp_rw [pairingFourier_join]

/-- Every signed-input rectangular bound survives full-vector Fourier after
the exact physical reshape. No desired numerical bound is a premise here. -/
theorem energyBound_reshape_fourier_iff (idx : O ⊕ I ≃ K)
    (B : CharacterPairing V) (hchar : ∀ x : V, x + x = 0)
    (v : (K → V) → ℝ) (c : ℝ) :
    EnergyBound (reshape idx (action (pairingFourier (B.product K)) v)) c ↔
      EnergyBound (reshape idx v) c := by
  rw [reshape_fourier]
  exact energyBound_fourierTransform_iff B hchar (reshape idx v) c

end Reshape
end AESPaper.RectangularFourier
