import AES8.Math.InformationEncoding

/-!
# Rectangular information-set encoding energy

This leaf extends the existing real counting-measure argument to rectangular
local matrices.  It proves the tensor estimate from individual local estimates;
the encoded estimate is a conclusion, never an assumed interface.
The literal physical-coordinate operator and its norm belong to PaperEncoding.
Constructive validation only; no attacks or numerical computations.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperEncodingEnergy
open AESMixing

variable {V W : Type*} [Fintype V] [Fintype W]

def coordinateKernel {I : Type*} [Fintype I]
    (A : I → W → V → ℝ) (y : I → W) (x : I → V) : ℝ :=
  ∏ i, A i (y i) (x i)

/-- Independent input/output coordinate changes preserve counting energy. -/
theorem reindex_energy {X X' Y Y' : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] [Fintype Y']
    (ex : X ≃ X') (ey : Y ≃ Y') (K : Y' → X' → ℝ) (b : ℝ)
    (h : ∀ f, (∑ y, action K f y ^ 2) ≤ b ^ 2 * ∑ x, f x ^ 2)
    (f : X → ℝ) :
    (∑ y, action (fun y x => K (ey y) (ex x)) f y ^ 2) ≤
      b ^ 2 * ∑ x, f x ^ 2 := by
  have ha (y : Y) :
      action (fun y x => K (ey y) (ex x)) f y =
        action K (fun x => f (ex.symm x)) (ey y) := by
    unfold action
    simpa only [ex.symm_apply_apply] using
      ex.sum_comp (fun x => K (ey y) x * f (ex.symm x))
  simp_rw [ha]
  rw [ey.sum_comp (fun y => action K (fun x => f (ex.symm x)) y ^ 2)]
  have he := h (fun x => f (ex.symm x))
  simpa only [ex.symm.sum_comp (fun x => f x ^ 2)] using he

/-- Rectangular tensorization for an arbitrary finite tuple. -/
theorem fin_coordinate_energy : ∀ (n : ℕ) (A : Fin n → W → V → ℝ)
    (ν : Fin n → ℝ),
    (∀ i f, (∑ y, action (A i) f y ^ 2) ≤ ν i ^ 2 * ∑ x, f x ^ 2) →
    ∀ f : (Fin n → V) → ℝ,
      (∑ y, action (coordinateKernel A) f y ^ 2) ≤
        (∏ i, ν i) ^ 2 * ∑ x, f x ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro A ν h f
    simp [coordinateKernel, action]
  | succ n ih =>
    intro A ν h f
    have hk : coordinateKernel A =
        fun y x => tensorKernel (A 0) (coordinateKernel (fun i : Fin n => A i.succ))
          (AESConcrete.FiniteTensorEnergy.consTupleEquiv n y)
          (AESConcrete.FiniteTensorEnergy.consTupleEquiv n x) := by
      funext y x
      simp only [coordinateKernel, tensorKernel,
        AESConcrete.FiniteTensorEnergy.consTupleEquiv, Equiv.coe_fn_mk,
        Fin.prod_univ_succ]
    rw [hk]
    have he := reindex_energy
      (AESConcrete.FiniteTensorEnergy.consTupleEquiv (V := V) n)
      (AESConcrete.FiniteTensorEnergy.consTupleEquiv (V := W) n)
      (tensorKernel (A 0) (coordinateKernel (fun i : Fin n => A i.succ)))
      (ν 0 * ∏ i : Fin n, ν i.succ)
      (tensorKernel_energy (A 0) (coordinateKernel (fun i : Fin n => A i.succ))
        (ν 0) (∏ i : Fin n, ν i.succ) (h 0)
        (ih (fun i => A i.succ) (fun i => ν i.succ) (fun i => h i.succ))) f
    simpa only [Fin.prod_univ_succ] using he

/-- Arbitrary finite information-coordinate index, including dimension zero. -/
theorem coordinate_energy {I : Type*} [Fintype I] [DecidableEq I]
    (A : I → W → V → ℝ) (ν : I → ℝ)
    (h : ∀ i f, (∑ y, action (A i) f y ^ 2) ≤ ν i ^ 2 * ∑ x, f x ^ 2)
    (f : (I → V) → ℝ) :
    (∑ y, action (coordinateKernel A) f y ^ 2) ≤
      (∏ i, ν i) ^ 2 * ∑ x, f x ^ 2 := by
  let e := Fintype.equivFin I
  have hk : coordinateKernel A = fun y x =>
      coordinateKernel (fun k => A (e.symm k))
        (AESConcrete.FiniteTensorEnergy.indexTupleEquiv e y)
        (AESConcrete.FiniteTensorEnergy.indexTupleEquiv e x) := by
    funext y x
    exact (e.symm.prod_comp (fun i => A i (y i) (x i))).symm
  rw [hk]
  have he := reindex_energy
    (AESConcrete.FiniteTensorEnergy.indexTupleEquiv (V := V) e)
    (AESConcrete.FiniteTensorEnergy.indexTupleEquiv (V := W) e)
    (coordinateKernel (fun k => A (e.symm k))) (∏ k, ν (e.symm k))
    (fin_coordinate_energy (Fintype.card I) (fun k => A (e.symm k))
      (fun k => ν (e.symm k)) (fun k => h (e.symm k))) f
  rw [e.symm.prod_comp ν] at he
  exact he

variable {C I J : Type*} [Fintype C] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

/-- Split-coordinate kernel of the literal tensor columns. -/
def kernel (e : C ≃ (I → V)) (rest : C → J → V)
    (A : I → W → V → ℝ) (B : J → W → V → ℝ)
    (y : (I → W) × (J → W)) (c : C) : ℝ :=
  (∏ i, A i (y.1 i) (e c i)) * ∏ j, B j (y.2 j) (rest c j)

theorem remaining_energy (B : J → W → V → ℝ) (δ : ℝ)
    (hB : ∀ j x, (∑ y, B j y x ^ 2) ≤ δ) (x : J → V) :
    (∑ y : J → W, (∏ j, B j (y j) (x j)) ^ 2) ≤ δ ^ Fintype.card J := by
  calc
    _ = ∏ j : J, ∑ y : W, B j y (x j) ^ 2 := by
      simp_rw [← Finset.prod_pow]
      exact (Fintype.prod_sum (fun j y => B j y (x j) ^ 2)).symm
    _ ≤ ∏ _ : J, δ := Finset.prod_le_prod
      (fun j _ => Finset.sum_nonneg (fun y _ => sq_nonneg _)) (fun j _ => hB j _)
    _ = δ ^ Fintype.card J := by simp

theorem action_factor (e : C ≃ (I → V)) (rest : C → J → V)
    (A : I → W → V → ℝ) (B : J → W → V → ℝ) (f : C → ℝ)
    (y : I → W) (z : J → W) :
    action (kernel e rest A B) f (y,z) =
      action (coordinateKernel A)
        (fun x => f (e.symm x) * ∏ j, B j (z j) (rest (e.symm x) j)) y := by
  unfold action kernel coordinateKernel
  rw [← e.symm.sum_comp (fun c =>
    ((∏ i, A i (y i) (e c i)) * ∏ j, B j (z j) (rest c j)) * f c)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [e.apply_symm_apply]
  ring

/-- The encoded energy bound, for arbitrary signed and correlated coefficients. -/
theorem encoding_energy (e : C ≃ (I → V)) (rest : C → J → V)
    (A : I → W → V → ℝ) (B : J → W → V → ℝ) (ν : I → ℝ) (δ : ℝ)
    (hA : ∀ i g, (∑ y, action (A i) g y ^ 2) ≤ ν i ^ 2 * ∑ x, g x ^ 2)
    (hB : ∀ j x, (∑ y, B j y x ^ 2) ≤ δ) (f : C → ℝ) :
    (∑ y, action (kernel e rest A B) f y ^ 2) ≤
      (∏ i, ν i) ^ 2 * δ ^ Fintype.card J * ∑ c, f c ^ 2 := by
  have hrest : (∑ x : I → V, ∑ z : J → W,
      (f (e.symm x) * ∏ j, B j (z j) (rest (e.symm x) j)) ^ 2) ≤
      δ ^ Fintype.card J * ∑ c, f c ^ 2 := by
    calc
      _ = ∑ x : I → V, f (e.symm x) ^ 2 *
          ∑ z : J → W, (∏ j, B j (z j) (rest (e.symm x) j)) ^ 2 := by
        simp_rw [mul_pow, ← Finset.mul_sum]
      _ ≤ ∑ x : I → V, f (e.symm x) ^ 2 * δ ^ Fintype.card J :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left
          (remaining_energy B δ hB (rest (e.symm x))) (sq_nonneg _))
      _ = δ ^ Fintype.card J * ∑ c, f c ^ 2 := by
        rw [← Finset.sum_mul, e.symm.sum_comp (fun c => f c ^ 2)]
        ring
  simp only [Fintype.sum_prod_type, action_factor]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ z : J → W, (∏ i, ν i) ^ 2 * ∑ x : I → V,
        (f (e.symm x) * ∏ j, B j (z j) (rest (e.symm x) j)) ^ 2 :=
      Finset.sum_le_sum (fun z _ => coordinate_energy A ν hA _)
    _ = (∏ i, ν i) ^ 2 * ∑ x : I → V, ∑ z : J → W,
        (f (e.symm x) * ∏ j, B j (z j) (rest (e.symm x) j)) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left hrest (sq_nonneg (∏ i, ν i))
      simpa only [mul_assoc] using hb

end AES8.PaperEncodingEnergy
