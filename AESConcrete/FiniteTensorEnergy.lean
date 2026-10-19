import AESMixing.CoordinateTensor
import AESMixing.FourTensor
import AESConcrete.ByteOrientations

/-!
# Finite-coordinate tensor energy on arbitrary joint inputs

This extends the existing two-factor tensor theorem to an arbitrary finite
coordinate index. The proof inducts on a finite tuple, then reindexes the
coordinate type by an actual equivalence. It assumes only the explicitly
given one-coordinate operator energy estimates. No product-law or positivity
assumption is imposed on the input vector. The final theorem specializes this
bound to the proved actual byte residual resources; no word-column or MDS
source instance is asserted. Constructive bounds only; no attacks or
manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.FiniteTensorEnergy
open AESMixing

variable {V : Type*} [Fintype V]

def consTupleEquiv (n : ℕ) : (Fin (n + 1) → V) ≃ V × (Fin n → V) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  right_inv _ := rfl

theorem fin_coordinate_energy : ∀ (n : ℕ) (T : Fin n → V → V → ℝ)
    (ν : Fin n → ℝ),
    (∀ i f, (∑ y, action (T i) f y ^ 2) ≤ (ν i) ^ 2 * ∑ x, f x ^ 2) →
    ∀ f : (Fin n → V) → ℝ,
      (∑ y, action (coordinateKernel T) f y ^ 2) ≤
        (∏ i, ν i) ^ 2 * ∑ x, f x ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro T ν h f
    simp [coordinateKernel, action]
  | succ n ih =>
    intro T ν h f
    have hk : coordinateKernel T = reindexKernel (consTupleEquiv (V := V) n)
        (tensorKernel (T 0) (coordinateKernel (fun i : Fin n => T i.succ))) := by
      funext y x
      simp only [coordinateKernel, reindexKernel, tensorKernel, consTupleEquiv,
        Equiv.coe_fn_mk, Fin.prod_univ_succ]
    rw [hk]
    have he := reindexKernel_energy (consTupleEquiv (V := V) n)
      (tensorKernel (T 0) (coordinateKernel (fun i : Fin n => T i.succ)))
      (ν 0 * ∏ i : Fin n, ν i.succ)
      (tensorKernel_energy (T 0) (coordinateKernel (fun i : Fin n => T i.succ))
        (ν 0) (∏ i : Fin n, ν i.succ) (h 0)
        (ih (fun i => T i.succ) (fun i => ν i.succ) (fun i => h i.succ))) f
    simpa only [Fin.prod_univ_succ] using he

def indexTupleEquiv {I K : Type*} (e : I ≃ K) : (I → V) ≃ (K → V) where
  toFun f k := f (e.symm k)
  invFun g i := g (e i)
  left_inv f := by funext i; simp
  right_inv g := by funext k; simp

/-- Tensorization for any finite coordinate type, including the empty type. -/
theorem coordinate_energy {I : Type*} [Fintype I] [DecidableEq I]
    (T : I → V → V → ℝ) (ν : I → ℝ)
    (h : ∀ i f, (∑ y, action (T i) f y ^ 2) ≤ (ν i) ^ 2 * ∑ x, f x ^ 2)
    (f : (I → V) → ℝ) :
    (∑ y, action (coordinateKernel T) f y ^ 2) ≤
      (∏ i, ν i) ^ 2 * ∑ x, f x ^ 2 := by
  let e := Fintype.equivFin I
  have hk : coordinateKernel T = reindexKernel (indexTupleEquiv (V := V) e)
      (coordinateKernel (fun k => T (e.symm k))) := by
    funext y x
    change (∏ i : I, T i (y i) (x i)) =
      ∏ k : Fin (Fintype.card I), T (e.symm k) (y (e.symm k)) (x (e.symm k))
    exact (e.symm.prod_comp (fun i => T i (y i) (x i))).symm
  rw [hk]
  have he := reindexKernel_energy (indexTupleEquiv (V := V) e)
    (coordinateKernel (fun k => T (e.symm k))) (∏ k, ν (e.symm k))
    (fin_coordinate_energy (Fintype.card I) (fun k => T (e.symm k))
      (fun k => ν (e.symm k)) (fun k => h (e.symm k))) f
  rw [e.symm.prod_comp ν] at he
  exact he

/-- Uniform one-coordinate energy coefficient, with the exponent retained
explicitly for the restricted-response application. -/
theorem uniform_coordinate_energy {I : Type*} [Fintype I] [DecidableEq I]
    (T : V → V → ℝ) (ν : ℝ)
    (h : ∀ f, (∑ y, action T f y ^ 2) ≤ ν ^ 2 * ∑ x, f x ^ 2)
    (f : (I → V) → ℝ) :
    (∑ y, action (coordinateKernel (fun _ : I => T)) f y ^ 2) ≤
      ν ^ (2 * Fintype.card I) * ∑ x, f x ^ 2 := by
  have he := coordinate_energy (fun _ : I => T) (fun _ : I => ν) (fun _ => h) f
  have hp : (∏ _ : I, ν) ^ 2 = ν ^ (2 * Fintype.card I) := by
    simp only [Finset.prod_const, Finset.card_univ]
    rw [← pow_mul, Nat.mul_comm]
  rw [hp] at he
  exact he

/-- Actual byte residual resources discharge every one-coordinate premise.
The orientation may be chosen separately on each coordinate. -/
theorem actual_byte_residual_coordinate_energy {I : Type*} [Fintype I] [DecidableEq I]
    (o : I → AESConcrete.ByteOrientations.Orientation)
    (f : (I → BinaryWord 8) → ℝ) :
    (∑ y, action (coordinateKernel (fun i =>
      residualMatrix (AESConcrete.ByteOrientations.channel (o i)) 0)) f y ^ 2) ≤
      (9 / 128 : ℝ) ^ (2 * Fintype.card I) * ∑ x, f x ^ 2 := by
  have he := coordinate_energy
    (fun i => residualMatrix (AESConcrete.ByteOrientations.channel (o i)) 0)
    (fun _ : I => (9 / 128 : ℝ)) (fun i g =>
      (AESConcrete.ByteOrientations.channel_resources (o i)).residual_matrix_energy g) f
  have hp : (∏ _ : I, (9 / 128 : ℝ)) ^ 2 =
      (9 / 128 : ℝ) ^ (2 * Fintype.card I) := by
    simp only [Finset.prod_const, Finset.card_univ]
    rw [← pow_mul, Nat.mul_comm]
  rw [hp] at he
  exact he

end AESConcrete.FiniteTensorEnergy
