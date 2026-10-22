import AESConcrete.FiniteTensorEnergy

/-!
# Tensor energy on a graph-supported input

The input coordinate omitted from an operator-energy estimate may be recovered
as a function of the other coordinates. In that case its kernel needs only a
column-energy bound. Slice on its output, apply the energy estimate on the
remaining coordinates, and then sum its column energy. All input weights are
arbitrary signed real functions; no product-law assumption is made.

This is a generic finite-kernel lemma. It does not construct an AES graph or
assert an AES source instance. The intended application retains independent
uniform retained keys, whitening, omitted final MixColumns, and ordered-distinct
pairs. Constructive bounds only; no attack development or manuscript changes.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.GraphColumnEnergy
open AESMixing

variable {V W Y Z : Type*}

/-- The rectangular kernel obtained by restricting the input of `B ⊗ A` to
the graph `v = g w`. Its input is indexed only by the free coordinate `w`. -/
def graphKernel (B : Y → V → ℝ) (A : Z → W → ℝ) (g : W → V) :
    Y × Z → W → ℝ :=
  fun y x => B y.1 (g x) * A y.2 x

/-- Support on the graph of `g`; no sign or normalization condition is imposed. -/
def SupportedOnGraph (g : W → V) (h : V × W → ℝ) : Prop :=
  ∀ v w, v ≠ g w → h (v, w) = 0

/-- A partial graph can be extended to a total graph. Empty fibers are filled
by an arbitrary point of `V`; nonempty fibers use their unique nonzero point.
This is classical choice and does not enumerate either coordinate type. -/
theorem exists_supported_graph_of_fiber_unique [Nonempty V]
    (h : V × W → ℝ)
    (hunique : ∀ w v v', h (v, w) ≠ 0 → h (v', w) ≠ 0 → v = v') :
    ∃ g : W → V, SupportedOnGraph g h := by
  classical
  have hpoint : ∀ w, ∃ v, ∀ v', h (v', w) ≠ 0 → v' = v := by
    intro w
    by_cases hex : ∃ v, h (v, w) ≠ 0
    · obtain ⟨v, hv⟩ := hex
      exact ⟨v, fun v' hv' => hunique w v' v hv' hv⟩
    · refine ⟨Classical.choice (inferInstance : Nonempty V), ?_⟩
      intro v' hv'
      exact False.elim (hex ⟨v', hv'⟩)
  let g : W → V := fun w => Classical.choose (hpoint w)
  refine ⟨g, ?_⟩
  intro v w hvg
  by_contra hv
  exact hvg (Classical.choose_spec (hpoint w) v hv)

variable [Fintype W]

theorem graphKernel_action (B : Y → V → ℝ) (A : Z → W → ℝ)
    (g : W → V) (μ : W → ℝ) (y : Y × Z) :
    action (graphKernel B A g) μ y =
      action A (fun x => μ x * B y.1 (g x)) y.2 := by
  unfold action graphKernel
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The exact weighted bound before replacing graph-column energies by a cap.
The proof is the common-source slicing argument, with no independence premise. -/
theorem graphKernel_weighted_energy [Fintype Y] [Fintype Z]
    (B : Y → V → ℝ) (A : Z → W → ℝ) (g : W → V) (a : ℝ)
    (hA : ∀ f : W → ℝ,
      (∑ y, action A f y ^ 2) ≤ a ^ 2 * ∑ x, f x ^ 2)
    (μ : W → ℝ) :
    (∑ y, action (graphKernel B A g) μ y ^ 2) ≤
      a ^ 2 * ∑ x, μ x ^ 2 * ∑ y, B y (g x) ^ 2 := by
  simp only [Fintype.sum_prod_type, graphKernel_action]
  calc
    (∑ b, ∑ z, action A (fun x => μ x * B b (g x)) z ^ 2)
        ≤ ∑ b, a ^ 2 * ∑ x, (μ x * B b (g x)) ^ 2 :=
      Finset.sum_le_sum (fun b _ => hA (fun x => μ x * B b (g x)))
    _ = a ^ 2 * ∑ x, μ x ^ 2 * ∑ b, B b (g x) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [mul_pow, Finset.mul_sum]

/-- Graph-column bound for every joint graph input. The factor `B` requires
only a bound on each column, whereas `A` requires an operator-energy bound. -/
theorem graphKernel_energy [Fintype Y] [Fintype Z]
    (B : Y → V → ℝ) (A : Z → W → ℝ) (g : W → V) (a c : ℝ)
    (hA : ∀ f : W → ℝ,
      (∑ y, action A f y ^ 2) ≤ a ^ 2 * ∑ x, f x ^ 2)
    (hB : ∀ v, (∑ y, B y v ^ 2) ≤ c ^ 2)
    (μ : W → ℝ) :
    (∑ y, action (graphKernel B A g) μ y ^ 2) ≤
      a ^ 2 * c ^ 2 * ∑ x, μ x ^ 2 := by
  calc
    (∑ y, action (graphKernel B A g) μ y ^ 2)
        ≤ a ^ 2 * ∑ x, μ x ^ 2 * ∑ y, B y (g x) ^ 2 :=
      graphKernel_weighted_energy B A g a hA μ
    _ ≤ a ^ 2 * ∑ x, μ x ^ 2 * c ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg a)
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_left (hB (g x)) (sq_nonneg (μ x))
    _ = a ^ 2 * c ^ 2 * ∑ x, μ x ^ 2 := by
      rw [← Finset.sum_mul]
      ring

variable [Fintype V]

/-- A graph-supported vector has exactly the energy of its free-coordinate
restriction. This identity also covers empty coordinate types. -/
theorem graph_supported_sq_sum (g : W → V) (h : V × W → ℝ)
    (hsupport : SupportedOnGraph g h) :
    (∑ x, h x ^ 2) = ∑ w, h (g w, w) ^ 2 := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.sum_eq_single (g w)
    (fun v _ hv => by rw [hsupport v w hv]; simp) (by simp)

/-- Restricting a tensor action to graph-supported inputs gives `graphKernel`.
This is an action identity, separate from the energy estimate. -/
theorem tensor_graph_supported_action (B : Y → V → ℝ) (A : Z → W → ℝ)
    (g : W → V) (h : V × W → ℝ) (hsupport : SupportedOnGraph g h)
    (y : Y × Z) :
    action (tensorKernel B A) h y =
      action (graphKernel B A g) (fun w => h (g w, w)) y := by
  classical
  simp only [action, tensorKernel, graphKernel, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  exact Finset.sum_eq_single (g w)
    (fun v _ hv => by rw [hsupport v w hv, mul_zero]) (by simp)

/-- The tensor bound in the original product-input indexing. The support
premise permits arbitrary correlations among all free input coordinates. -/
theorem tensor_graph_supported_energy [Fintype Y] [Fintype Z]
    (B : Y → V → ℝ) (A : Z → W → ℝ) (g : W → V) (a c : ℝ)
    (hA : ∀ f : W → ℝ,
      (∑ y, action A f y ^ 2) ≤ a ^ 2 * ∑ x, f x ^ 2)
    (hB : ∀ v, (∑ y, B y v ^ 2) ≤ c ^ 2)
    (h : V × W → ℝ) (hsupport : SupportedOnGraph g h) :
    (∑ y, action (tensorKernel B A) h y ^ 2) ≤
      a ^ 2 * c ^ 2 * ∑ x, h x ^ 2 := by
  simp_rw [tensor_graph_supported_action B A g h hsupport]
  have he := graphKernel_energy B A g a c hA hB (fun w => h (g w, w))
  rw [← graph_supported_sq_sum g h hsupport] at he
  exact he

/-- The same tensor bound when support is only known to be a partial graph:
each free-coordinate fiber contains at most one nonzero input coordinate. -/
theorem tensor_partial_graph_energy [Nonempty V] [Fintype Y] [Fintype Z]
    (B : Y → V → ℝ) (A : Z → W → ℝ) (a c : ℝ)
    (hA : ∀ f : W → ℝ,
      (∑ y, action A f y ^ 2) ≤ a ^ 2 * ∑ x, f x ^ 2)
    (hB : ∀ v, (∑ y, B y v ^ 2) ≤ c ^ 2)
    (h : V × W → ℝ)
    (hunique : ∀ w v v', h (v, w) ≠ 0 → h (v', w) ≠ 0 → v = v') :
    (∑ y, action (tensorKernel B A) h y ^ 2) ≤
      a ^ 2 * c ^ 2 * ∑ x, h x ^ 2 := by
  obtain ⟨g, hsupport⟩ := exists_supported_graph_of_fiber_unique h hunique
  exact tensor_graph_supported_energy B A g a c hA hB h hsupport

-- Editorial interface choice: the distinguished coordinate is explicit in a
-- product, while the free coordinates have an arbitrary finite index type.
-- A later coordinate permutation may select any inactive AES word; this module
-- does not supply or assume the graph relation for that application.

/-- Bridge from the arbitrary finite-coordinate tensor theorem: the graph
coordinate has column cap `c`, and all free coordinates tensorize normally. -/
theorem coordinate_graph_energy {I : Type*} [Fintype I] [DecidableEq I]
    (B : V → V → ℝ) (T : I → V → V → ℝ) (g : (I → V) → V)
    (s : I → ℝ) (c : ℝ)
    (hT : ∀ i f, (∑ y, action (T i) f y ^ 2) ≤
      (s i) ^ 2 * ∑ x, f x ^ 2)
    (hB : ∀ v, (∑ y, B y v ^ 2) ≤ c ^ 2)
    (μ : (I → V) → ℝ) :
    (∑ y, action (graphKernel B (coordinateKernel T) g) μ y ^ 2) ≤
      (∏ i, s i) ^ 2 * c ^ 2 * ∑ x, μ x ^ 2 :=
  graphKernel_energy B (coordinateKernel T) g (∏ i, s i) c
    (FiniteTensorEnergy.coordinate_energy T s hT) hB μ

/-- Product-indexed version of `coordinate_graph_energy`, for a vector whose
support is proved to lie on the graph of the distinguished coordinate. -/
theorem coordinate_tensor_graph_supported_energy
    {I : Type*} [Fintype I] [DecidableEq I]
    (B : V → V → ℝ) (T : I → V → V → ℝ) (g : (I → V) → V)
    (s : I → ℝ) (c : ℝ)
    (hT : ∀ i f, (∑ y, action (T i) f y ^ 2) ≤
      (s i) ^ 2 * ∑ x, f x ^ 2)
    (hB : ∀ v, (∑ y, B y v ^ 2) ≤ c ^ 2)
    (h : V × (I → V) → ℝ) (hsupport : SupportedOnGraph g h) :
    (∑ y, action (tensorKernel B (coordinateKernel T)) h y ^ 2) ≤
      (∏ i, s i) ^ 2 * c ^ 2 * ∑ x, h x ^ 2 :=
  tensor_graph_supported_energy B (coordinateKernel T) g (∏ i, s i) c
    (FiniteTensorEnergy.coordinate_energy T s hT) hB h hsupport

end AESConcrete.GraphColumnEnergy
