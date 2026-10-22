import AESConcrete.GraphColumnEnergy
import AESConcrete.FourierGraphEnergy
import AESMixing.Product

/-!
# Partial-graph tensor energy on arbitrary finite physical labels

A decidable predicate marks the free physical labels; its complement is the
dependent tuple. The explicit split preserves every original label and exact
counting energy. Free labels require operator bounds; dependent labels require
only their individual nonnegative column-energy caps. The input is one
arbitrary signed joint real function, with no coordinate independence premise.

Future generic candidate only, outside the current retained-graph seven-source
inventory. No AES geometry, physical cap, inventory increment or accepted result
is asserted. The optional Fourier wrapper assumes its own transformed-input
partial-graph premise and uses exact common-kernel conjugation identities.
Constructive mathematics only; no attacks or application execution. Independent
uniform retained keys, whitening, omitted final MixColumns, ordered-distinct
pairs and the fixed 10/14/16 target stay unchanged. Accepted/current candidate
sources, tooling, manuscripts, objectives, memory and schedules are frozen.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.IndexedGraphEnergy
open AESMixing

variable {I V : Type*}

/-- Free labels retain their original physical identities. -/
abbrev FreeCoordinates (p : I → Prop) := {i : I // p i}

/-- All labels not marked free are grouped into the dependent tuple. -/
abbrev DependentCoordinates (p : I → Prop) := {i : I // ¬ p i}

def joinCoordinates (p : I → Prop) [DecidablePred p]
    (v : DependentCoordinates p → V) (w : FreeCoordinates p → V) (i : I) : V :=
  if h : p i then w ⟨i, h⟩ else v ⟨i, h⟩

/-- Dependent coordinates come first, matching `GraphColumnEnergy`.
Neither tuple is enumerated or replaced by a cardinality-equivalent type. -/
def splitCoordinates (p : I → Prop) [DecidablePred p] :
    (I → V) ≃ (DependentCoordinates p → V) × (FreeCoordinates p → V) where
  toFun x := (fun i => x i.val, fun i => x i.val)
  invFun t := joinCoordinates p t.1 t.2
  left_inv x := by
    funext i
    by_cases h : p i <;> simp [joinCoordinates, h]
  right_inv t := by
    apply Prod.ext
    · funext i
      simp [joinCoordinates, i.property]
    · funext i
      simp [joinCoordinates, i.property]

section FiniteLabels
variable [Fintype I]

/-- Pure kernel reindexing on the actual free/dependent label subtypes. -/
theorem coordinateKernel_split (T : I → V → V → ℝ)
    (p : I → Prop) [DecidablePred p] :
    coordinateKernel T = reindexKernel (splitCoordinates p)
      (tensorKernel
        (coordinateKernel (fun j : DependentCoordinates p => T j.val))
        (coordinateKernel (fun i : FreeCoordinates p => T i.val))) := by
  funext y x
  change (∏ i : I, T i (y i) (x i)) =
    (∏ j : DependentCoordinates p, T j.val (y j.val) (x j.val)) *
      ∏ i : FreeCoordinates p, T i.val (y i.val) (x i.val)
  rw [← Fintype.prod_subtype_mul_prod_subtype p]
  exact mul_comm _ _

-- Decidable coordinate equality is needed for function-space counting, not
-- for the pure product/kernel split above.
variable [DecidableEq I] [Fintype V]

/-- Counting energy is exactly preserved by the label split. No source
normalization, fiber cardinality or product-input premise is introduced. -/
theorem splitCoordinates_input_energy (p : I → Prop) [DecidablePred p]
    (f : (I → V) → ℝ) :
    (∑ x, f ((splitCoordinates p).symm x) ^ 2) = ∑ x, f x ^ 2 :=
  (splitCoordinates p).symm.sum_comp (fun x => f x ^ 2)

variable [Nonempty V]

/-- Heterogeneous graph energy for any finite physical label type, including
empty free or dependent label sets. The entire dependent tuple is uniquely
determined wherever the input is nonzero over one complete free tuple. -/
theorem coordinate_partial_graph_energy
    (T : I → V → V → ℝ) (p : I → Prop) [DecidablePred p]
    (nu : FreeCoordinates p → ℝ) (delta : DependentCoordinates p → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j)
    (hT : ∀ (i : FreeCoordinates p) (g : V → ℝ),
      (∑ y, action (T i.val) g y ^ 2) ≤ nu i ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ (j : DependentCoordinates p) (v : V),
      (∑ y, T j.val y v ^ 2) ≤ delta j)
    (f : (I → V) → ℝ)
    (hgraph : ∀ (w : FreeCoordinates p → V) (v v' : DependentCoordinates p → V),
      f ((splitCoordinates p).symm (v, w)) ≠ 0 →
      f ((splitCoordinates p).symm (v', w)) ≠ 0 → v = v') :
    (∑ y, action (coordinateKernel T) f y ^ 2) ≤
      (∏ i : FreeCoordinates p, nu i) ^ 2 *
        (∏ j : DependentCoordinates p, delta j) * ∑ x, f x ^ 2 := by
  let e := splitCoordinates (V := V) p
  let B := coordinateKernel (fun j : DependentCoordinates p => T j.val)
  let A := coordinateKernel (fun i : FreeCoordinates p => T i.val)
  let a : ℝ := ∏ i : FreeCoordinates p, nu i
  let D : ℝ := ∏ j : DependentCoordinates p, delta j
  let c : ℝ := Real.sqrt D
  have hD : 0 ≤ D := Finset.prod_nonneg (fun j _ => hdelta j)
  have hc : c ^ 2 = D := Real.sq_sqrt hD
  have hA : ∀ g : (FreeCoordinates p → V) → ℝ,
      (∑ y, action A g y ^ 2) ≤ a ^ 2 * ∑ x, g x ^ 2 :=
    FiniteTensorEnergy.coordinate_energy
      (fun i : FreeCoordinates p => T i.val) nu hT
  have hB : ∀ v : DependentCoordinates p → V,
      (∑ y, B y v ^ 2) ≤ c ^ 2 := by
    intro v
    rw [hc]
    change (∑ y : DependentCoordinates p → V,
      (∏ j : DependentCoordinates p, T j.val (y j) (v j)) ^ 2) ≤
        ∏ j : DependentCoordinates p, delta j
    rw [product_column_energy (fun j y => T j.val y (v j))]
    exact Finset.prod_le_prod
      (fun j _ => Finset.sum_nonneg (fun y _ => sq_nonneg (T j.val y (v j))))
      (fun j _ => hcolumn j (v j))
  have hfiber : ∀ (w : FreeCoordinates p → V) (v v' : DependentCoordinates p → V),
      (f ∘ e.symm) (v, w) ≠ 0 → (f ∘ e.symm) (v', w) ≠ 0 → v = v' := hgraph
  have he := GraphColumnEnergy.tensor_partial_graph_energy B A a c hA hB
    (f ∘ e.symm) hfiber
  have hn : (∑ x, (f ∘ e.symm) x ^ 2) = ∑ x, f x ^ 2 :=
    splitCoordinates_input_energy p f
  rw [hn, hc] at he
  rw [coordinateKernel_split T p]
  simp_rw [reindexKernel_action]
  rw [e.sum_comp (fun y => action (tensorKernel B A) (f ∘ e.symm) y ^ 2)]
  exact he

end FiniteLabels

section Fourier
variable [Fintype I] [DecidableEq I] [AddCommGroup V] [Fintype V]

/-- Fourier wrapper for one common coordinate kernel. The free/dependent
resources concern its actual two-sided conjugate, and the graph premise
concerns the actual product-Fourier input. No geometric instance is inferred. -/
theorem coordinate_fourier_partial_graph_energy
    (B : CharacterPairing V) (hchar : ∀ x : V, x + x = 0)
    (T : V → V → ℝ) (p : I → Prop) [DecidablePred p]
    (nu : FreeCoordinates p → ℝ) (delta : DependentCoordinates p → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j)
    (hT : ∀ (i : FreeCoordinates p) (g : V → ℝ),
      (∑ y, action (fourierConjugate B T) g y ^ 2) ≤ nu i ^ 2 * ∑ x, g x ^ 2)
    (hcolumn : ∀ (j : DependentCoordinates p) (v : V),
      (∑ y, fourierConjugate B T y v ^ 2) ≤ delta j)
    (f : (I → V) → ℝ)
    (hgraph : ∀ (w : FreeCoordinates p → V) (v v' : DependentCoordinates p → V),
      action (coordinateKernel (fun _ : I => pairingFourier B)) f
        ((splitCoordinates p).symm (v, w)) ≠ 0 →
      action (coordinateKernel (fun _ : I => pairingFourier B)) f
        ((splitCoordinates p).symm (v', w)) ≠ 0 → v = v') :
    (∑ y, action (coordinateKernel (fun _ : I => T)) f y ^ 2) ≤
      (∏ i : FreeCoordinates p, nu i) ^ 2 *
        (∏ j : DependentCoordinates p, delta j) * ∑ x, f x ^ 2 := by
  have he := coordinate_partial_graph_energy
    (fun _ : I => fourierConjugate B T) p nu delta hdelta hT hcolumn
    (action (coordinateKernel (fun _ : I => pairingFourier B)) f) hgraph
  rw [FourierGraphEnergy.coordinate_fourier_conjugation_energy B hchar T f,
    FourierGraphEnergy.coordinate_fourier_input_energy B hchar f] at he
  exact he

end Fourier
end AESConcrete.IndexedGraphEnergy
