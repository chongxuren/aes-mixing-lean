import AESConcrete.GeneralMDSGraphEnergy

/-!
# Heterogeneous coordinate energy on a partial graph

Only free-mask labels need operator-energy bounds. Each dependent label has
its own nonnegative column-energy cap. The input is one arbitrary signed joint
real function supported on a partial graph over the entire free tuple. Both
coordinate reindexings preserve exact counting energy.

This module is generic only; no AES specialization, physical cap or inventory
statement is made. Independent retained uniform keys, whitening, omitted final
MixColumns, ordered-distinct pairs and the fixed 10/14/16 target remain
unchanged.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.HeterogeneousGraphEnergy
open AESMixing
open AESConcrete.GeneralMDSGraphSupport (OtherCoordinates splitMask)
open AESConcrete.GeneralMDSGraphEnergy (coordinateKernel_splitMask)

variable {V : Type*} [Fintype V] [Nonempty V]

/-- Free labels receive only their own operator coefficients, while dependent
labels receive only their own column-energy caps. The partial-graph premise
allows arbitrary signs and joint dependence on the complete free tuple. -/
theorem coordinate_partial_graph_energy
    (T : Fin 4 → V → V → ℝ) (m : Fin 16)
    (nu : MaskCoordinates m → ℝ) (delta : OtherCoordinates m → ℝ)
    (hdelta : ∀ j, 0 ≤ delta j)
    (hT : ∀ (i : MaskCoordinates m) (f : V → ℝ),
      (∑ y, action (T i.val) f y ^ 2) ≤ nu i ^ 2 * ∑ x, f x ^ 2)
    (hcolumn : ∀ (j : OtherCoordinates m) (v : V),
      (∑ y, T j.val y v ^ 2) ≤ delta j)
    (f : (Fin 4 → V) → ℝ)
    (hgraph : ∀ (w : MaskCoordinates m → V) (v v' : OtherCoordinates m → V),
      f ((splitMask m).symm (v, w)) ≠ 0 →
      f ((splitMask m).symm (v', w)) ≠ 0 → v = v') :
    (∑ y, action (coordinateKernel T) f y ^ 2) ≤
      (∏ i : MaskCoordinates m, nu i) ^ 2 *
        (∏ j : OtherCoordinates m, delta j) * ∑ x, f x ^ 2 := by
  let e := splitMask (V := V) m
  let B := coordinateKernel (fun j : OtherCoordinates m => T j.val)
  let A := coordinateKernel (fun i : MaskCoordinates m => T i.val)
  let a : ℝ := ∏ i : MaskCoordinates m, nu i
  let D : ℝ := ∏ j : OtherCoordinates m, delta j
  let c : ℝ := Real.sqrt D
  have hD : 0 ≤ D := Finset.prod_nonneg (fun j _ => hdelta j)
  have hc : c ^ 2 = D := Real.sq_sqrt hD
  have hA : ∀ g : (MaskCoordinates m → V) → ℝ,
      (∑ y, action A g y ^ 2) ≤ a ^ 2 * ∑ x, g x ^ 2 :=
    FiniteTensorEnergy.coordinate_energy
      (fun i : MaskCoordinates m => T i.val) nu hT
  have hB : ∀ v : OtherCoordinates m → V,
      (∑ y, B y v ^ 2) ≤ c ^ 2 := by
    intro v
    rw [hc]
    change (∑ y : OtherCoordinates m → V,
      (∏ j : OtherCoordinates m, T j.val (y j) (v j)) ^ 2) ≤
        ∏ j : OtherCoordinates m, delta j
    rw [product_column_energy (fun j y => T j.val y (v j))]
    exact Finset.prod_le_prod
      (fun j _ => Finset.sum_nonneg (fun y _ => sq_nonneg (T j.val y (v j))))
      (fun j _ => hcolumn j (v j))
  have hfiber : ∀ (w : MaskCoordinates m → V) (v v' : OtherCoordinates m → V),
      (f ∘ e.symm) (v, w) ≠ 0 → (f ∘ e.symm) (v', w) ≠ 0 → v = v' := hgraph
  have he := GraphColumnEnergy.tensor_partial_graph_energy B A a c hA hB
    (f ∘ e.symm) hfiber
  have hn : (∑ x, (f ∘ e.symm) x ^ 2) = ∑ x, f x ^ 2 :=
    e.symm.sum_comp (fun x => f x ^ 2)
  rw [hn, hc] at he
  rw [coordinateKernel_splitMask T m]
  simp_rw [reindexKernel_action]
  rw [e.sum_comp (fun y => action (tensorKernel B A) (f ∘ e.symm) y ^ 2)]
  exact he

end AESConcrete.HeterogeneousGraphEnergy
