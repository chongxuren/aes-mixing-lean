import AESMixing.DegreeComposition
import AESMixing.LawRelabel

/-!
# Exact byte-degree transport under zero-fixing coordinate permutations

The alphabet is generic. Specializing `V` to the AES byte and `z` to zero
covers byte-monomial maps: `p` permutes positions, and each `e i` can be
multiplication by a nonzero field scalar. The proof allows every byte
permutation fixing zero; it asserts no invariance of the AES channel itself.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace AESPaper.ByteCoordinateTransport
open AESMixing

variable {I V : Type*}

/-- Position reindexing, with its inverse kept explicit. -/
def reindexEquiv (p : Equiv.Perm I) : Equiv.Perm (I → V) where
  toFun x i := x (p i)
  invFun x i := x (p.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

/-- Actual coordinate map: first reindex positions, then relabel each value. -/
def coordinateEquiv (p : Equiv.Perm I) (e : I → Equiv.Perm V) :
    Equiv.Perm (I → V) :=
  (reindexEquiv p).trans (Equiv.piCongrRight e)

theorem coordinateEquiv_apply (p : Equiv.Perm I) (e : I → Equiv.Perm V)
    (x : I → V) (i : I) : coordinateEquiv p e x i = e i (x (p i)) := rfl

theorem coordinateEquiv_symm_apply (p : Equiv.Perm I) (e : I → Equiv.Perm V)
    (x : I → V) (i : I) :
    (coordinateEquiv p e).symm x i = (e (p.symm i)).symm (x (p.symm i)) := rfl

theorem coordinateEquiv_const (p : Equiv.Perm I) (e : I → Equiv.Perm V)
    (z : V) (he : ∀ i, e i z = z) :
    coordinateEquiv p e (fun _ => z) = fun _ => z := by
  funext i
  exact he i

section Projections
variable [Fintype V] [DecidableEq V]

theorem fixed_value_iff (e : Equiv.Perm V) (z : V) (he : e z = z) (x : V) :
    e x = z ↔ x = z := by
  constructor
  · intro h
    exact e.injective (h.trans he.symm)
  · rintro rfl
    exact he

/-- Both the activity and residual projection kernels are invariant under
the same distinguished-value-preserving permutation of their two labels. -/
theorem degreePiece_equiv (e : Equiv.Perm V) (z : V) (he : e z = z)
    (b : Bool) (x y : V) :
    degreePiece z b (e x) (e y) = degreePiece z b x y := by
  have hx := fixed_value_iff e z he x
  have hy := fixed_value_iff e z he y
  have hxy : e x = e y ↔ x = y := e.injective.eq_iff
  cases b <;>
    simp only [degreePiece, Bool.false_eq_true, if_false, if_true,
      residualProjection, Pi.sub_apply, identityKernel, activityMatrix, hx, hy, hxy]

variable [Fintype I] [DecidableEq I]

theorem productProjection_equiv (p : Equiv.Perm I) (e : I → Equiv.Perm V)
    (z : V) (he : ∀ i, e i z = z) (a : I → Bool) (x y : I → V) :
    productProjection z (reindexEquiv p a)
        (coordinateEquiv p e x) (coordinateEquiv p e y) =
      productProjection z a x y := by
  unfold productProjection
  simp only [reindexEquiv, coordinateEquiv_apply, degreePiece_equiv _ z (he _)]
  exact Equiv.prod_comp p (fun i => degreePiece z (a i) (x i) (y i))

end Projections

section FourCoordinates
variable [Fintype V] [DecidableEq V]

/-- Reindexing four residual flags preserves their number. -/
theorem degreeIndex_reindex (p : Equiv.Perm (Fin 4)) (a : Fin 4 → Bool) :
    degreeIndex (reindexEquiv p a) = degreeIndex a := by
  apply Fin.ext
  change (Finset.univ.filter (fun i => a (p i) = true)).card =
    (Finset.univ.filter (fun i => a i = true)).card
  simpa using Equiv.sum_comp p (fun i => if a i = true then (1 : ℕ) else 0)

theorem degreeKernel_equiv (p : Equiv.Perm (Fin 4))
    (e : Fin 4 → Equiv.Perm V) (z : V) (he : ∀ i, e i z = z)
    (j : Fin 5) (x y : Fin 4 → V) :
    degreeKernel z j (coordinateEquiv p e x) (coordinateEquiv p e y) =
      degreeKernel z j x y := by
  have h := Equiv.sum_comp (reindexEquiv p : Equiv.Perm (Fin 4 → Bool))
    (fun a => if degreeIndex a = j then
      productProjection z a (coordinateEquiv p e x) (coordinateEquiv p e y) else 0)
  simpa only [degreeIndex_reindex,
    productProjection_equiv p e z he, degreeKernel] using h.symm

/-- Applying the transported degree component at the transported argument
recovers the original component. The input function may be arbitrary and joint. -/
theorem degreeComponent_transport_apply (p : Equiv.Perm (Fin 4))
    (e : Fin 4 → Equiv.Perm V) (z : V) (he : ∀ i, e i z = z)
    (j : Fin 5) (f : (Fin 4 → V) → ℝ) (y : Fin 4 → V) :
    degreeComponent z j (lawRelabel (coordinateEquiv p e) f)
        (coordinateEquiv p e y) = degreeComponent z j f y := by
  simp only [← degreeKernel_action, action, lawRelabel]
  have h := Equiv.sum_comp (coordinateEquiv p e)
    (fun x => degreeKernel z j (coordinateEquiv p e y) x *
      f ((coordinateEquiv p e).symm x))
  simpa only [(coordinateEquiv p e).symm_apply_apply,
    degreeKernel_equiv p e z he] using h.symm

theorem degreeComponent_transport (p : Equiv.Perm (Fin 4))
    (e : Fin 4 → Equiv.Perm V) (z : V) (he : ∀ i, e i z = z)
    (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    degreeComponent z j (lawRelabel (coordinateEquiv p e) f) =
      lawRelabel (coordinateEquiv p e) (degreeComponent z j f) := by
  funext y
  have h := degreeComponent_transport_apply p e z he j f ((coordinateEquiv p e).symm y)
  simpa only [(coordinateEquiv p e).apply_symm_apply, lawRelabel] using h

/-- Exact counting-measure source-degree energy preservation. -/
theorem degree_energy_transport (p : Equiv.Perm (Fin 4))
    (e : Fin 4 → Equiv.Perm V) (z : V) (he : ∀ i, e i z = z)
    (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ y, degreeComponent z j (lawRelabel (coordinateEquiv p e) f) y ^ 2) =
      ∑ y, degreeComponent z j f y ^ 2 := by
  rw [degreeComponent_transport p e z he]
  exact Equiv.sum_comp (coordinateEquiv p e).symm
    (fun y => degreeComponent z j f y ^ 2)

/-- The uniform non-distinguished reference is fixed by the same map. -/
theorem uniformExcept_transport (p : Equiv.Perm (Fin 4))
    (e : Fin 4 → Equiv.Perm V) (z : V) (he : ∀ i, e i z = z) :
    lawRelabel (coordinateEquiv p e) (uniformExcept (fun _ : Fin 4 => z)) =
      uniformExcept (fun _ : Fin 4 => z) :=
  lawRelabel_uniformExcept (coordinateEquiv p e) (fun _ => z)
    (coordinateEquiv_const p e z he)

end FourCoordinates
end AESPaper.ByteCoordinateTransport
