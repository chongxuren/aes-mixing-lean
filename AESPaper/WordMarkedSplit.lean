import AESPaper.WordMarkedCode

/-!
# Physical output/input split of actual marked word coordinates

The split records which physical coordinates are outputs and which are
inputs. It supplies actual equivalences and exact reindexing identities;
it assumes no invariance of a matrix norm under a bare relabeling.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordMarkedSplit
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked)
attribute [local instance] Classical.propDecidable

abbrev OutputMarked (m : GraphPosition → Bool) := {i : Fin 4 // m (Sum.inl i) = true}
abbrev InputMarked (m : GraphPosition → Bool) := {i : Fin 4 // m (Sum.inr i) = true}

def outputPosition (m : GraphPosition → Bool) (i : OutputMarked m) : Marked m :=
  ⟨Sum.inl i.val, i.property⟩

def inputPosition (m : GraphPosition → Bool) (i : InputMarked m) : Marked m :=
  ⟨Sum.inr i.val, i.property⟩

/-- The physical sum split, with output and input roles retained. -/
def positionEquiv (m : GraphPosition → Bool) :
    OutputMarked m ⊕ InputMarked m ≃ Marked m where
  toFun := Sum.elim (outputPosition m) (inputPosition m)
  invFun p := match p with
    | ⟨Sum.inl i, h⟩ => Sum.inl ⟨i,h⟩
    | ⟨Sum.inr i, h⟩ => Sum.inr ⟨i,h⟩
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨p,h⟩; cases p <;> rfl

@[simp] theorem positionEquiv_inl (m : GraphPosition → Bool) (i : OutputMarked m) :
    positionEquiv m (Sum.inl i) = outputPosition m i := rfl

@[simp] theorem positionEquiv_inr (m : GraphPosition → Bool) (i : InputMarked m) :
    positionEquiv m (Sum.inr i) = inputPosition m i := rfl

theorem marked_card (m : GraphPosition → Bool) :
    Fintype.card (Marked m) = Fintype.card (OutputMarked m) + Fintype.card (InputMarked m) := by
  rw [← Fintype.card_congr (positionEquiv m), Fintype.card_sum]

theorem sum_positions (m : GraphPosition → Bool) (f : Marked m → ℝ) :
    (∑ p : Marked m, f p) =
      (∑ i : OutputMarked m, f (outputPosition m i)) +
        ∑ i : InputMarked m, f (inputPosition m i) := by
  simpa only [Fintype.sum_sum_type, positionEquiv_inl, positionEquiv_inr] using
    ((positionEquiv m).sum_comp f).symm

theorem prod_positions (m : GraphPosition → Bool) (f : Marked m → ℝ) :
    (∏ p : Marked m, f p) =
      (∏ i : OutputMarked m, f (outputPosition m i)) *
        ∏ i : InputMarked m, f (inputPosition m i) := by
  simpa only [Fintype.prod_sum_type, positionEquiv_inl, positionEquiv_inr] using
    ((positionEquiv m).prod_comp f).symm

section Tuples
variable {V : Type*}

/-- Tuples split into their actual physical output and input restrictions. -/
def tupleEquiv (m : GraphPosition → Bool) :
    (Marked m → V) ≃ (OutputMarked m → V) × (InputMarked m → V) where
  toFun v := (fun i => v (outputPosition m i), fun i => v (inputPosition m i))
  invFun v := fun p => Sum.elim v.1 v.2 ((positionEquiv m).symm p)
  left_inv v := by
    funext p
    rcases p with ⟨p,h⟩
    cases p <;> rfl
  right_inv v := by
    apply Prod.ext <;> funext p <;> rfl

def join (m : GraphPosition → Bool) (y : OutputMarked m → V) (x : InputMarked m → V) :
    Marked m → V := (tupleEquiv m).symm (y,x)

@[simp] theorem join_output (m : GraphPosition → Bool)
    (y : OutputMarked m → V) (x : InputMarked m → V) (i : OutputMarked m) :
    join m y x (outputPosition m i) = y i := rfl

@[simp] theorem join_input (m : GraphPosition → Bool)
    (y : OutputMarked m → V) (x : InputMarked m → V) (i : InputMarked m) :
    join m y x (inputPosition m i) = x i := rfl

theorem join_restrictions (m : GraphPosition → Bool) (v : Marked m → V) :
    join m (fun i => v (outputPosition m i)) (fun i => v (inputPosition m i)) = v :=
  (tupleEquiv m).symm_apply_apply v

variable [Fintype V]

theorem sum_tuples (m : GraphPosition → Bool) (f : (Marked m → V) → ℝ) :
    (∑ v : Marked m → V, f v) =
      ∑ y : OutputMarked m → V, ∑ x : InputMarked m → V, f (join m y x) := by
  calc
    _ = ∑ yx : (OutputMarked m → V) × (InputMarked m → V),
        f ((tupleEquiv m).symm yx) := ((tupleEquiv m).symm.sum_comp f).symm
    _ = _ := by simp only [Fintype.sum_prod_type, join]

/-- Coordinate kernels factor in the same physical split as the tuples. -/
theorem coordinateKernel_join (m : GraphPosition → Bool)
    (T : Marked m → V → V → ℝ)
    (y v : OutputMarked m → V) (x w : InputMarked m → V) :
    coordinateKernel T (join m y x) (join m v w) =
      coordinateKernel (fun i => T (outputPosition m i)) y v *
        coordinateKernel (fun i => T (inputPosition m i)) x w := by
  unfold coordinateKernel
  rw [prod_positions]
  simp only [join_output, join_input]

end Tuples

section Fourier
variable {V : Type*} [AddCommGroup V] [Fintype V]

/-- Product Fourier has the physical rectangular output/input split, with
the counting normalization fixed by the exact tuple equivalence. -/
theorem pairingFourier_join (m : GraphPosition → Bool) (B : CharacterPairing V)
    (y v : OutputMarked m → V) (x w : InputMarked m → V) :
    pairingFourier (B.product (Marked m)) (join m y x) (join m v w) =
      pairingFourier (B.product (OutputMarked m)) y v *
        pairingFourier (B.product (InputMarked m)) x w := by
  rw [productPairing_fourier, coordinateKernel_join,
    ← productPairing_fourier, ← productPairing_fourier]

/-- Explicit full-vector Fourier action after the actual physical reshape.
No operator norm or desired bound is assumed in this reindexing. -/
theorem fourier_join (m : GraphPosition → Bool) (B : CharacterPairing V)
    (f : (Marked m → V) → ℝ) (y : OutputMarked m → V) (x : InputMarked m → V) :
    action (pairingFourier (B.product (Marked m))) f (join m y x) =
      ∑ v : OutputMarked m → V, ∑ w : InputMarked m → V,
        pairingFourier (B.product (OutputMarked m)) y v *
          pairingFourier (B.product (InputMarked m)) x w * f (join m v w) := by
  unfold action
  rw [sum_tuples]
  simp_rw [pairingFourier_join]

end Fourier
end AESPaper.WordMarkedSplit
