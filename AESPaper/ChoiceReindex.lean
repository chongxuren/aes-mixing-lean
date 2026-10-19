import AESPaper.ScalarActivityArrays
import AESPaper.RectangularArrays
import AESConcrete.MarkedBlockShortening

/-!
# Count-preserving reindexing of finite Boolean activity choices

An explicit equivalence of positions induces an explicit equivalence of
Boolean tuples and of their true-coordinate subtypes. Scalar-array energy
transport then uses the accepted counting-measure reindex theorem for every
signed input. Empty position types are included.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ChoiceReindex
open AESMixing AESPaper.RectangularFourier AESPaper.ScalarActivityArrays
open AESConcrete.MarkedBlockShortening (uniformCount)

section Positions
variable {A B : Type*} [Fintype A] [Fintype B]

def tupleEquiv (e : A ≃ B) : (A → Bool) ≃ (B → Bool) where
  toFun s := fun b => s (e.symm b)
  invFun t := fun a => t (e a)
  left_inv s := by funext a; exact congrArg s (e.symm_apply_apply a)
  right_inv t := by funext b; exact congrArg t (e.apply_symm_apply b)

theorem tupleEquiv_apply (e : A ≃ B) (s : A → Bool) (b : B) :
    tupleEquiv e s b = s (e.symm b) := rfl

/-- The true coordinates themselves, not only the ambient cardinalities,
are put in bijection by the actual position equivalence. -/
def trueSubtypeEquiv (e : A ≃ B) (s : A → Bool) :
    {a : A // s a = true} ≃ {b : B // tupleEquiv e s b = true} where
  toFun a := ⟨e a.val, by
    change s (e.symm (e a.val)) = true
    rw [e.symm_apply_apply]
    exact a.property⟩
  invFun b := ⟨e.symm b.val, by
    have h := b.property
    change s (e.symm b.val) = true at h
    exact h⟩
  left_inv a := by apply Subtype.ext; exact e.symm_apply_apply a.val
  right_inv b := by apply Subtype.ext; exact e.apply_symm_apply b.val

theorem uniformCount_tupleEquiv (e : A ≃ B) (s : A → Bool) :
    uniformCount (tupleEquiv e s) = uniformCount s := by
  change Fintype.card {b : B // tupleEquiv e s b = true} =
    Fintype.card {a : A // s a = true}
  exact (Fintype.card_congr (trueSubtypeEquiv e s)).symm

theorem uniformCount_eq_sum (s : A → Bool) :
    uniformCount s = ∑ a : A, if s a then 1 else 0 := by
  simp [uniformCount, Fintype.card_subtype]

theorem weight_tupleEquiv {n : ℕ} (e : A ≃ Fin n) (s : A → Bool) :
    weight (tupleEquiv e s) = uniformCount s := by
  rw [weight_eq_card]
  exact uniformCount_tupleEquiv e s

end Positions

section ScalarTransport
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Physical Boolean-choice matrix whose entries depend on the actual
number of uniform choices on both sides. -/
def countArray (entry : ℕ → ℝ) : (A → Bool) → (B → Bool) → ℝ :=
  fun s t => entry (uniformCount s + uniformCount t)

theorem weightArray_tupleEquiv (a b : ℕ) (eA : A ≃ Fin a) (eB : B ≃ Fin b)
    (entry : ℕ → ℝ) (s : A → Bool) (t : B → Bool) :
    weightArray a b entry (tupleEquiv eA s) (tupleEquiv eB t) = countArray entry s t := by
  change entry (weight (tupleEquiv eA s) + weight (tupleEquiv eB t)) =
    entry (uniformCount s + uniformCount t)
  rw [weight_tupleEquiv, weight_tupleEquiv]

theorem energyBound_countArray (a b : ℕ) (eA : A ≃ Fin a) (eB : B ≃ Fin b)
    (entry : ℕ → ℝ) (n : ℝ) (hScalar : EnergyBound (weightArray a b entry) n) :
    EnergyBound (countArray (A := A) (B := B) entry) n := by
  have h := RectangularArrays.energyBound_reindex (weightArray a b entry) n
    (tupleEquiv eA) (tupleEquiv eB) hScalar
  have he : (fun s t => weightArray a b entry (tupleEquiv eA s) (tupleEquiv eB t)) =
      countArray (A := A) (B := B) entry := by
    funext s t
    exact weightArray_tupleEquiv a b eA eB entry s t
  rw [he] at h
  exact h

/-- Cardinal equalities choose explicit position equivalences; the count and
energy transport still proceed through those equivalences. -/
theorem energyBound_countArray_of_card (a b : ℕ)
    (hA : Fintype.card A = a) (hB : Fintype.card B = b)
    (entry : ℕ → ℝ) (n : ℝ) (hScalar : EnergyBound (weightArray a b entry) n) :
    EnergyBound (countArray (A := A) (B := B) entry) n := by
  let eA : A ≃ Fin a := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hA)
  let eB : B ≃ Fin b := Fintype.equivOfCardEq (by simpa only [Fintype.card_fin] using hB)
  exact energyBound_countArray a b eA eB entry n hScalar

end ScalarTransport
end AESPaper.ChoiceReindex
