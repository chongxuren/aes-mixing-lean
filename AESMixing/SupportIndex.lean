import AESMixing.SupportOrthogonality
import AESMixing.IncidenceCounting

/-! Enumerate genuine support components of a given residual degree.
Only the four coordinate labels are enumerated; no alphabet vectors are
enumerated or assumed to factor. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskBit maskSize)

abbrev SupportIndex (j : ℕ) :=
  {p : Fin 16 × Fin 16 // MaskDisjoint p.2 p.1 ∧ maskSize p.1 = j}

def supportIndexSize {j : ℕ} (p : SupportIndex j) : Fin (5-j) :=
  ⟨4-maskSize p.val.2-j,by
    have h := disjoint_mask_size_le_four p.val.2 p.val.1 p.property.1
    have hj := p.property.2
    omega⟩

theorem supportIndexSize_eq {j : ℕ} (p : SupportIndex j) :
    (supportIndexSize p).val+j = 4-maskSize p.val.2 := by
  have h := disjoint_mask_size_le_four p.val.2 p.val.1 p.property.1
  have hj := p.property.2
  simp only [supportIndexSize]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem supportIndex_fiber_card : ∀ j : Fin 5, ∀ a : Fin (5-j.val),
    Fintype.card {p : SupportIndex j.val // supportIndexSize p = a} =
      Nat.choose 4 j.val * Nat.choose (4-j.val) a.val := by decide

theorem supportIndex_sum_by_size (j : Fin 5) (f : Fin (5-j.val) → ℝ) :
    (∑ p : SupportIndex j.val, f (supportIndexSize p)) =
      ∑ a, (Nat.choose 4 j.val * Nat.choose (4-j.val) a.val : ℕ)*f a := by
  rw [← Fintype.sum_fiberwise' supportIndexSize f]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,supportIndex_fiber_card]

variable {V : Type*} [Fintype V] [DecidableEq V]

def supportIndexComponent (z : V) {j : ℕ} (p : SupportIndex j)
    (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  action (supportProduct z (maskBit p.val.1) (maskBit p.val.2)) f

theorem supportIndex_orthogonal (z : V) (hn : 1 < Fintype.card V) {j : ℕ}
    (p q : SupportIndex j) (hpq : p ≠ q) (f g : (Fin 4 → V) → ℝ) :
    (∑ x, supportIndexComponent z p f x * supportIndexComponent z q g x) = 0 := by
  apply supportProduct_mixed_orthogonal z hn
  intro h
  apply hpq
  apply Subtype.ext
  exact Prod.ext (maskBits_injective h.1) (maskBits_injective h.2)

theorem supportIndex_energy (z : V) (hn : 1 < Fintype.card V) (j : ℕ)
    (f : (Fin 4 → V) → ℝ) :
    (∑ x, (∑ p : SupportIndex j, supportIndexComponent z p f x)^2) =
      ∑ p : SupportIndex j, ∑ x, supportIndexComponent z p f x^2 :=
  orthogonal_family_energy _ (fun p q hpq => supportIndex_orthogonal z hn p q hpq f f)

end AESMixing
