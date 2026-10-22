import AES8.Math.PaperActivityInputGram

/-! Exact Boolean support geometry for the activity-input estimate.
Only at most six Boolean labels are enumerated; no AES values are enumerated.
The scalar matrix acts on arbitrary signed coefficients. Actual graph response
identification and its moments are separate obligations. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperActivityInputCounts
open AESMixing PaperActivityInputGram
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

abbrev Mask (n : ℕ) := Fin n → Bool
def weight {n : ℕ} (a : Mask n) : ℕ :=
  (Finset.univ.filter (fun i => a i = true)).card

def allowedTwo (a : Mask 2) (b : Mask 4) : Prop := weight a + weight b = 3
def allowedThree (a : Mask 1) (b : Mask 4) : Prop :=
  weight a + weight b = 2 ∨ weight a + weight b = 3

instance (a : Mask 2) (b : Mask 4) : Decidable (allowedTwo a b) := inferInstanceAs
  (Decidable (weight a + weight b = 3))
instance (a : Mask 1) (b : Mask 4) : Decidable (allowedThree a b) := inferInstanceAs
  (Decidable (weight a + weight b = 2 ∨ weight a + weight b = 3))

def rowCount {m : ℕ} (P : Mask m → Mask 4 → Prop) [∀ a b, Decidable (P a b)]
    (a : Mask m) : ℕ := ∑ b, if P a b then 1 else 0
def overlap {m : ℕ} (P : Mask m → Mask 4 → Prop) [∀ a b, Decidable (P a b)]
    (a a' : Mask m) : ℕ := ∑ b, if P a b ∧ P a' b then 1 else 0

theorem two_row_counts : ∀ a : Mask 2,
    rowCount allowedTwo a = if weight a = 1 then 6 else 4 := by decide
theorem two_overlap : ∀ a a' : Mask 2,
    overlap allowedTwo a a' = if weight a = weight a' then rowCount allowedTwo a else 0 := by decide
theorem two_rowGram : ∀ a : Mask 2, (∑ a', overlap allowedTwo a a') ≤ 12 := by decide

theorem three_row_counts : ∀ a : Mask 1, rowCount allowedThree a = 10 := by decide
theorem three_overlap : ∀ a a' : Mask 1,
    overlap allowedThree a a' = if a = a' then 10 else 6 := by decide
theorem three_rowGram : ∀ a : Mask 1, (∑ a', overlap allowedThree a a') = 16 := by decide

theorem line_choices : (∑ b : Mask 4, if weight b = 1 ∨ weight b = 3 then 1 else 0 : ℕ) = 8 := by decide
theorem plane_choices : (∑ b : Mask 4, if weight b = 2 then 1 else 0 : ℕ) = 6 := by decide

def scalarMatrix {m : ℕ} (P : Mask m → Mask 4 → Prop)
    [∀ a b, Decidable (P a b)] (a : Mask m) (b : Mask 4) : ℝ := if P a b then 1 else 0

theorem scalar_rowGram {m : ℕ} (P : Mask m → Mask 4 → Prop)
    [∀ a b, Decidable (P a b)] (a a' : Mask m) :
    (∑ b, scalarMatrix P a b * scalarMatrix P a' b) = (overlap P a a' : ℝ) := by
  unfold scalarMatrix overlap
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : P a b <;> by_cases h' : P a' b <;> simp [h,h']

theorem scalar_energy {m r : ℕ} (P : Mask m → Mask 4 → Prop)
    [∀ a b, Decidable (P a b)]
    (hrow : ∀ a, (∑ a', overlap P a a') ≤ r) (c : Mask 4 → ℝ) :
    (∑ a, action (scalarMatrix P) c a ^ 2) ≤ (r : ℝ) * ∑ b, c b ^ 2 := by
  apply energy_of_rowGram _ _ (Nat.cast_nonneg r)
  · intro a a'
    rw [scalar_rowGram]
    positivity
  · intro a
    simp_rw [scalar_rowGram]
    exact_mod_cast hrow a

theorem two_energy (c : Mask 4 → ℝ) :
    (∑ a, action (scalarMatrix allowedTwo) c a ^ 2) ≤ 12 * ∑ b, c b ^ 2 :=
  scalar_energy allowedTwo two_rowGram c

theorem three_energy (c : Mask 4 → ℝ) :
    (∑ a, action (scalarMatrix allowedThree) c a ^ 2) ≤ 16 * ∑ b, c b ^ 2 :=
  scalar_energy allowedThree (fun a => (three_rowGram a).le) c

end AES8.PaperActivityInputCounts
