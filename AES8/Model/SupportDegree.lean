/- Module role: Concrete AES support definitions and coordinate/projection interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Model.SupportProfile
import AESMixing.FiveDegree

/-!
# Support refinement of the five residual degrees

Each fourteen-coordinate component groups raw orthogonal support pieces of one
residual degree.  Summing over every support at that degree gives the old
`degreeComponent`; selecting one support size can only decrease its energy.
The statements hold for arbitrary joint inputs, without a zero-extension or
product-law hypothesis.  No concrete initializer or transfer estimate is used.

The original support and degree modules keep their definitions and namespaces.
This bridge deliberately uses their raw projections, avoiding the separate
`SupportIndex` interface and its additional import closure.  Constructive proof
work only; no predecessor or manuscript changes.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace AES8.SupportDegree
open AESMixing AESMixing.AES
open AES8.SupportProfile

theorem residualDegree_lt (c : Fin 14) : SupportProfile.residualDegree c < 5 := by
  fin_cases c <;> decide

/-- The old five-degree index corresponding to a fourteen-coordinate entry. -/
def degree (c : Fin 14) : Fin 5 :=
  ⟨SupportProfile.residualDegree c, residualDegree_lt c⟩

theorem degree_val (c : Fin 14) : (degree c).val = SupportProfile.residualDegree c := rfl

private theorem mask_degree_size : ∀ m : Fin 16,
    (AESMixing.degreeIndex (maskBit m)).val = maskSize m := by decide

private theorem mask_degree_eq (m : Fin 16) (j : Fin 5) :
    AESMixing.degreeIndex (maskBit m) = j ↔ maskSize m = j.val := by
  rw [Fin.ext_iff, mask_degree_size]

/-- Exact energy of one old residual degree, refined by both four-bit masks. -/
theorem degree_energy (f : SupportProfile.State → ℝ) (j : Fin 5) :
    (∑ x, degreeComponent (0 : AES.Word) j f x ^ 2) =
      ∑ p : SupportProfile.Label,
        if maskSize p.1 = j.val then ∑ x, raw p f x ^ 2 else 0 := by
  calc
    (∑ x, degreeComponent (0 : AES.Word) j f x ^ 2) =
        ∑ a : Fin 4 → Bool, if AESMixing.degreeIndex a = j then
          ∑ x, action (productProjection (0 : AES.Word) a) f x ^ 2 else 0 :=
      degreeComponent_energy (0 : AES.Word) SupportProfile.word_card_gt_one j f
    _ = ∑ m : Fin 16, if AESMixing.degreeIndex (maskBit m) = j then
          ∑ x, action (productProjection (0 : AES.Word) (maskBit m)) f x ^ 2 else 0 :=
      (maskBitsEquiv.sum_comp (fun a : Fin 4 → Bool =>
        if AESMixing.degreeIndex a = j then
          ∑ x, action (productProjection (0 : AES.Word) a) f x ^ 2 else 0)).symm
    _ = ∑ p : SupportProfile.Label,
          if maskSize p.1 = j.val then ∑ x, raw p f x ^ 2 else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro m _
      by_cases hm : maskSize m = j.val
      · simp only [mask_degree_eq, hm, if_true]
        calc
          (∑ x, action (productProjection (0 : AES.Word) (maskBit m)) f x ^ 2) =
              ∑ inactive : Fin 4 → Bool,
                ∑ x, action (supportProduct (0 : AES.Word) (maskBit m) inactive) f x ^ 2 :=
            supportProduct_pythagoras (0 : AES.Word) SupportProfile.word_card_gt_one
              (maskBit m) f
          _ = ∑ n : Fin 16, ∑ x, raw (m, n) f x ^ 2 :=
            (maskBitsEquiv.sum_comp (fun inactive : Fin 4 → Bool =>
              ∑ x, action (supportProduct (0 : AES.Word) (maskBit m) inactive) f x ^ 2)).symm
      · simp only [mask_degree_eq, hm, if_false, Finset.sum_const_zero]

/-- Energy of a fourteen-coordinate component in the same raw refinement. -/
theorem component_energy (f : SupportProfile.State → ℝ) (c : Fin 14) :
    (∑ x, component f c x ^ 2) =
      ∑ p : SupportProfile.Label,
        if coord p = c.succ then ∑ x, raw p f x ^ 2 else 0 := by
  exact groupedFamily_energy coord (fun p => raw p f)
    (fun p q hpq => raw_orthogonal p q hpq f f) c.succ

/-- A support-size component is an orthogonal refinement of its old degree. -/
theorem component_energy_le_degree (f : SupportProfile.State → ℝ) (c : Fin 14) :
    (∑ x, component f c x ^ 2) ≤
      ∑ x, degreeComponent (0 : AES.Word) (degree c) f x ^ 2 := by
  rw [component_energy, degree_energy]
  apply Finset.sum_le_sum
  intro p _
  by_cases hp : Valid p
  · by_cases hc : coord p = c.succ
    · have hd : maskSize p.1 = (degree c).val := ((coord_type p c hp).mp hc).1
      simp only [hc, hd, if_true]
      exact le_rfl
    · rw [if_neg hc]
      by_cases hd : maskSize p.1 = (degree c).val
      · rw [if_pos hd]
        exact Finset.sum_nonneg (fun x _ => sq_nonneg (raw p f x))
      · simp only [if_neg hd, le_refl]
  · simp only [raw_invalid p hp f, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, ite_self, le_refl]

/-- Counting-measure norm bound, ready for the old five-entry initializer. -/
theorem profile_le_degree (f : SupportProfile.State → ℝ) (c : Fin 14) :
    SupportProfile.profile f c ≤
      l2 (degreeComponent (0 : AES.Word) (degree c) f) := by
  apply (sq_le_sq₀ (SupportProfile.profile_nonneg f c) (l2_nonneg _)).mp
  simpa only [SupportProfile.profile, l2_sq] using component_energy_le_degree f c

/-- At grouped index `j+1`, the refinement uses exactly the actual error. -/
theorem actual_le_degree (a : AES.State) (j : ℕ) (c : Fin 14) :
    SupportProfile.actual a j c ≤
      l2 (degreeComponent (0 : AES.Word) (degree c)
        (AESPaper.GroupedLaw.error (j + 1) a)) :=
  profile_le_degree _ c

end AES8.SupportDegree
