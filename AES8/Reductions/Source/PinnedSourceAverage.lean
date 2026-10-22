/- Module role: Common-source conditioning, restricted response and signed mass reductions.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Reductions.Source.ElevenConditionalResponse

/-!
# Average the squared zero-pin coefficient using a second original source

The finite-product lemma conditions on every coordinate except one actual
initial source. If the zero pin is a permutation of that source word, its
point cap multiplies the complete collision sum of the chosen source.
The AES specialization proves that permutation from the literal affine sum;
it does not posit independence of any later boundary observations.

Constructive proof work only; no attacks or manuscript/predecessor edits.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators

namespace AES8.PinnedSourceAverage
open AESMixing AESMixing.AES
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.BoundarySourceCoordinates (outputEquiv)
open AES8.ConditionalSourceResponse
open AES8.ElevenConditionalResponse (zeroPin)

section ProductLaw
variable {I V : Type*} [Fintype I] [DecidableEq I] [Fintype V]

abbrev Remaining (t : I) := {i : I // i ≠ t}

def joinAt (t : I) (x : V) (w : Remaining t → V) : I → V :=
  fun i => if hi : i = t then x else w ⟨i, hi⟩

@[simp] theorem joinAt_same (t : I) (x : V) (w : Remaining t → V) :
    joinAt t x w t = x := by simp [joinAt]

@[simp] theorem joinAt_other (t : I) (x : V) (w : Remaining t → V) (i : Remaining t) :
    joinAt t x w i.val = w i := by simp [joinAt, i.property]

def splitAt (t : I) : (I → V) ≃ V × (Remaining t → V) where
  toFun v := (v t, fun i => v i.val)
  invFun p := joinAt t p.1 p.2
  left_inv v := by
    funext i
    by_cases hi : i = t
    · subst i
      exact joinAt_same t (v t) (fun i => v i.val)
    · simp [joinAt, hi]
  right_inv p := by
    rcases p with ⟨x, w⟩
    apply Prod.ext
    · exact joinAt_same t x w
    · funext i
      exact joinAt_other t x w i

theorem product_joinAt (eta : I → V → ℝ) (t : I) (x : V) (w : Remaining t → V) :
    (∏ i, eta i (joinAt t x w i)) = eta t x * ∏ i : Remaining t, eta i.val (w i) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ t]
  simp only [joinAt_same, joinAt_other]

/-- A product expectation uses a point cap at t and only the counting-measure
collision of mu. No joint-law premise about transformed coordinates occurs. -/
theorem weighted_pin_average_le
    (eta : I → V → ℝ) (heta : ∀ i x, 0 ≤ eta i x)
    (htotal : ∀ i, (∑ x, eta i x) = 1) (t : I) (p : ℝ)
    (hcap : ∀ x, eta t x ≤ p) (mu : V → ℝ) (pin : (I → V) → V)
    (hpin : ∀ w : Remaining t → V, Function.Bijective (fun x => pin (joinAt t x w))) :
    (∑ v : I → V, (∏ i, eta i (v i)) * mu (pin v) ^ 2) ≤
      p * ∑ x, mu x ^ 2 := by
  let restWeight (w : Remaining t → V) : ℝ := ∏ i : Remaining t, eta i.val (w i)
  have hrest (w : Remaining t → V) : 0 ≤ restWeight w :=
    Finset.prod_nonneg (fun i _ => heta i.val (w i))
  have hrest_total : (∑ w : Remaining t → V, restWeight w) = 1 := by
    unfold restWeight
    rw [← Fintype.prod_sum]
    simp only [htotal, Finset.prod_const_one]
  have hinner (w : Remaining t → V) :
      (∑ x, eta t x * mu (pin (joinAt t x w)) ^ 2) ≤ p * ∑ x, mu x ^ 2 := by
    calc
      _ ≤ ∑ x, p * mu (pin (joinAt t x w)) ^ 2 :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hcap x) (sq_nonneg _))
      _ = p * ∑ x, mu (pin (joinAt t x w)) ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = p * ∑ x, mu x ^ 2 := by
        apply congrArg (fun z : ℝ => p * z)
        exact Equiv.sum_comp (Equiv.ofBijective (fun x => pin (joinAt t x w)) (hpin w))
          (fun x => mu x ^ 2)
  let F : (I → V) → ℝ := fun v => (∏ i, eta i (v i)) * mu (pin v) ^ 2
  calc
    _ = ∑ v : I → V, F v := rfl
    _ = ∑ a : V × (Remaining t → V), F (joinAt t a.1 a.2) :=
      ((splitAt t).symm.sum_comp F).symm
    _ = ∑ w : Remaining t → V, restWeight w *
        ∑ x, eta t x * mu (pin (joinAt t x w)) ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      change (∏ i, eta i (joinAt t x w i)) * mu (pin (joinAt t x w)) ^ 2 = _
      rw [product_joinAt]
      dsimp [restWeight]
      ring
    _ ≤ ∑ w : Remaining t → V, restWeight w * (p * ∑ x, mu x ^ 2) :=
      Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hinner w) (hrest w))
    _ = p * ∑ x, mu x ^ 2 := by rw [← Finset.sum_mul, hrest_total, _root_.one_mul]

end ProductLaw

section ActualPin

private def negEquiv : Equiv.Perm AES.Word where
  toFun x := -x
  invFun x := -x
  left_inv x := neg_neg x
  right_inv x := neg_neg x

theorem zeroPin_eq_inverse_translation (k : Fin 4) (w : OtherAssignments k) (j : Fin 4) :
    zeroPin k w j = (outputEquiv k j).symm (-translation k w j) := by
  apply (outputEquiv k j).injective
  rw [Equiv.apply_symm_apply]
  have h := ElevenConditionalResponse.affine_zeroPin k w j
  change outputEquiv k j (zeroPin k w j) + translation k w j = 0 at h
  exact add_right_cancel (h.trans (neg_add_cancel (translation k w j)).symm)

def remainingTranslation (k : Fin 4) (t : OtherCoordinates k)
    (w : Remaining t → AES.Word) (j : Fin 4) : AES.Word :=
  ∑ i : Remaining t, outputEquiv i.val.val j (w i)

theorem translation_joinAt (k : Fin 4) (t : OtherCoordinates k)
    (x : AES.Word) (w : Remaining t → AES.Word) (j : Fin 4) :
    translation k (joinAt t x w) j = outputEquiv t.val j x + remainingTranslation k t w j := by
  unfold translation
  rw [Fintype.sum_eq_add_sum_subtype_ne _ t]
  simp only [joinAt_same, joinAt_other, remainingTranslation]

/-- Vary exactly one second original source; all remaining sources stay
jointly fixed. The resulting zero pin is a genuine permutation of its word. -/
def pinEquiv (k : Fin 4) (t : OtherCoordinates k)
    (w : Remaining t → AES.Word) (j : Fin 4) : Equiv.Perm AES.Word :=
  (((outputEquiv t.val j).trans (Equiv.addRight (remainingTranslation k t w j))).trans
    negEquiv).trans (outputEquiv k j).symm

@[simp] theorem pinEquiv_apply (k : Fin 4) (t : OtherCoordinates k)
    (w : Remaining t → AES.Word) (j : Fin 4) (x : AES.Word) :
    pinEquiv k t w j x = zeroPin k (joinAt t x w) j := by
  rw [zeroPin_eq_inverse_translation, translation_joinAt]
  rfl

theorem zeroPin_joinAt_bijective (k : Fin 4) (t : OtherCoordinates k)
    (w : Remaining t → AES.Word) (j : Fin 4) :
    Function.Bijective (fun x => zeroPin k (joinAt t x w) j) := by
  have he : (fun x => pinEquiv k t w j x) =
      (fun x => zeroPin k (joinAt t x w) j) := funext (pinEquiv_apply k t w j)
  rw [← he]
  exact (pinEquiv k t w j).bijective

/-- The source at t supplies its point cap; source k supplies its complete
pre-centering collision. Inactive sources still have exact total mass one. -/
theorem actual_pin_average_le (b : AES.State) (k : Fin 4) (hk : sourceInput b k ≠ 0)
    (t : OtherCoordinates k) (ht : sourceInput b t.val ≠ 0) (j : Fin 4) :
    (∑ w : OtherAssignments k, conditionWeight b k w *
      wordLaw (sourceInput b k) (zeroPin k w j) ^ 2) ≤ 23 / q ^ 2 := by
  have h := weighted_pin_average_le
    (fun i : OtherCoordinates k => wordLaw (sourceInput b i.val))
    (fun i x => AESPaper.StartingWord.wordLaw_nonnegative (sourceInput b i.val) x)
    (fun i => AESPaper.StartingWord.wordLaw_total (sourceInput b i.val))
    t (20 / q) (fun x => (AESPaper.StartingWord.wordLaw_point_lt (sourceInput b t.val) x ht).le)
    (wordLaw (sourceInput b k)) (fun w => zeroPin k w j)
    (fun w => zeroPin_joinAt_bijective k t w j)
  change (∑ w : OtherAssignments k, conditionWeight b k w *
      wordLaw (sourceInput b k) (zeroPin k w j) ^ 2) ≤
    (20 / q) * ∑ x, wordLaw (sourceInput b k) x ^ 2 at h
  calc
    _ ≤ (20 / q) * ∑ x, wordLaw (sourceInput b k) x ^ 2 := h
    _ ≤ (20 / q) * (17 / (15 * q)) :=
      mul_le_mul_of_nonneg_left (AESPaper.StartingWord.wordLaw_collision_lt _ hk).le
        (by norm_num [q])
    _ ≤ 23 / q ^ 2 := by norm_num [q]

end ActualPin
end AES8.PinnedSourceAverage
