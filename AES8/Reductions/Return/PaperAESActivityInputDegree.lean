import AES8.Reductions.Return.PaperAESActivityInputAssembly

/-! Orthogonal degree aggregation and exact degree-zero input reconstruction.
The target here is the full-space degree-zero input projection. The paper's
centered NonzeroSpace projection and complex operator interface are separate. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputDegree
open AESMixing WordActivityFrame PaperActivityInputArithmetic PaperActivityInputAssembly
open PaperActivityInputCoordinates PaperAESActivityIdentification PaperAESActivityInputPhysical
open PaperAESActivityInputResponse PaperAESActivityInputAssembly
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000

private theorem degree_truthSet : ∀ a : Fin 4 → Bool,
    (degreeIndex a).val = (truthSet a).card := by decide

private theorem mask_truthSet (a : Fin 4 → Bool) : residualMask (truthSet a) = a := by
  funext k
  exact truthSet_bit a k

private theorem count_two :
    (∑ a : Fin 4 → Bool, if degreeIndex a = (2 : Fin 5) then 1 else 0 : ℕ) = 6 := by decide
private theorem count_three :
    (∑ a : Fin 4 → Bool, if degreeIndex a = (3 : Fin 5) then 1 else 0 : ℕ) = 4 := by decide
private theorem count_four :
    (∑ a : Fin 4 → Bool, if degreeIndex a = (4 : Fin 5) then 1 else 0 : ℕ) = 1 := by decide

theorem aggregate_fixed_energy (i : Fin 5) (r : ℝ) (adjoint : Bool)
    (c : (Fin 4 → Bool) → ℝ)
    (hfixed : ∀ O : Finset (Fin 4), O.card = i.val →
      (∑ x : AES.WordState, action (productProjection 0 (residualMask O))
        (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
          r * ∑ x, synthesize c x^2) :
    (∑ x, degreeComponent (0 : AES.Word) i
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      ((∑ a : Fin 4 → Bool, if degreeIndex a = i then 1 else 0 : ℕ) : ℝ) * r *
        ∑ x, synthesize c x^2 := by
  rw [degreeComponent_energy 0 AESConcrete.AES.word_card_gt_one]
  calc
    _ ≤ ∑ a : Fin 4 → Bool, if degreeIndex a = i
        then r * ∑ x, synthesize c x^2 else 0 := by
      apply Finset.sum_le_sum
      intro a _
      by_cases ha : degreeIndex a = i
      · rw [if_pos ha,if_pos ha]
        have hcard : (truthSet a).card = i.val := by
          rw [← degree_truthSet a,ha]
        have h := hfixed (truthSet a) hcard
        simpa only [mask_truthSet] using h
      · simp only [if_neg ha,le_refl]
    _ = _ := by rw [weighted_choices]; ring

theorem degree_one_energy (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) 1
      (action (actualStep adjoint) (synthesize c)) x ^ 2) = 0 := by
  have h := aggregate_fixed_energy 1 0 adjoint c (fun O hO => by
    rw [degree_one_fixed_energy O hO adjoint c,zero_mul])
  simp only [mul_zero,zero_mul] at h
  exact le_antisymm h (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem degree_two_energy (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) 2
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      (72*loss^2*tau^2/wordQ^3)*∑ x, synthesize c x^2 := by
  have h := aggregate_fixed_energy 2 (loss^2*(12*(tau^2/wordQ^3))) adjoint c
    (fun O hO => degree_two_fixed_energy O hO adjoint c)
  rw [count_two] at h
  apply h.trans_eq
  ring

theorem degree_three_energy (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) 3
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      (64*loss^2*tau^2*beta/wordQ^2)*∑ x, synthesize c x^2 := by
  have h := aggregate_fixed_energy 3 (loss^2*(16*(tau^2*beta/wordQ^2))) adjoint c
    (fun O hO => degree_three_fixed_energy O hO adjoint c)
  rw [count_three] at h
  apply h.trans_eq
  ring

theorem degree_four_energy (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) 4
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      (loss^2*(8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2))*∑ x, synthesize c x^2 := by
  have h := aggregate_fixed_energy 4
    (loss^2*(8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)) adjoint c
    (fun O hO => degree_four_fixed_energy O hO adjoint c)
  simpa only [count_four,Nat.cast_one,one_mul] using h

def inputCoefficients (f : AES.WordState → ℝ) (s : Fin 4 → Bool) : ℝ :=
  ∑ t : Fin 4 → Bool, frameInverse AES.Word s t * analyze f t

theorem degree_zero_synthesis (f : AES.WordState → ℝ) :
    synthesize (inputCoefficients f) = degreeComponent 0 0 f := by
  rw [degree_zero_action 0 AESConcrete.AES.word_card_gt_one]
  funext x
  simp only [synthesize,inputCoefficients,analyze,Finset.mul_sum,mul_assoc]

theorem degree_zero_energy_le (f : AES.WordState → ℝ) :
    (∑ x, degreeComponent (0 : AES.Word) 0 f x^2) ≤ ∑ x, f x^2 := by
  have h : (∑ x, degreeComponent (0 : AES.Word) 0 f x^2) ≤
      ∑ j : Fin 5, ∑ x, degreeComponent (0 : AES.Word) j f x^2 :=
    Finset.single_le_sum
      (f := fun j : Fin 5 => ∑ x : AES.WordState, degreeComponent 0 j f x^2)
      (fun j _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.mem_univ (0 : Fin 5))
  rw [degreeComponent_pythagoras 0 AESConcrete.AES.word_card_gt_one] at h
  exact h

end AES8.PaperAESActivityInputDegree
