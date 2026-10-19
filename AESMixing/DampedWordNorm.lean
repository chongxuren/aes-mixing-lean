import AESMixing.DegreeMatrixNorm
import AESMixing.Numeric
import AESMixing.DegreeAdjoint

/-! Assemble the word norm from the byte resources and the five-degree
diffusion bounds. This generic lemma retains the diffusion estimates as
explicit premises until both concrete oriented activity tables are linked. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def twoSubstitutionKernel (D E : BinaryWord 8 → BinaryWord 8 → ℝ)
    (L : Equiv.Perm (Fin 4 → BinaryWord 8)) :
    (Fin 4 → BinaryWord 8) → (Fin 4 → BinaryWord 8) → ℝ :=
  kernelCompose (substitutionKernel D)
    (fun y x => substitutionKernel E (L.symm y) x)

theorem twoSubstitutionKernel_action (D E : BinaryWord 8 → BinaryWord 8 → ℝ)
    (L : Equiv.Perm (Fin 4 → BinaryWord 8)) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    action (twoSubstitutionKernel D E L) f =
      action (substitutionKernel D) (fun y => action (substitutionKernel E) f (L.symm y)) := by
  rw [twoSubstitutionKernel,kernelCompose_action]
  rfl

theorem byteComparison_nonneg (i j : Fin 5) : 0 ≤ byteComparison i j := by
  fin_cases i <;> fin_cases j <;> norm_num [byteComparison]

theorem substitution_joint_centered {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (hD : ByteResources D) (f : (Fin 4 → BinaryWord 8) → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    action (substitutionKernel D) f 0 = 0 ∧
      (∑ y, action (substitutionKernel D) f y) = 0 := by
  have hp : PointedBistochastic (substitutionKernel D) (0 : Fin 4 → BinaryWord 8) :=
    coordinateKernel_pointed _ _ (fun _ => hD.pointed)
  exact ⟨(hp.action_zero f).trans hz,(hp.action_sum f).trans hs⟩

theorem twoSubstitution_degree_bound {D E : BinaryWord 8 → BinaryWord 8 → ℝ}
    (hD : ByteResources D) (hE : ByteResources E)
    (L : Equiv.Perm (Fin 4 → BinaryWord 8))
    (hDiff : ∀ (i j : Fin 5) (f : (Fin 4 → BinaryWord 8) → ℝ),
      f 0 = 0 → (∑ x, f x) = 0 →
      (∑ x, degreeTransfer 0 i j L f x^2) ≤
        (byteComparison i j)^2*∑ x, degreeComponent 0 j f x^2)
    (i j : Fin 5) (f : (Fin 4 → BinaryWord 8) → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    l2 (degreeComponent 0 i (action (twoSubstitutionKernel D E L) (degreeComponent 0 j f))) ≤
      dampedComparison i j*l2 (degreeComponent 0 j f) := by
  let g := action (substitutionKernel E) f
  have hg := substitution_joint_centered hE f hz hs
  have hleft := l2_le_of_energy _ _ ((9/128 : ℝ)^i.val) (by positivity)
    (substitution_degree_energy hD i
      (fun y => degreeComponent 0 j g (L.symm y)))
  have hmiddle := l2_le_of_energy _ _ (byteComparison i j) (byteComparison_nonneg i j)
    (hDiff i j g hg.1 hg.2)
  have hright := l2_le_of_energy _ _ ((9/128 : ℝ)^j.val) (by positivity)
    (substitution_degree_energy hE j f)
  rw [substitution_degree_commutes hE] at hright
  have hid : degreeComponent 0 i (action (twoSubstitutionKernel D E L) (degreeComponent 0 j f)) =
      action (substitutionKernel D)
        (degreeComponent 0 i (fun y => degreeComponent 0 j g (L.symm y))) := by
    rw [twoSubstitutionKernel_action,substitution_degree_commutes hE,
      substitution_degree_commutes hD]
  rw [hid]
  calc
    _ ≤ (9/128 : ℝ)^i.val*l2 (degreeTransfer 0 i j L g) := hleft
    _ ≤ (9/128 : ℝ)^i.val*(byteComparison i j*l2 (degreeComponent 0 j g)) :=
      mul_le_mul_of_nonneg_left hmiddle (by positivity)
    _ ≤ (9/128 : ℝ)^i.val*(byteComparison i j*((9/128 : ℝ)^j.val*l2 (degreeComponent 0 j f))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hright
        (byteComparison_nonneg i j)) (by positivity)
    _ = _ := by rw [dampedComparison,pow_add]; ring

theorem twoSubstitution_centered_energy {D E : BinaryWord 8 → BinaryWord 8 → ℝ}
    (hD : ByteResources D) (hE : ByteResources E)
    (L : Equiv.Perm (Fin 4 → BinaryWord 8))
    (hDiff : ∀ (i j : Fin 5) (f : (Fin 4 → BinaryWord 8) → ℝ),
      f 0 = 0 → (∑ x, f x) = 0 →
      (∑ x, degreeTransfer 0 i j L f x^2) ≤
        (byteComparison i j)^2*∑ x, degreeComponent 0 j f x^2)
    (f : (Fin 4 → BinaryWord 8) → ℝ) (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action (twoSubstitutionKernel D E L) f x^2) ≤
      (11/65536 : ℝ)^2*∑ x, f x^2 := by
  apply degree_matrix_energy 0 (by norm_num [BinaryWord.card]) _ dampedComparison
    (11/65536) dampedComparison_nonneg local_comparison_energy f
  exact fun i j => twoSubstitution_degree_bound hD hE L hDiff i j f hz hs

end AESMixing
