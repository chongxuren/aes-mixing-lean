import AESMixing.SubstitutionDegree
import AESMixing.GroupedEnergy

/-! The paper's five degree spaces, defined from byte positions. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

def degreeIndex (a : Fin 4 → Bool) : Fin 5 :=
  ⟨residualDegree a, Nat.lt_succ_of_le (residualDegree_le a)⟩

def degreeComponent {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (j : Fin 5) (f : (Fin 4 → V) → ℝ) : (Fin 4 → V) → ℝ :=
  groupedFamily degreeIndex (fun a => action (productProjection z a) f) j

theorem degreeComponent_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (f : (Fin 4 → V) → ℝ) :
    (fun x => ∑ j, degreeComponent z j f x) = f := by
  funext x
  rw [show (∑ j, degreeComponent z j f x) = ∑ a, action (productProjection z a) f x
    from groupedFamily_sum degreeIndex _ x]
  exact congrFun (productProjection_decomposition z f) x

theorem degreeComponent_energy {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeComponent z j f x^2) =
      ∑ a, if degreeIndex a = j then ∑ x, action (productProjection z a) f x^2 else 0 :=
  groupedFamily_energy degreeIndex _ (fun a b hab => productProjection_orthogonal z hn a b hab f f) j

theorem degreeComponent_pythagoras {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (f : (Fin 4 → V) → ℝ) :
    (∑ j, ∑ x, degreeComponent z j f x^2) = ∑ x, f x^2 := by
  change (∑ j, ∑ x, groupedFamily degreeIndex
    (fun a => action (productProjection z a) f) j x^2) = _
  rw [groupedFamily_pythagoras degreeIndex _
    (fun a b hab => productProjection_orthogonal z hn a b hab f f)]
  exact (productProjection_pythagoras z hn f).symm

theorem degreeComponent_orthogonal {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (i j : Fin 5) (hij : i ≠ j)
    (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeComponent z i f x * degreeComponent z j f x) = 0 :=
  groupedFamily_orthogonal degreeIndex _
    (fun a b hab => productProjection_orthogonal z hn a b hab f f) i j hij

theorem action_groupedFamily {I J V W : Type*} [Fintype I] [Fintype V] [DecidableEq J]
    (K : W → V → ℝ) (group : I → J) (f : I → V → ℝ) (j : J) :
    action K (groupedFamily group f j) = groupedFamily group (fun a => action K (f a)) j := by
  funext y
  unfold action groupedFamily
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : group a = j <;> simp [ha]

theorem substitution_degree_commutes {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (j : Fin 5) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    action (substitutionKernel D) (degreeComponent 0 j f) =
      degreeComponent 0 j (action (substitutionKernel D) f) := by
  unfold degreeComponent
  rw [action_groupedFamily]
  simp_rw [← substitution_pattern_commutes h]

theorem substitution_degree_energy {D : BinaryWord 8 → BinaryWord 8 → ℝ}
    (h : ByteResources D) (j : Fin 5) (f : (Fin 4 → BinaryWord 8) → ℝ) :
    (∑ y, action (substitutionKernel D) (degreeComponent 0 j f) y^2) ≤
      ((9/128 : ℝ)^j.val)^2 * ∑ x, degreeComponent 0 j f x^2 := by
  have hn : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  rw [substitution_degree_commutes h, degreeComponent_energy 0 hn,
    degreeComponent_energy 0 hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : degreeIndex a = j
  · simp only [ha, if_true]
    have hd : residualDegree a = j.val := congrArg Fin.val ha
    simpa only [← substitution_pattern_commutes h a f, hd] using substitution_pattern_energy h a f
  · simp [ha]

end AESMixing
