import AESMixing.FiveDegree

/-! Every degree projection is an orthogonal contraction. Consequently an
arbitrary permutation between two such projections has energy bound one.
These bounds hold for arbitrary joint inputs, with no factorization premise. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

theorem degreeComponent_energy_le {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (j : Fin 5) (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeComponent z j f x ^ 2) ≤ ∑ x, f x ^ 2 := by
  calc
    (∑ x, degreeComponent z j f x ^ 2) ≤
        ∑ i : Fin 5, ∑ x, degreeComponent z i f x ^ 2 :=
      Finset.single_le_sum (fun i _ => Finset.sum_nonneg
        (fun x _ => sq_nonneg (degreeComponent z i f x)))
        (Finset.mem_univ j)
    _ = ∑ x, f x ^ 2 := degreeComponent_pythagoras z hn f

theorem degree_permutation_energy_le {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (j : Fin 5)
    (e : Equiv.Perm (Fin 4 → V)) (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeComponent z j (fun y => f (e y)) x ^ 2) ≤ ∑ x, f x ^ 2 := by
  calc
    (∑ x, degreeComponent z j (fun y => f (e y)) x ^ 2) ≤
        ∑ x, f (e x) ^ 2 := degreeComponent_energy_le z hn j _
    _ = ∑ x, f x ^ 2 := Equiv.sum_comp e (fun x => f x ^ 2)

theorem degree_block_energy_le {V : Type*} [Fintype V] [DecidableEq V]
    (z : V) (hn : 1 < Fintype.card V) (i j : Fin 5)
    (e : Equiv.Perm (Fin 4 → V)) (f : (Fin 4 → V) → ℝ) :
    (∑ x, degreeComponent z i (fun y => degreeComponent z j f (e y)) x ^ 2) ≤
      ∑ x, degreeComponent z j f x ^ 2 :=
  degree_permutation_energy_le z hn i e _

end AESMixing
