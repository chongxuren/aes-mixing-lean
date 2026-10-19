import AESMixing.IncidenceKernel

/-! The MDS shortening property gives the row and column bounds for
marked-coordinate incidence matrices. No distributional independence
assumption is used in this operator estimate. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES

theorem empty_mask_bit (i : Fin 4) : maskBit 0 i = false := by
  fin_cases i <;> decide

theorem empty_mask_coordinate (i : MaskCoordinates 0) : False := by
  have h := i.property
  rw [empty_mask_bit] at h
  contradiction

theorem mask_disjoint_empty (r : Fin 16) : MaskDisjoint r 0 := by
  intro i _ h
  rw [empty_mask_bit] at h
  contradiction

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def shortenedOutput (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z out : Fin 16)
    (x : ShortenedGraph L r z) : MaskCoordinates out → V :=
  fun i => L x.val i.val

def shortenedInput (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z inp : Fin 16)
    (x : ShortenedGraph L r z) : MaskCoordinates inp → V :=
  fun i => x.val i.val

theorem shortened_output_fiber_bound
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out : Fin 16) (hr : MaskDisjoint r out) (v : MaskCoordinates out → V) :
    Fintype.card {x : ShortenedGraph L r z // shortenedOutput L r z out x = v} ≤
      Fintype.card V ^ (4-(maskSize r+maskSize z+maskSize out)) := by
  classical
  have he (x : ShortenedGraph L r z) : shortenedOutput L r z out x = v ↔
      shortenedProjection L r z out 0 x = (v,fun _ => (0 : V)) := by
    constructor
    · intro h
      exact Prod.ext h (funext (fun i => (empty_mask_coordinate i).elim))
    · intro h
      exact congrArg Prod.fst h
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  have h := shortened_projection_fiber_bound L hL r z out 0 hr (mask_disjoint_empty z)
    (v,fun _ => (0 : V))
  simpa only [show maskSize 0 = 0 by decide, Nat.add_zero] using h

theorem shortened_input_fiber_bound
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z inp : Fin 16) (hz : MaskDisjoint z inp) (v : MaskCoordinates inp → V) :
    Fintype.card {x : ShortenedGraph L r z // shortenedInput L r z inp x = v} ≤
      Fintype.card V ^ (4-(maskSize r+maskSize z+maskSize inp)) := by
  classical
  have he (x : ShortenedGraph L r z) : shortenedInput L r z inp x = v ↔
      shortenedProjection L r z 0 inp x = (fun _ => (0 : V),v) := by
    constructor
    · intro h
      exact Prod.ext (funext (fun i => (empty_mask_coordinate i).elim)) h
    · intro h
      exact congrArg Prod.snd h
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  have h := shortened_projection_fiber_bound L hL r z 0 inp (mask_disjoint_empty r) hz
    (fun _ => (0 : V),v)
  simpa only [show maskSize 0 = 0 by decide, Nat.add_zero] using h

theorem shortened_incidence_energy
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (r z out inp : Fin 16) (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (f : (MaskCoordinates inp → V) → ℝ) :
    (∑ y, action (incidenceMultiplicity
      (shortenedOutput L r z out) (shortenedInput L r z inp)) f y^2) ≤
      (Fintype.card V : ℝ)^(4-(maskSize r+maskSize z+maskSize out)) *
      (Fintype.card V : ℝ)^(4-(maskSize r+maskSize z+maskSize inp)) * ∑ x, f x^2 := by
  have h := incidenceMultiplicity_schur (shortenedOutput L r z out) (shortenedInput L r z inp)
    (Fintype.card V^(4-(maskSize r+maskSize z+maskSize out)))
    (Fintype.card V^(4-(maskSize r+maskSize z+maskSize inp)))
    (shortened_output_fiber_bound L hL r z out hr)
    (shortened_input_fiber_bound L hL r z inp hz) f
  simpa only [Nat.cast_pow] using h

end AESMixing
