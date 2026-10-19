import AESPaper.ResponseMaskSelection
import AESPaper.ActualRestrictedWordResponse

/-!
# Exact transport of joint restricted responses between coordinate labels

All source weights may be signed and unnormalized. Coordinate reindexing is
an actual equivalence, so marginal transport and response energy are exact.
The marked-mask specialization retains the same boundary restriction and
further source event. Extra outputs may depend on the same source as the core.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace AESPaper.ResponseCoordinateTransport
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESConcrete.RestrictedMarginalEnergy (marginal)
open AESPaper.ResponseMaskSelection (unionCoordinateEquiv)
open AESPaper.WordRestrictedResponse (residual delta)
open AESPaper.StartingWord (q sourceInput)
open AESPaper.WordDamping (nu)

section Generic
variable {X I K V : Type*}
  [Fintype X] [Fintype I] [Fintype K] [Fintype V]
  [DecidableEq I] [DecidableEq K]

/-- Tuple reindexing is bijective even when the source coordinates depend. -/
abbrev tupleEquiv (e : K ≃ I) : (K → V) ≃ (I → V) :=
  FiniteTensorEnergy.indexTupleEquiv (V := V) e

omit [Fintype I] [Fintype K] [Fintype V] [DecidableEq I] [DecidableEq K] in
theorem tupleEquiv_apply (e : K ≃ I) (y : K → V) (i : I) :
    tupleEquiv (V := V) e y i = y (e.symm i) := rfl

omit [Fintype I] [Fintype K] [Fintype V] [DecidableEq I] [DecidableEq K] in
theorem tupleEquiv_symm_apply (e : K ≃ I) (y : I → V) (k : K) :
    (tupleEquiv (V := V) e).symm y k = y (e k) := rfl

/-- Arbitrary joint marginals transport without changing their weights. -/
theorem marginal_reindex [DecidableEq V] (e : K ≃ I)
    (coord : X → I → V) (g : X → ℝ) (y : K → V) :
    marginal (fun c k => coord c (e k)) g y =
      marginal coord g (tupleEquiv (V := V) e y) := by
  let E := tupleEquiv (V := V) e
  unfold marginal
  apply Finset.sum_congr rfl
  intro c _
  have hc : E.symm (coord c) = y ↔ coord c = E y := by
    constructor
    · intro h
      calc
        coord c = E (E.symm (coord c)) := (E.apply_symm_apply _).symm
        _ = E y := congrArg E h
    · intro h
      calc
        E.symm (coord c) = E.symm (E y) := congrArg E.symm h
        _ = y := E.symm_apply_apply y
  change (if E.symm (coord c) = y then g c else 0) =
    if coord c = E y then g c else 0
  simp only [hc]

/-- Counting-measure tensor energy is unchanged by coordinate reindexing. -/
theorem tensorResponse_reindex_energy (e : K ≃ I) (T : I → V → V → ℝ)
    (coord : X → I → V) (g : X → ℝ) :
    (∑ y : K → V, WordColumnGram.tensorResponse (fun k => T (e k))
      (fun c k => coord c (e k)) g y ^ 2) =
      ∑ y : I → V, WordColumnGram.tensorResponse T coord g y ^ 2 :=
  RestrictedCoordinateChoices.tensorResponse_reindex_energy e T coord g

/-- The same exact identity on the residual action of the joint marginal. -/
theorem marginal_action_reindex_energy [DecidableEq V]
    (e : K ≃ I) (T : I → V → V → ℝ) (coord : X → I → V) (g : X → ℝ) :
    (∑ y : K → V, action (coordinateKernel (fun k => T (e k)))
      (marginal (fun c k => coord c (e k)) g) y ^ 2) =
      ∑ y : I → V, action (coordinateKernel T) (marginal coord g) y ^ 2 := by
  simpa only [ActualRestrictedResponse.tensorResponse_eq_action_marginal] using
    tensorResponse_reindex_energy e T coord g

end Generic

/-- The actual joint-event marginal has exactly the same response energy
after splitting its marked coordinates into core and complement. -/
theorem marked_union_response_energy (b : AES.State) (r core extra : Fin 16)
    (hd : MaskDisjoint core extra)
    (event : AES.WordState → Prop) [DecidablePred event] :
    (∑ y, action (coordinateKernel
      (fun _ : MaskCoordinates core ⊕ MaskCoordinates extra => residual))
      (marginal (fun x => Sum.elim (ActualRestrictedSource.markedCoordinates core x)
        (ActualRestrictedSource.markedCoordinates extra x))
        (ActualRestrictedSource.boundaryRestriction b r event)) y ^ 2) =
      ∑ y, action (coordinateKernel
        (fun _ : MaskCoordinates (maskUnion core extra) => residual))
        (ActualRestrictedSource.markedMarginal b r (maskUnion core extra) event) y ^ 2 := by
  let e := unionCoordinateEquiv core extra hd
  have he := marginal_action_reindex_energy e
    (fun _ : MaskCoordinates (maskUnion core extra) => residual)
    (ActualRestrictedSource.markedCoordinates (maskUnion core extra))
    (ActualRestrictedSource.boundaryRestriction b r event)
  have hC : (fun x k =>
      ActualRestrictedSource.markedCoordinates (maskUnion core extra) x (e k)) =
      (fun x => Sum.elim (ActualRestrictedSource.markedCoordinates core x)
        (ActualRestrictedSource.markedCoordinates extra x)) := by
    funext x k
    cases k <;> rfl
  rw [hC] at he
  exact he

/-- The high-response branch transported back to its marked union mask. -/
theorem actual_high_union_energy (b : AES.State) (r z s u core extra : Fin 16)
    (hsu : MaskDisjoint s u) (hzu : MaskDisjoint z (maskUnion s u))
    (hsize : maskSize r + maskSize z + maskSize s + maskSize u = 4)
    (hd : MaskDisjoint core extra) (hr : MaskDisjoint r (maskUnion core extra))
    (hcore : maskSize r + maskSize z + maskSize core = 4)
    (ha : ∀ i : Fin 4, sourceInput b i = 0 ↔ maskBit z i = true)
    (event : AES.WordState → Prop) [DecidablePred event] :
    (∑ y, action (coordinateKernel
      (fun _ : MaskCoordinates (maskUnion core extra) => residual))
      (ActualRestrictedSource.markedMarginal b r (maskUnion core extra) event) y ^ 2) ≤
      nu^(2 * maskSize core) * delta^maskSize extra *
        ((20/q)^(2 * maskSize r) * (6/(5*q))^maskSize core) := by
  rw [← marked_union_response_energy b r core extra hd event]
  have h := ActualRestrictedWordResponse.actual_high_energy b r z s u core hsu hzu hsize
    (ResponseMaskSelection.disjoint_core r core extra hr) hcore ha event
    (ActualRestrictedSource.markedCoordinates extra)
  simpa only [maskCoordinates_card] using h

end AESPaper.ResponseCoordinateTransport
