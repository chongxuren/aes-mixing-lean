import AESConcrete.ActualRestrictedDensity

/-!
# Shortened source sums as actual full-word restrictions

The first-substitution law is zero unless every inactive input byte stays
zero. Therefore a shortened-graph source, with any further event, has the
same weighted sums as the full-word source restricted only by the output
zero event and that further event. Marginal and signed tensor-response
identities follow for arbitrary coordinate maps, without normalization or
energy inequalities.

Constructive mathematics only; no attacks, manuscript or historical edits.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.RestrictedSourcePushforward
open AESMixing
open AESMixing.AES (maskBit)
open AESConcrete.ByteOrientations (Orientation)
open AESConcrete.WordColumnGram (Byte Word inputColumn inputColumn_nonneg inputColumn_support
  tensorResponse)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom byteDiffusionHom_apply)
open AESConcrete.ActualRestrictedDensity (restrictedSource outputCoordinates)
open AESConcrete.RestrictedMarginalEnergy (marginal)

/-- Exact restriction identity for arbitrary finite sums. -/
theorem sum_subtype_eq_restricted_sum {X M : Type*} [Fintype X] [AddCommMonoid M]
    (p : X → Prop) [DecidablePred p] (f : X → M) :
    (∑ c : {x : X // p x}, f c.val) = ∑ x : X, if p x then f x else 0 := by
  classical
  symm
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) _

/-- The event is on the actual diffused word, in either diffusion direction. -/
def outputZeros (inverse : Bool) (r : Fin 16) (x : Word) : Prop :=
  ∀ i : Fin 4, maskBit r i = true → byteDiffusionOrientation inverse x i = 0

instance (inverse : Bool) (r : Fin 16) : DecidablePred (outputZeros inverse r) := by
  intro x
  unfold outputZeros
  infer_instance

/-- On nonzero source mass, the input-zero half of shortening is automatic. -/
theorem graphZeroConditions_iff_outputZeros_of_inputColumn_ne_zero
    (right : Orientation) (inverse : Bool) (a x : Word) (r z : Fin 16)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (hx : inputColumn right a x ≠ 0) :
    graphZeroConditions (byteDiffusionHom inverse) r z x ↔ outputZeros inverse r x := by
  constructor
  · intro h i hi
    simpa only [byteDiffusionHom_apply] using h.1 i hi
  · intro h
    constructor
    · intro i hi
      simpa only [byteDiffusionHom_apply] using h i hi
    · intro i hi
      exact (inputColumn_support right a x hx i).mp ((ha i).mpr hi)

/-- An unnormalized full-word restriction with no artificial input-zero event. -/
def fullWordSource (right : Orientation) (inverse : Bool) (a : Word) (r : Fin 16)
    (event : Word → Prop) [DecidablePred event] (x : Word) : ℝ :=
  if outputZeros inverse r x ∧ event x then inputColumn right a x else 0

theorem fullWordSource_nonneg (right : Orientation) (inverse : Bool) (a : Word)
    (r : Fin 16) (event : Word → Prop) [DecidablePred event] (x : Word) :
    0 ≤ fullWordSource right inverse a r event x := by
  unfold fullWordSource
  split_ifs
  · exact inputColumn_nonneg right a x
  · exact le_rfl

/-- Signed weights are allowed; this is an exact sum identity, not monotonicity. -/
theorem shortened_weighted_sum_eq_full (right : Orientation) (inverse : Bool) (a : Word)
    (r z : Fin 16) (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : Word → Prop) [DecidablePred event] (w : Word → ℝ) :
    (∑ c : ShortenedGraph (byteDiffusionHom inverse) r z,
      w c.val * restrictedSource right inverse a r z (fun c => event c.val) c) =
      ∑ x : Word, w x * fullWordSource right inverse a r event x := by
  change (∑ c : {x : Word // graphZeroConditions (byteDiffusionHom inverse) r z x},
    w c.val * (if event c.val then inputColumn right a c.val else 0)) = _
  calc
    _ = ∑ x : Word, if graphZeroConditions (byteDiffusionHom inverse) r z x then
        w x * (if event x then inputColumn right a x else 0) else 0 :=
      sum_subtype_eq_restricted_sum _
        (fun x : Word => w x * (if event x then inputColumn right a x else 0))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : inputColumn right a x = 0
      · simp [fullWordSource, hx]
      · have hgraph :=
          graphZeroConditions_iff_outputZeros_of_inputColumn_ne_zero right inverse a x r z ha hx
        by_cases hr : outputZeros inverse r x <;> by_cases he : event x <;>
          simp [fullWordSource, hgraph, hr, he]

/-- Every finite pushforward marginal is preserved, including its event mass. -/
theorem shortened_marginal_eq_full {Y : Type*} [Fintype Y] [DecidableEq Y]
    (right : Orientation) (inverse : Bool) (a : Word) (r z : Fin 16)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : Word → Prop) [DecidablePred event] (coord : Word → Y) :
    marginal (fun c : ShortenedGraph (byteDiffusionHom inverse) r z => coord c.val)
      (restrictedSource right inverse a r z (fun c => event c.val)) =
      marginal coord (fullWordSource right inverse a r event) := by
  funext y
  have h := shortened_weighted_sum_eq_full right inverse a r z ha event
    (fun x => if coord x = y then (1 : ℝ) else 0)
  simpa only [marginal, ite_mul, one_mul, zero_mul] using h

/-- Any signed tensor channel sees exactly the same restricted full-word sum. -/
theorem shortened_tensorResponse_eq_full {I : Type*} [Fintype I] [DecidableEq I]
    (right : Orientation) (inverse : Bool) (a : Word) (r z : Fin 16)
    (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : Word → Prop) [DecidablePred event]
    (T : I → Byte → Byte → ℝ) (coord : Word → I → Byte) :
    tensorResponse T (fun c : ShortenedGraph (byteDiffusionHom inverse) r z => coord c.val)
      (restrictedSource right inverse a r z (fun c => event c.val)) =
      tensorResponse T coord (fullWordSource right inverse a r event) := by
  funext y
  exact shortened_weighted_sum_eq_full right inverse a r z ha event
    (fun x => ∏ i : I, T i (y i) (coord x i))

/-- Actual marked outputs as a coordinate map on all four-byte words. -/
def fullOutputCoordinates (inverse : Bool) (out : Fin 16) (x : Word) :
    MaskCoordinates out → Byte :=
  fun i => byteDiffusionOrientation inverse x i.val

/-- Actual shortened output marginal, now on the full-word source. -/
theorem shortened_output_marginal_eq_full (right : Orientation) (inverse : Bool) (a : Word)
    (r z out : Fin 16) (ha : ∀ i : Fin 4, a i = 0 ↔ maskBit z i = true)
    (event : Word → Prop) [DecidablePred event] :
    marginal (outputCoordinates inverse r z out)
      (restrictedSource right inverse a r z (fun c => event c.val)) =
      marginal (fullOutputCoordinates inverse out) (fullWordSource right inverse a r event) := by
  exact shortened_marginal_eq_full right inverse a r z ha event (fullOutputCoordinates inverse out)

/-- Expanded actual marginal formula, with only the intended full-word events. -/
theorem full_output_marginal_apply (right : Orientation) (inverse : Bool) (a : Word)
    (r out : Fin 16) (event : Word → Prop) [DecidablePred event]
    (y : MaskCoordinates out → Byte) :
    marginal (fullOutputCoordinates inverse out) (fullWordSource right inverse a r event) y =
      ∑ x : Word, if outputZeros inverse r x ∧ event x ∧ fullOutputCoordinates inverse out x = y
        then inputColumn right a x else 0 := by
  unfold marginal fullWordSource
  apply Finset.sum_congr rfl
  intro x _
  by_cases hr : outputZeros inverse r x <;> by_cases he : event x <;>
    by_cases hc : fullOutputCoordinates inverse out x = y <;> simp [hr, he, hc]

end AESConcrete.RestrictedSourcePushforward
