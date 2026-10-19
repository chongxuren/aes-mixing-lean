import AESPaper.GroupedRecurrence
import AESPaper.Profile
import AESConcrete.WordStepZeros

/-!
# Exact activity / degree-one zeros on the v9 word boundary

The forward boundary in the grouped physical law is exactly the checked
`wordMixAddEquiv`.  Its action on laws therefore uses that equivalence's
inverse.  This identifies the already checked word-MDS cancellation with
the actual `ProfileSpace.component` projections, on arbitrary joint inputs.

The zero blocks concern `Pi`, `H Pi`, and `H Pi H`.  They do not assert a
zero block for the repeated operator `(H Pi)^2`: intermediate residual
degrees two through four can contribute there.  No centering or numerical
norm assumption is needed for the identities below.  All shared sources
used here match the fixed 13,659-pair closure; no later activity extension
from the separate round-target project is imported.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section

namespace AESPaper.BoundaryZeros
open AESMixing AESMixing.AES
open AESPaper.ProfileSpace AESPaper.GroupedRecurrence
open AESConcrete.WordCrossZero AESConcrete.WordStepZeros

/-- The physical execution order agrees before taking any inverse. -/
theorem boundary_wordMix (x : AES.WordState) :
    boundary x = AES.wordMix x := by
  -- Editorial: rewrite only the named maps; a single definitional equality
  -- between the two nested concrete AES expressions can expand far too much.
  have hs (y : AES.State) : shiftRowsEquiv y = AES.shiftRows y := rfl
  have hm (y : AES.State) : mixColumnsEquiv y = AES.mixColumns y := rfl
  have hw : AES.wordMix x = transposeState.symm (AES.wordDiffusion (transposeState x)) := by
    funext col row
    exact AES.wordMix_apply x col row
  rw [hw, boundary_apply, hs, hm, hs, AES.wordDiffusion]

/-- Equality of additive equivalences also identifies their inverse maps. -/
theorem boundary_eq_wordMixAddEquiv : boundary = wordMixAddEquiv := by
  -- Stop extensionality at the additive-equivalence interface, before bits.
  apply AddEquiv.ext
  intro x
  rw [wordMixAddEquiv_apply]
  exact boundary_wordMix x

/-- Forward law transport evaluates the old law at the inverse word map. -/
theorem Pi_eq_wordMix_transport (f : AES.WordState → ℝ) :
    Pi f = fun x => f (wordMixAddEquiv.symm x) := by
  funext x
  rw [Pi_apply, boundary_eq_wordMixAddEquiv]

/-- The already checked concrete kernel is the actual grouped two-round step. -/
theorem H_Pi_eq_wordStep (f : AES.WordState → ℝ) :
    H (Pi f) = action wordStepKernel f := by
  rw [wordStepKernel_action, Pi_eq_wordMix_transport]
  rfl

/-- Activity output from one residual word is identically zero. -/
theorem Pi_zero_one (f : AES.WordState → ℝ) :
    degreeComponent (0 : AES.Word) 0
      (Pi (degreeComponent (0 : AES.Word) 1 f)) = 0 := by
  rw [Pi_eq_wordMix_transport]
  funext x
  exact word_degree_zero_one_apply f x

/-- One residual output word from activity input is identically zero. -/
theorem Pi_one_zero (f : AES.WordState → ℝ) :
    degreeComponent (0 : AES.Word) 1
      (Pi (degreeComponent (0 : AES.Word) 0 f)) = 0 := by
  rw [Pi_eq_wordMix_transport]
  funext x
  exact word_degree_one_zero_apply f x

theorem H_Pi_zero_one (f : AES.WordState → ℝ) :
    degreeComponent (0 : AES.Word) 0
      (H (Pi (degreeComponent (0 : AES.Word) 1 f))) = 0 := by
  rw [H_Pi_eq_wordStep]
  exact wordStep_zero_one f

theorem H_Pi_one_zero (f : AES.WordState → ℝ) :
    degreeComponent (0 : AES.Word) 1
      (H (Pi (degreeComponent (0 : AES.Word) 0 f))) = 0 := by
  rw [H_Pi_eq_wordStep]
  exact wordStep_one_zero f

/-- The right word layer commutes with residual degree, so both two-layer
cross couplings used in the paper vanish on the same word spaces. -/
theorem H_Pi_H_zero_one (f : AES.WordState → ℝ) :
    degreeComponent (0 : AES.Word) 0
      (H (Pi (H (degreeComponent (0 : AES.Word) 1 f)))) = 0 := by
  have hc : H (degreeComponent (0 : AES.Word) 1 f) =
      degreeComponent (0 : AES.Word) 1 (H f) :=
    AESConcrete.WordChannelCommutation.parallel_word_degree_commutes 1 f
  rw [hc]
  exact H_Pi_zero_one (H f)

theorem H_Pi_H_one_zero (f : AES.WordState → ℝ) :
    degreeComponent (0 : AES.Word) 1
      (H (Pi (H (degreeComponent (0 : AES.Word) 0 f)))) = 0 := by
  have hc : H (degreeComponent (0 : AES.Word) 0 f) =
      degreeComponent (0 : AES.Word) 0 (H f) :=
    AESConcrete.WordChannelCommutation.parallel_word_degree_commutes 0 f
  rw [hc]
  exact H_Pi_one_zero (H f)

/- These are the actual continuous linear projections used by the fixed
profile.  `WithLp.toLp` only packages the same counting-measure vector.
Editorial: specialize the opaque generic component_toLp_apply coercion
bridge below, then compose explicitly typed equalities. Elaborating the
same coercion directly at a nested concrete Pi input can unfold its enormous
finite state space; generic proof checking avoids that delta-unification.
Use explicit PiLp.ext and keep component/coercion rewrites out of wrappers. -/

theorem component_toLp_apply (i : Fin 5) (g : AES.WordState → ℝ) (x : AES.WordState) :
    component i (WithLp.toLp 2 g) x = degreeComponent (0 : AES.Word) i g x :=
  component_apply i (WithLp.toLp 2 g) x

theorem component_Pi_zero_one (f : ProfileSpace.State) :
    component 0 (WithLp.toLp 2 (Pi (fun x => component 1 f x))) = 0 := by
  apply PiLp.ext
  intro x
  have hi : (fun y => component 1 f y) =
      degreeComponent (0 : AES.Word) 1 (fun y => f y) :=
    funext (fun y => component_apply 1 f y)
  have ho : component 0 (WithLp.toLp 2 (Pi (fun y => component 1 f y))) x =
      degreeComponent (0 : AES.Word) 0 (Pi (fun y => component 1 f y)) x :=
    component_toLp_apply 0 (Pi (fun y => component 1 f y)) x
  have hz : degreeComponent (0 : AES.Word) 0 (Pi (fun y => component 1 f y)) x = 0 :=
    (congrArg (fun g : AES.WordState → ℝ =>
      degreeComponent (0 : AES.Word) 0 (Pi g) x) hi).trans
      (congrFun (Pi_zero_one (fun y => f y)) x)
  exact ho.trans hz

theorem component_Pi_one_zero (f : ProfileSpace.State) :
    component 1 (WithLp.toLp 2 (Pi (fun x => component 0 f x))) = 0 := by
  apply PiLp.ext
  intro x
  have hi : (fun y => component 0 f y) =
      degreeComponent (0 : AES.Word) 0 (fun y => f y) :=
    funext (fun y => component_apply 0 f y)
  have ho : component 1 (WithLp.toLp 2 (Pi (fun y => component 0 f y))) x =
      degreeComponent (0 : AES.Word) 1 (Pi (fun y => component 0 f y)) x :=
    component_toLp_apply 1 (Pi (fun y => component 0 f y)) x
  have hz : degreeComponent (0 : AES.Word) 1 (Pi (fun y => component 0 f y)) x = 0 :=
    (congrArg (fun g : AES.WordState → ℝ =>
      degreeComponent (0 : AES.Word) 1 (Pi g) x) hi).trans
      (congrFun (Pi_one_zero (fun y => f y)) x)
  exact ho.trans hz

theorem component_H_Pi_zero_one (f : ProfileSpace.State) :
    component 0 (WithLp.toLp 2 (H (Pi (fun x => component 1 f x)))) = 0 := by
  apply PiLp.ext
  intro x
  have hi : (fun y => component 1 f y) =
      degreeComponent (0 : AES.Word) 1 (fun y => f y) :=
    funext (fun y => component_apply 1 f y)
  have ho : component 0 (WithLp.toLp 2 (H (Pi (fun y => component 1 f y)))) x =
      degreeComponent (0 : AES.Word) 0 (H (Pi (fun y => component 1 f y))) x :=
    component_toLp_apply 0 (H (Pi (fun y => component 1 f y))) x
  have hz : degreeComponent (0 : AES.Word) 0 (H (Pi (fun y => component 1 f y))) x = 0 :=
    (congrArg (fun g : AES.WordState → ℝ =>
      degreeComponent (0 : AES.Word) 0 (H (Pi g)) x) hi).trans
      (congrFun (H_Pi_zero_one (fun y => f y)) x)
  exact ho.trans hz

theorem component_H_Pi_one_zero (f : ProfileSpace.State) :
    component 1 (WithLp.toLp 2 (H (Pi (fun x => component 0 f x)))) = 0 := by
  apply PiLp.ext
  intro x
  have hi : (fun y => component 0 f y) =
      degreeComponent (0 : AES.Word) 0 (fun y => f y) :=
    funext (fun y => component_apply 0 f y)
  have ho : component 1 (WithLp.toLp 2 (H (Pi (fun y => component 0 f y)))) x =
      degreeComponent (0 : AES.Word) 1 (H (Pi (fun y => component 0 f y))) x :=
    component_toLp_apply 1 (H (Pi (fun y => component 0 f y))) x
  have hz : degreeComponent (0 : AES.Word) 1 (H (Pi (fun y => component 0 f y))) x = 0 :=
    (congrArg (fun g : AES.WordState → ℝ =>
      degreeComponent (0 : AES.Word) 1 (H (Pi g)) x) hi).trans
      (congrFun (H_Pi_one_zero (fun y => f y)) x)
  exact ho.trans hz

theorem component_H_Pi_H_zero_one (f : ProfileSpace.State) :
    component 0 (WithLp.toLp 2 (H (Pi (H (fun x => component 1 f x))))) = 0 := by
  apply PiLp.ext
  intro x
  have hi : (fun y => component 1 f y) =
      degreeComponent (0 : AES.Word) 1 (fun y => f y) :=
    funext (fun y => component_apply 1 f y)
  have ho : component 0 (WithLp.toLp 2 (H (Pi (H (fun y => component 1 f y))))) x =
      degreeComponent (0 : AES.Word) 0 (H (Pi (H (fun y => component 1 f y)))) x :=
    component_toLp_apply 0 (H (Pi (H (fun y => component 1 f y)))) x
  have hz : degreeComponent (0 : AES.Word) 0 (H (Pi (H (fun y => component 1 f y)))) x = 0 :=
    (congrArg (fun g : AES.WordState → ℝ =>
      degreeComponent (0 : AES.Word) 0 (H (Pi (H g))) x) hi).trans
      (congrFun (H_Pi_H_zero_one (fun y => f y)) x)
  exact ho.trans hz

theorem component_H_Pi_H_one_zero (f : ProfileSpace.State) :
    component 1 (WithLp.toLp 2 (H (Pi (H (fun x => component 0 f x))))) = 0 := by
  apply PiLp.ext
  intro x
  have hi : (fun y => component 0 f y) =
      degreeComponent (0 : AES.Word) 0 (fun y => f y) :=
    funext (fun y => component_apply 0 f y)
  have ho : component 1 (WithLp.toLp 2 (H (Pi (H (fun y => component 0 f y))))) x =
      degreeComponent (0 : AES.Word) 1 (H (Pi (H (fun y => component 0 f y)))) x :=
    component_toLp_apply 1 (H (Pi (H (fun y => component 0 f y)))) x
  have hz : degreeComponent (0 : AES.Word) 1 (H (Pi (H (fun y => component 0 f y)))) x = 0 :=
    (congrArg (fun g : AES.WordState → ℝ =>
      degreeComponent (0 : AES.Word) 1 (H (Pi (H g))) x) hi).trans
      (congrFun (H_Pi_H_one_zero (fun y => f y)) x)
  exact ho.trans hz

end AESPaper.BoundaryZeros
