import AESPaper.ManySourceMarginal
import AESPaper.CenteredConvolution
import AESPaper.OneSourceLaw

/-!
# Actual several-source boundary marginals

The first parallel word layer has the product law proved from the fixed
physical input. The actual additive boundary sends each source word through
its own checked output equivalence, then adds the four images. Each one-word
marginal is therefore the balanced convolution of four independent source
pushforwards. Their full joint boundary law is not asserted to be a product.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.ManySourceLaw
open AESMixing AESConcrete
open AESPaper.StartingWord (q wordLaw sourceInput)
open AESPaper.BoundarySourceCoordinates (singleWord outputEquiv)
open AESConcrete.RestrictedMarginalEnergy (marginal)

/-- One observed word, with every other word summed out without normalization. -/
def wordMarginal (f : AES.WordState → ℝ) (c : Fin 4) (y : AES.Word) : ℝ :=
  marginal (fun x : AES.WordState => x c) f y

/-- Source i as seen at boundary output c; probability weights use the inverse. -/
def transportedSource (b : AES.State) (c i : Fin 4) : AES.Word → ℝ :=
  lawRelabel (outputEquiv i c) (wordLaw (sourceInput b i))

theorem singleWord_sum (x : AES.WordState) :
    (∑ i : Fin 4, singleWord i (x i)) = x := by
  funext c
  simp only [Finset.sum_apply, singleWord, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- Additivity is used before any probability law or source independence. -/
theorem boundary_sum (x : AES.WordState) (c : Fin 4) :
    GroupedRecurrence.boundary x c = ∑ i : Fin 4, outputEquiv i c (x i) := by
  calc
    _ = GroupedRecurrence.boundary (∑ i : Fin 4, singleWord i (x i)) c :=
      congrArg (fun z : AES.WordState => GroupedRecurrence.boundary z c) (singleWord_sum x).symm
    _ = ∑ i : Fin 4, outputEquiv i c (x i) := by
      rw [map_sum]
      simp only [Finset.sum_apply, BoundarySourceCoordinates.boundary_singleWord]

/-- Every fixed input has the actual fourfold-convolution boundary marginal.
No independence of the four observed boundary words is inferred. -/
theorem boundary_marginal (b : AES.State) (c : Fin 4) :
    wordMarginal (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) c =
      convolution
        (convolution (transportedSource b c 0) (transportedSource b c 1))
        (convolution (transportedSource b c 2) (transportedSource b c 3)) := by
  change marginal (fun x : AES.WordState => x c)
    (GroupedRecurrence.Pi (GroupedLaw.groupedLaw 0 b)) = _
  rw [GroupedRecurrence.Pi, ManySourceMarginal.marginal_relabel]
  change marginal (fun x : AES.WordState => GroupedRecurrence.boundary x c)
      (GroupedLaw.groupedLaw 0 b) = _
  have hg : GroupedLaw.groupedLaw 0 b =
      (fun x : AES.WordState => ∏ i : Fin 4, wordLaw (sourceInput b i) (x i)) := by
    funext x
    exact StartingWord.grouped_initial_product b x
  have hc : (fun x : AES.WordState => GroupedRecurrence.boundary x c) =
      (fun x => ∑ i : Fin 4, outputEquiv i c (x i)) := by
    funext x
    exact boundary_sum x c
  rw [hg, hc]
  exact ManySourceMarginal.relabeled_four_marginal
    (fun i : Fin 4 => outputEquiv i c) (fun i => wordLaw (sourceInput b i))

theorem wordMarginal_mass (f : AES.WordState → ℝ) (c : Fin 4) :
    (∑ y, wordMarginal f c y) = ∑ x, f x :=
  ManySourceMarginal.marginal_mass _ _

theorem wordMarginal_nonnegative (f : AES.WordState → ℝ) (hf : ∀ x, 0 ≤ f x)
    (c : Fin 4) (y : AES.Word) : 0 ≤ wordMarginal f c y :=
  RestrictedMarginalEnergy.marginal_nonneg _ f hf y

theorem transportedSource_nonnegative (b : AES.State) (c i : Fin 4) (y : AES.Word) :
    0 ≤ transportedSource b c i y := StartingWord.wordLaw_nonnegative _ _

theorem transportedSource_mass (b : AES.State) (c i : Fin 4) :
    (∑ y, transportedSource b c i y) = 1 := by
  unfold transportedSource lawRelabel
  exact (Equiv.sum_comp (outputEquiv i c).symm (wordLaw (sourceInput b i))).trans
    (StartingWord.wordLaw_total _)

theorem wordLaw_zero_eq_differencePoint : wordLaw (0 : AES.Word) = differencePoint 0 := by
  funext y
  simp only [OneSourceLaw.wordLaw_zero_input, differencePoint, eq_comm]

/-- An inactive physical source contributes exactly the additive identity. -/
theorem transportedSource_inactive (b : AES.State) (c i : Fin 4)
    (hi : sourceInput b i = 0) : transportedSource b c i = differencePoint 0 := by
  rw [transportedSource, hi, wordLaw_zero_eq_differencePoint,
    lawRelabel_differencePoint, BoundarySourceCoordinates.outputEquiv_zero]

theorem transportedSource_collision (b : AES.State) (c i : Fin 4) :
    (∑ y, transportedSource b c i y ^ 2) =
      ∑ y, wordLaw (sourceInput b i) y ^ 2 :=
  Equiv.sum_comp (outputEquiv i c).symm (fun y => wordLaw (sourceInput b i) y ^ 2)

theorem transportedSource_collision_lt (b : AES.State) (c i : Fin 4)
    (hi : sourceInput b i ≠ 0) :
    (∑ y, transportedSource b c i y ^ 2) < 17/(15*q) := by
  rw [transportedSource_collision]
  exact StartingWord.wordLaw_collision_lt _ hi

theorem transportedSource_collision_lt_six_fifths (b : AES.State) (c i : Fin 4)
    (hi : sourceInput b i ≠ 0) :
    (∑ y, transportedSource b c i y ^ 2) < 6/(5*q) := by
  rw [transportedSource_collision]
  exact StartingWord.wordLaw_collision_lt_six_fifths _ hi

theorem transportedSource_abs_point_lt (b : AES.State) (c i : Fin 4)
    (hi : sourceInput b i ≠ 0) (y : AES.Word) :
    |transportedSource b c i y| < 20/q :=
  StartingWord.wordLaw_abs_point_lt _ _ hi

/-- Full-group uniform centering is distinct from uniform nonzero-word centering. -/
theorem transportedSource_centered_energy_lt (b : AES.State) (c i : Fin 4)
    (hi : sourceInput b i ≠ 0) :
    CenteredConvolution.centeredEnergy (transportedSource b c i) < 1/(5*q) := by
  rw [CenteredConvolution.centeredEnergy_eq_collision_sub _ (transportedSource_mass b c i),
    ← StartingWord.q_eq_word_card]
  calc
    _ < 6/(5*q)-1/q :=
      sub_lt_sub_right (transportedSource_collision_lt_six_fifths b c i hi) _
    _ = 1/(5*q) := by norm_num [q]

theorem transportedSource_centered_energy_le (b : AES.State) (c i : Fin 4)
    (hi : sourceInput b i ≠ 0) :
    CenteredConvolution.centeredEnergy (transportedSource b c i) ≤ 1/(5*q) :=
  (transportedSource_centered_energy_lt b c i hi).le

end AESPaper.ManySourceLaw
