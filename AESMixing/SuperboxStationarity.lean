import AESMixing.PointedComposition
import AESMixing.ParallelSuperboxes

/-! Invariant directions of the actual AES word channel and its four
parallel copies. These are exact stationarity statements, not norm bounds. -/
noncomputable section
open scoped BigOperators
namespace AESMixing.AES

theorem word_substitution_pointed :
    PointedBistochastic (substitutionKernel aesByteChannel) (0 : Word) :=
  coordinateKernel_pointed _ _ (fun _ => aes_byte_resources.pointed)

theorem word_superbox_pointed : PointedBistochastic wordSuperboxKernel (0 : Word) := by
  have hz : byteDiffusionEquiv (0 : Word) = 0 := by
    change columnMatrix mixEntry 0 = 0
    exact map_zero _
  exact word_substitution_pointed.compose
    (word_substitution_pointed.relabel_output byteDiffusionEquiv hz)

theorem parallel_superbox_pointed :
    PointedBistochastic parallelSuperboxKernel (0 : WordState) :=
  coordinateKernel_pointed _ _ (fun _ => word_superbox_pointed)

theorem word_superbox_average (f : Word → ℝ) :
    action wordSuperboxKernel (wordAverage 0 f) = wordAverage 0 f :=
  word_superbox_pointed.action_average f

theorem word_superbox_centered (f : Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    action wordSuperboxKernel f 0 = 0 ∧ (∑ y, action wordSuperboxKernel f y) = 0 :=
  ⟨(word_superbox_pointed.action_zero f).trans hz,
    (word_superbox_pointed.action_sum f).trans hs⟩

end AESMixing.AES
