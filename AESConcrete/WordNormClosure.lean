import AESConcrete.WordByteDiffusionBounds
import AESMixing.SuperboxStationarity

/-!
# Concrete AES word-norm closure and the sharper assembly interface

The first three energy theorems concern the actual AES word kernel and assume
no local norm estimate.  They close the older coefficient 11/65536, conditional
only on successful checking/restoration of the explicit supporting proofs.
This coefficient is weaker than the current certificate's 21/131072.

The final generic assembly theorem permits sharper byte-degree diffusion caps
and a new small-matrix certificate to replace the old comparison.  Its premises
are exact degree-block estimates and a finite matrix inequality, never the
desired word-norm conclusion.  Concrete sharper Gram estimates remain needed.
The historical project and its paused record are not modified.
-/

noncomputable section
open scoped BigOperators Matrix

namespace AESConcrete.WordNorm
open AESMixing

theorem word_superbox_centered_energy (f : AES.Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action AES.wordSuperboxKernel f x ^ 2) ≤
      (11 / 65536 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  WordNormSupport.aes_oriented_word_energy aes_byte_resources
    aes_byte_resources false f hz hs

theorem word_superbox_residual_energy (f : AES.Word → ℝ) :
    (∑ x, action (residualMatrix AES.wordSuperboxKernel 0) f x ^ 2) ≤
      (11 / 65536 : ℝ) ^ 2 * ∑ x, f x ^ 2 := by
  apply residualMatrix_energy AES.word_superbox_pointed
    (by norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]) (11 / 65536)
    word_superbox_centered_energy f

theorem word_superbox_transpose_centered_energy (f : AES.Word → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action (fun y x => AES.wordSuperboxKernel x y) f x ^ 2) ≤
      (11 / 65536 : ℝ) ^ 2 * ∑ x, f x ^ 2 :=
  transpose_residual_energy AES.wordSuperboxKernel 0 ((11 / 65536 : ℝ) ^ 2)
    AES.word_superbox_pointed.zero_column AES.word_superbox_pointed.row_sum
    word_superbox_centered_energy f hz hs

/-- Equivalent counting-measure L2 form, quantified over arbitrary joint
four-byte functions, including functions which do not factor across bytes. -/
theorem word_superbox_residual_l2 (f : AES.Word → ℝ) :
    l2 (action (residualMatrix AES.wordSuperboxKernel 0) f) ≤
      (11 / 65536 : ℝ) * l2 f :=
  l2_le_of_energy _ _ (11 / 65536) (by norm_num)
    (word_superbox_residual_energy f)

theorem old_constant_exceeds_certificate :
    (21 / 131072 : ℝ) < 11 / 65536 := by norm_num

/-- This tests the comparison matrix, not the actual AES operator.  In
particular it is not a cryptanalytic experiment or a lower bound on AES error. -/
def comparisonObstruction : Fin 5 → ℝ := ![100, 18, 53, 42, 15]

theorem old_comparison_exceeds_certificate_rate :
    (21 / 2 : ℝ) * ∑ i, comparisonObstruction i ^ 2 <
      ∑ i, ∑ j, 65536 * dampedComparison i j *
        comparisonObstruction i * comparisonObstruction j := by
  norm_num [comparisonObstruction, dampedComparison, byteComparison,
    Fin.sum_univ_succ]

/-- The old comparison cannot yield 10.5/65536 just by changing the positive
vector witness; at least one load-bearing entry bound must improve. -/
theorem old_comparison_exact_excess :
    (∑ i, ∑ j, 65536 * dampedComparison i j *
        comparisonObstruction i * comparisonObstruction j) -
      (21 / 2 : ℝ) * ∑ i, comparisonObstruction i ^ 2 =
      971983444055226341 / 357341279027200 := by
  norm_num [comparisonObstruction, dampedComparison, byteComparison,
    Fin.sum_univ_succ]

/-- Byte substitution contributes one factor of 9/128 for each residual
degree on each side of diffusion. -/
def dampedCaps (caps : Fin 5 → Fin 5 → ℝ) (i j : Fin 5) : ℝ :=
  (9 / 128 : ℝ) ^ (i.val + j.val) * caps i j

theorem dampedCaps_nonneg {caps : Fin 5 → Fin 5 → ℝ}
    (hcap : ∀ i j, 0 ≤ caps i j) : ∀ i j, 0 ≤ dampedCaps caps i j := by
  intro i j
  exact mul_nonneg (by positivity) (hcap i j)

/-- A cap-parametric version of the old byte-to-word block assembly.  This
exposes the route to a sharper word norm without hardwiring 11/65536. -/
theorem two_substitution_degree_bound_of_caps
    {D E : BinaryWord 8 → BinaryWord 8 → ℝ}
    (hD : ByteResources D) (hE : ByteResources E)
    (L : Equiv.Perm (Fin 4 → BinaryWord 8))
    (caps : Fin 5 → Fin 5 → ℝ) (hcap : ∀ i j, 0 ≤ caps i j)
    (hDiff : ∀ (i j : Fin 5) (f : (Fin 4 → BinaryWord 8) → ℝ),
      f 0 = 0 → (∑ x, f x) = 0 →
      (∑ x, degreeTransfer 0 i j L f x ^ 2) ≤
        (caps i j) ^ 2 * ∑ x, degreeComponent 0 j f x ^ 2)
    (i j : Fin 5) (f : (Fin 4 → BinaryWord 8) → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    l2 (degreeComponent 0 i
      (action (twoSubstitutionKernel D E L) (degreeComponent 0 j f))) ≤
        dampedCaps caps i j * l2 (degreeComponent 0 j f) := by
  let g := action (substitutionKernel E) f
  have hg := substitution_joint_centered hE f hz hs
  have hleft := l2_le_of_energy _ _ ((9 / 128 : ℝ) ^ i.val) (by positivity)
    (substitution_degree_energy hD i
      (fun y => degreeComponent 0 j g (L.symm y)))
  have hmiddle := l2_le_of_energy _ _ (caps i j) (hcap i j)
    (hDiff i j g hg.1 hg.2)
  have hright := l2_le_of_energy _ _ ((9 / 128 : ℝ) ^ j.val) (by positivity)
    (substitution_degree_energy hE j f)
  rw [substitution_degree_commutes hE] at hright
  have hid : degreeComponent 0 i
      (action (twoSubstitutionKernel D E L) (degreeComponent 0 j f)) =
        action (substitutionKernel D)
          (degreeComponent 0 i (fun y => degreeComponent 0 j g (L.symm y))) := by
    rw [twoSubstitutionKernel_action, substitution_degree_commutes hE,
      substitution_degree_commutes hD]
  rw [hid]
  calc
    _ ≤ (9 / 128 : ℝ) ^ i.val * l2 (degreeTransfer 0 i j L g) := hleft
    _ ≤ (9 / 128 : ℝ) ^ i.val * (caps i j * l2 (degreeComponent 0 j g)) :=
      mul_le_mul_of_nonneg_left hmiddle (by positivity)
    _ ≤ (9 / 128 : ℝ) ^ i.val *
        (caps i j * ((9 / 128 : ℝ) ^ j.val * l2 (degreeComponent 0 j f))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hright
        (hcap i j)) (by positivity)
    _ = _ := by rw [dampedCaps, pow_add]; ring

/-- The input hypotheses are exact diffusion block bounds and an explicit
five-dimensional matrix certificate.  Neither is a word-norm assumption. -/
theorem two_substitution_centered_energy_of_caps
    {D E : BinaryWord 8 → BinaryWord 8 → ℝ}
    (hD : ByteResources D) (hE : ByteResources E)
    (L : Equiv.Perm (Fin 4 → BinaryWord 8))
    (caps : Fin 5 → Fin 5 → ℝ) (hcap : ∀ i j, 0 ≤ caps i j)
    (c : ℝ)
    (hsmall : ∀ v : Fin 5 → ℝ,
      (∑ i, action (dampedCaps caps) v i ^ 2) ≤ c ^ 2 * ∑ j, v j ^ 2)
    (hDiff : ∀ (i j : Fin 5) (f : (Fin 4 → BinaryWord 8) → ℝ),
      f 0 = 0 → (∑ x, f x) = 0 →
      (∑ x, degreeTransfer 0 i j L f x ^ 2) ≤
        (caps i j) ^ 2 * ∑ x, degreeComponent 0 j f x ^ 2)
    (f : (Fin 4 → BinaryWord 8) → ℝ)
    (hz : f 0 = 0) (hs : (∑ x, f x) = 0) :
    (∑ x, action (twoSubstitutionKernel D E L) f x ^ 2) ≤
      c ^ 2 * ∑ x, f x ^ 2 := by
  apply degree_matrix_energy 0 (by norm_num [BinaryWord.card]) _
    (dampedCaps caps) c (dampedCaps_nonneg hcap) hsmall f
  exact fun i j => two_substitution_degree_bound_of_caps
    hD hE L caps hcap hDiff i j f hz hs

/-- Concrete actual-AES specialization of the sharper route.  To use
`c = 21/131072`, supply proved sharper MixColumns block caps and a checked
small-matrix certificate.  This statement does not assert those premises. -/
theorem word_superbox_residual_energy_of_caps
    (caps : Fin 5 → Fin 5 → ℝ) (hcap : ∀ i j, 0 ≤ caps i j)
    (c : ℝ)
    (hsmall : ∀ v : Fin 5 → ℝ,
      (∑ i, action (dampedCaps caps) v i ^ 2) ≤ c ^ 2 * ∑ j, v j ^ 2)
    (hDiff : ∀ (i j : Fin 5) (f : AES.Word → ℝ),
      f 0 = 0 → (∑ x, f x) = 0 →
      (∑ x, degreeTransfer 0 i j (byteDiffusionOrientation false) f x ^ 2) ≤
        (caps i j) ^ 2 * ∑ x, degreeComponent 0 j f x ^ 2)
    (f : AES.Word → ℝ) :
    (∑ x, action (residualMatrix AES.wordSuperboxKernel 0) f x ^ 2) ≤
      c ^ 2 * ∑ x, f x ^ 2 := by
  apply residualMatrix_energy AES.word_superbox_pointed
    (by norm_num [AES.Word, BinaryWord.card, Fintype.card_fun]) c ?_ f
  intro g hz hs
  exact two_substitution_centered_energy_of_caps
    aes_byte_resources aes_byte_resources (byteDiffusionOrientation false)
    caps hcap c hsmall hDiff g hz hs

end AESConcrete.WordNorm
