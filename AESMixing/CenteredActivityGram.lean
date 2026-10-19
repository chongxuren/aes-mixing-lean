import AESMixing.CenteredGram
import AESMixing.PointedProducts
import AESMixing.AESGramOrientation

/-! Exact correction for the two fixed word directions in the activity
Gram matrix. The degree-zero certificate bounds the centered response;
positive-degree certificates use the uncentered Gram matrix directly. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {V : Type*} [Fintype V] [Zero V] [DecidableEq V]

omit [Fintype V] in
theorem activityColumn_zero (a : Fin 16) : activityColumn (V := V) a 0 = 1 := by
  have h : maskProjection a (0 : Fin 4 → V) = 0 := by
    funext i
    simp [maskProjection]
  simp [activityColumn, h]

theorem degree_zero_activity_statistics (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) ≃ (Fin 4 → V)) (hL : L 0 = 0) (a : Fin 16) :
    degreeComponent 0 0 (diffusedActivityColumn L a) 0 = 1 ∧
    (∑ x, degreeComponent 0 0 (diffusedActivityColumn L a) x) =
      (Fintype.card V : ℝ)^AES.maskSize a := by
  have hLi : L.symm 0 = 0 := by
    apply L.injective
    simp [hL]
  have hp : PointedBistochastic (degreeKernel (0 : V) 0) (0 : Fin 4 → V) :=
    degree_zero_pointed (0 : V) hn
  simp only [← degreeKernel_action]
  constructor
  · rw [hp.action_zero]
    simpa only [diffusedActivityColumn, hLi] using activityColumn_zero (V := V) a
  · rw [hp.action_sum]
    change (∑ x, activityColumn a (L.symm x)) = _
    rw [L.symm.sum_comp]
    exact activityColumn_sum a

def invariantActivityGram (m : ℝ) (a b : Fin 16) : ℝ :=
  1 + (m^AES.maskSize a - 1) * (m^AES.maskSize b - 1) / (m^4 - 1)

def centeredActivityResponse (L : (Fin 4 → V) ≃ (Fin 4 → V))
    (a : Fin 16) : (Fin 4 → V) → ℝ :=
  wordResidual 0 (degreeComponent 0 0 (diffusedActivityColumn L a))

omit [Zero V] in
theorem wordResidual_linear_combination {A : Type*} [Fintype A]
    (z : V) (f : A → V → ℝ) (c : A → ℝ) :
    wordResidual z (fun x => ∑ a, f a x * c a) =
      fun x => ∑ a, wordResidual z (f a) x * c a := by
  simp_rw [← residualProjection_action]
  funext x
  simp only [action, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem centered_activity_response_expansion
    (L : (Fin 4 → V) ≃ (Fin 4 → V)) (f : (Fin 4 → V) → ℝ) :
    wordResidual 0 (degreeComponent 0 0 (fun x => degreeComponent 0 0 f (L.symm x))) =
      fun x => ∑ a : Fin 16, centeredActivityResponse L a x * activityCoefficient a f := by
  have he : degreeComponent 0 0 (fun x => degreeComponent 0 0 f (L.symm x)) =
      fun x => ∑ a : Fin 16,
        degreeComponent 0 0 (diffusedActivityColumn L a) x * activityCoefficient a f := by
    funext x
    exact degree_diffuse_activity_expansion L 0 f x
  rw [he, wordResidual_linear_combination]
  rfl

theorem centered_activity_transfer_from_gram_certificate {K : Type*} [Fintype K]
    (L : (Fin 4 → V) ≃ (Fin 4 → V))
    (S : K → Fin 16 → ℝ) (d : K → ℝ) (c : ℝ)
    (hd : ∀ k, 0 ≤ d k)
    (hc : ∀ a b, c^2 * (Fintype.card V : ℝ)^AES.maskSize (maskIntersection a b) -
        gram (fun y a => centeredActivityResponse L a y) a b =
      ∑ k, d k * S k a * S k b) (f : (Fin 4 → V) → ℝ) :
    (∑ y, wordResidual 0
      (degreeComponent 0 0 (fun x => degreeComponent 0 0 f (L.symm x))) y^2) ≤
      c^2 * ∑ y, degreeComponent 0 0 f y^2 := by
  have he := gram_domination_from_certificate
    (fun y a => activityColumn (V := V) a y)
    (fun y a => centeredActivityResponse L a y)
    S d c hd (fun a b => by rw [activity_gram]; exact hc a b)
    (fun a => activityCoefficient a f)
  rw [centered_activity_response_expansion]
  simpa only [degree_zero_reconstruction] using he

theorem centered_activity_gram (hn : 1 < Fintype.card V)
    (L : (Fin 4 → V) ≃ (Fin 4 → V)) (hL : L 0 = 0) (a b : Fin 16) :
    gram (fun y a => centeredActivityResponse L a y) a b =
      gram (fun y a => degreeComponent 0 0 (diffusedActivityColumn L a) y) a b -
        invariantActivityGram (Fintype.card V) a b := by
  have hw : 1 < Fintype.card (Fin 4 → V) := by
    simp only [Fintype.card_fun, Fintype.card_fin]
    exact Nat.one_lt_pow (by decide) hn
  have ha := degree_zero_activity_statistics hn L hL a
  have hb := degree_zero_activity_statistics hn L hL b
  unfold gram centeredActivityResponse
  rw [wordResidual_inner 0 hw, wordAverage_inner 0 hw]
  rw [ha.1, hb.1, ha.2, hb.2]
  simp only [invariantActivityGram, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, one_mul]

theorem byteDiffusionOrientation_zero (inverse : Bool) :
    byteDiffusionOrientation inverse 0 = 0 := by
  rw [byteDiffusionOrientation_apply]
  exact map_zero _

theorem oriented_centered_activity_gram_from_ranks (inverse : Bool) (a b : Fin 16)
    (rank : Fin 625 → ℕ)
    (hcount : ∀ i, gramCaseCount inverse a b i = 256^(8-rank i)) :
    gram (fun y a => centeredActivityResponse (byteDiffusionOrientation inverse) a y) a b =
      (rankGramNumerator (fun m => rank (finFunctionFinEquiv m)) 0 : ℝ)/255^4 -
        invariantActivityGram 256 a b := by
  have hn : 1 < Fintype.card (BinaryWord 8) := by norm_num [BinaryWord.card]
  rw [centered_activity_gram hn _ (byteDiffusionOrientation_zero inverse)]
  rw [show gram (fun y a => degreeComponent 0 0
      (diffusedActivityColumn (byteDiffusionOrientation inverse) a) y) a b =
      (rankGramNumerator (fun m => rank (finFunctionFinEquiv m)) 0 : ℝ)/255^4 from
    oriented_activity_gram_from_ranks inverse 0 a b rank hcount]
  norm_num only [BinaryWord.card, Nat.reducePow, Nat.cast_ofNat]

end AESMixing
