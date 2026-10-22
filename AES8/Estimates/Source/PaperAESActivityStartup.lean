import AES8.Reductions.Support.PaperActivitySupportMass
import AES8.Math.PaperFiniteEventMass
import AES8.Reductions.Source.PaperAESStartupSource
import AES8.Reductions.Support.PaperSupportProfileJoin
import AES8.Estimates.Source.PaperStartupScalars

/-! The activity portion of the four-round startup, from exact original
source probabilities and support averaging. Finite ordinary-byte entries
remain an explicit resource; no startup inequality is assumed. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityStartup
open AESMixing PaperActivitySupportMass PaperAESStartupSource PaperRestrictedDiffusion
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def zeroPositions (s : Fin 4 → Bool) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => s i = true)

def exactEvent (s : Fin 4 → Bool) (x : AES.WordState) : Prop :=
  ∀ i, diffusion x i = 0 ↔ s i = true

def properCap (t : ℕ) : ℝ :=
  (17 / (15 * 4294967296)) * (14 / 4294967296)^(3-t)

theorem zeroPositions_card (s : Fin 4 → Bool) :
    (zeroPositions s).card = 4-PaperSupportProjection.supportCount s := by
  let r := maskBitsEquiv.symm s
  have hr : AES.maskBit r = s := maskBitsEquiv.apply_symm_apply s
  have he : zeroPositions s = PaperAESSource.maskSet r := by
    ext i
    simp only [zeroPositions, Finset.mem_filter, Finset.mem_univ, true_and,
      PaperAESSource.mem_maskSet, hr]
  rw [he, PaperAESSource.maskSet_card]
  have h := PaperSupportProfileJoin.supportCount_mask r
  rw [hr] at h
  have hl := AESConcrete.RestrictedCoordinateChoices.maskSize_le_four r
  omega

theorem actual_mass_eq_event (a : AES.State) (s : Fin 4 → Bool) :
    mass s (AESPaper.GroupedLaw.groupedLaw 1 a) =
      eventMass diffusion (active a) (zeroPositions s) (law a) (exactEvent s) := by
  rw [grouped_four_round_response, mass_tensor_response _ AES.word_superbox_pointed,
    eventMass_eq_grouped_initial]
  apply Finset.sum_congr rfl
  intro x _
  rw [indicator_eq_ite]
  by_cases he : exactEvent s x
  · have hz : ∀ i ∈ zeroPositions s, diffusion x i = 0 := by
      intro i hi
      exact (he i).mpr (Finset.mem_filter.mp hi).2
    have he' : ∀ i, diffusion x i = 0 ↔ s i = true := he
    have hb : (∀ i ∈ zeroPositions s, diffusion x i = 0) ∧ exactEvent s x := ⟨hz, he⟩
    simp only [if_pos he', one_mul, if_pos hb]
  · have he' : ¬(∀ i, diffusion x i = 0 ↔ s i = true) := he
    have hb : ¬((∀ i ∈ zeroPositions s, diffusion x i = 0) ∧ exactEvent s x) :=
      fun h => he h.2
    simp only [if_neg he', zero_mul, if_neg hb]

theorem initial_nonneg (a : AES.State) (x : AES.WordState) :
    0 ≤ AESPaper.GroupedLaw.groupedLaw 0 a x := by
  rw [← originalLaw_eq_grouped_initial]
  exact originalLaw_nonneg (active a) (law a) (fun i _ y => law_nonneg a i y) x

theorem actual_mass_nonneg (a : AES.State) (s : Fin 4 → Bool) :
    0 ≤ mass s (AESPaper.GroupedLaw.groupedLaw 1 a) := by
  rw [grouped_four_round_response, mass_tensor_response _ AES.word_superbox_pointed]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (indicator_nonneg _ _) (initial_nonneg a x))

/-- Proper exact-support events are bounded before any normalization. -/
theorem actual_proper_mass_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (s : Fin 4 → Bool)
    (hs : PaperSupportProjection.supportCount s < 4) :
    mass s (AESPaper.GroupedLaw.groupedLaw 1 a) ≤
      properCap (PaperSupportProjection.supportCount s) := by
  rw [actual_mass_eq_event]
  by_cases hz : (active a).card ≤ (zeroPositions s).card
  · rw [eventMass_zero a ha _ hz]
    unfold properCap
    positivity
  · have hz0 : 0 < (zeroPositions s).card := by rw [zeroPositions_card]; omega
    have h := actual_event_mass_le_simple diffusion diffusion_graph_isMDS
      (active a) (zeroPositions s) hz0 (by omega) (law a) (exactEvent s)
      (14 / 4294967296) (17 / (15 * 4294967296)) (by norm_num) (by norm_num)
      (fun i _ x => law_nonneg a i x) (fun i _ => law_mass_one a i)
      (fun i hi x => law_point_le raw a i hi x) (fun i hi => law_collision_le a i hi)
    rw [zeroPositions_card,
      show 4-PaperSupportProjection.supportCount s-1 =
        3-PaperSupportProjection.supportCount s by omega] at h
    exact h

theorem ideal_mass (s : Fin 4 → Bool)
    (hs : 0 < PaperSupportProjection.supportCount s) :
    mass s (uniformExcept (0 : AES.WordState)) =
      (4294967295 : ℝ)^PaperSupportProjection.supportCount s /
        ((4294967296 : ℝ)^4-1) := by
  rw [uniform_mass s hs]
  norm_num [volume, BinaryWord.card]

theorem ideal_proper_mass_le (t : Fin 5) (ht0 : 0 < t.val) (ht4 : t.val < 4)
    (s : Fin 4 → Bool) (hs : PaperSupportProjection.supportCount s = t.val) :
    mass s (uniformExcept (0 : AES.WordState)) ≤ properCap t.val := by
  rw [ideal_mass s (by omega), hs]
  fin_cases t <;> norm_num [properCap] at *

theorem proper_activity_energy (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (t : Fin 5) (ht0 : 0 < t.val) (ht4 : t.val < 4) :
    (4294967296 : ℝ)^5 *
      (∑ y, PaperSupportProjection.component (0 : AES.Word)
        (AESPaper.GroupedLaw.error 1 a) 0 t.val y^2) ≤
      (PaperStartupScalars.properActivitySquared t.val : ℝ) := by
  have he : AESPaper.GroupedLaw.error 1 a =
      AESPaper.GroupedLaw.groupedLaw 1 a - uniformExcept (0 : AES.WordState) := rfl
  rw [he]
  have h := activity_component_energy_le AESConcrete.AES.word_card_gt_one
    (AESPaper.GroupedLaw.groupedLaw 1 a) (uniformExcept (0 : AES.WordState)) t
    (properCap t.val) (by
      intro s hs
      have h0 := actual_mass_nonneg a s
      have h1 := actual_proper_mass_le raw a ha s (by omega)
      rw [hs] at h1
      have g0 : 0 ≤ mass s (uniformExcept (0 : AES.WordState)) := by
        rw [ideal_mass s (by omega)]
        exact div_nonneg (pow_nonneg (by norm_num) _) (by norm_num)
      have g1 := ideal_proper_mass_le t ht0 ht4 s hs
      have hab : |mass s (AESPaper.GroupedLaw.groupedLaw 1 a) -
          mass s (uniformExcept (0 : AES.WordState))| ≤ properCap t.val :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2)
  have hh := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4294967296^5)
  simp only [AESConcrete.AES.word_card_exact] at hh
  apply hh.trans_eq
  norm_num [PaperStartupScalars.properActivitySquared, PaperStartupScalars.collision,
    PaperStartupScalars.point, PaperComparison.q, properCap]
  ring

theorem single_zero_mass_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) (i : Fin 4) :
    PaperFiniteEventMass.mass (AESPaper.GroupedLaw.groupedLaw 0 a)
      (fun x => diffusion x i = 0) ≤ (17 / (15 * 4294967296) : ℝ) := by
  have he : PaperFiniteEventMass.mass (AESPaper.GroupedLaw.groupedLaw 0 a)
      (fun x => diffusion x i = 0) =
      eventMass diffusion (active a) {i} (law a) (fun _ => True) := by
    rw [eventMass_eq_grouped_initial]
    simp only [PaperFiniteEventMass.mass, Finset.mem_singleton, forall_eq,
      and_true]
    exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun x => by
      by_cases hx : diffusion x i = 0 <;> simp [hx])
  rw [he]
  by_cases hw : (active a).card ≤ ({i} : Finset (Fin 4)).card
  · rw [eventMass_zero a ha _ hw]
    norm_num
  · have h := actual_event_mass_le_simple diffusion diffusion_graph_isMDS
      (active a) {i} (by simp) (by omega) (law a) (fun _ => True)
      (14 / 4294967296) (17 / (15 * 4294967296)) (by norm_num) (by norm_num)
      (fun j _ x => law_nonneg a j x) (fun j _ => law_mass_one a j)
      (fun j hj x => law_point_le raw a j hj x) (fun j hj => law_collision_le a j hj)
    simpa using h

theorem all_active_mass (a : AES.State) :
    mass (fun _ : Fin 4 => false) (AESPaper.GroupedLaw.groupedLaw 1 a) =
      PaperFiniteEventMass.mass (AESPaper.GroupedLaw.groupedLaw 0 a)
        (fun x => ∀ i, diffusion x i ≠ 0) := by
  rw [grouped_four_round_response, mass_tensor_response _ AES.word_superbox_pointed]
  simp only [PaperFiniteEventMass.mass, indicator_eq_ite, Bool.false_eq_true,
    iff_false, ite_mul, one_mul, zero_mul]
  exact Fintype.sum_equiv (Equiv.refl _) _ _ (fun x => by
    by_cases hx : ∀ i, diffusion x i ≠ 0 <;> simp [hx])

theorem actual_full_interval (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) :
    1-4*(17 / (15 * 4294967296) : ℝ) ≤
      mass (fun _ : Fin 4 => false) (AESPaper.GroupedLaw.groupedLaw 1 a) ∧
    mass (fun _ : Fin 4 => false) (AESPaper.GroupedLaw.groupedLaw 1 a) ≤ 1 := by
  rw [all_active_mass]
  constructor
  · simpa only [Fintype.card_fin, Nat.cast_ofNat] using
      PaperFiniteEventMass.complement_union_lower (AESPaper.GroupedLaw.groupedLaw 0 a)
        (initial_nonneg a) (AESPaper.GroupedLaw.grouped_total 0 a)
        (fun i x => diffusion x i = 0) (17 / (15 * 4294967296))
        (single_zero_mass_le raw a ha)
  · exact (PaperFiniteEventMass.le_total _ (initial_nonneg a) _).trans_eq
      (AESPaper.GroupedLaw.grouped_total 0 a)

theorem full_support_mask (s : Fin 4 → Bool)
    (hs : PaperSupportProjection.supportCount s = 4) : s = fun _ => false := by
  have hc : (zeroPositions s).card = 0 := by rw [zeroPositions_card, hs]
  have he := Finset.card_eq_zero.mp hc
  funext i
  cases hi : s i with
  | false => rfl
  | true =>
    have hm : i ∈ zeroPositions s := by simp [zeroPositions, hi]
    rw [he] at hm
    simp at hm

theorem ideal_full_interval :
    1-4*(17 / (15 * 4294967296) : ℝ) ≤
      mass (fun _ : Fin 4 => false) (uniformExcept (0 : AES.WordState)) ∧
    mass (fun _ : Fin 4 => false) (uniformExcept (0 : AES.WordState)) ≤ 1 := by
  rw [ideal_mass _ (by decide)]
  norm_num [PaperSupportProjection.supportCount]

theorem full_activity_energy (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (ha : a ≠ 0) :
    (4294967296 : ℝ)^5 *
      (∑ y, PaperSupportProjection.component (0 : AES.Word)
        (AESPaper.GroupedLaw.error 1 a) 0 4 y^2) ≤
      (PaperStartupScalars.fullActivitySquared : ℝ) := by
  have he : AESPaper.GroupedLaw.error 1 a =
      AESPaper.GroupedLaw.groupedLaw 1 a - uniformExcept (0 : AES.WordState) := rfl
  rw [he]
  have h := activity_component_energy_le AESConcrete.AES.word_card_gt_one
    (AESPaper.GroupedLaw.groupedLaw 1 a) (uniformExcept (0 : AES.WordState)) (4 : Fin 5)
    (4*(17 / (15 * 4294967296))) (by
      intro s hs
      rw [full_support_mask s hs]
      obtain ⟨h0, h1⟩ := actual_full_interval raw a ha
      obtain ⟨g0, g1⟩ := ideal_full_interval
      have hab : |mass (fun _ : Fin 4 => false) (AESPaper.GroupedLaw.groupedLaw 1 a) -
          mass (fun _ : Fin 4 => false) (uniformExcept (0 : AES.WordState))| ≤
          4*(17 / (15 * 4294967296)) := abs_le.mpr ⟨by linarith, by linarith⟩
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2)
  have hh := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4294967296^5)
  apply hh.trans_eq
  norm_num [BinaryWord.card, PaperStartupScalars.fullActivitySquared,
    PaperStartupScalars.collision, PaperComparison.q]

end AES8.PaperAESActivityStartup
