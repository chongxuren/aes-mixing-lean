import AES8.Reductions.Source.PaperAESStartupSource
import AES8.Math.PaperPointedSupportResponse
import AES8.Estimates.Word.SharpWordNorm
import AES8.Reductions.Source.PaperAESSourceResidual
import AES8.Reductions.Support.PaperSupportBlockLift
import AES8.Reductions.Support.PaperSupportProfileJoin

/-!
# Restricted positive-residual startup on the actual four-round source

The zero and nonzero indicators remain on the original independent word
source. Restricted marginal energy is bounded before the orthogonal position
sum. Numerical startup-vector comparison is intentionally a separate leaf.
The ordinary source bound is explicit and independent of its proof provider.
Constructive proofs only; no attacks or assumed component cap.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESStartupResidual
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.WordColumnGram (tensorResponse)
open PaperRestrictedDiffusion PaperAESStartupSource
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- Every position outside the prescribed zero mask remains nonzero. -/
def nonzeroOutside (r : Fin 16) (x : AES.WordState) : Prop :=
  ∀ i : Fin 4, maskBit r i ≠ true → diffusion x i ≠ 0

/-- The full exact support event, without normalization or conditioning. -/
def fullSource (a : AES.State) (r : Fin 16) (x : AES.WordState) : ℝ :=
  PaperPointedSupportResponse.exactSource r diffusion
    (AESPaper.GroupedLaw.groupedLaw 0 a) x

theorem exactZeroPattern_diffusion (r : Fin 16) (x : AES.WordState) :
    PaperPointedSupportResponse.exactZeroPattern r (diffusion x) ↔
      (∀ i ∈ PaperAESSource.maskSet r, diffusion x i = 0) ∧ nonzeroOutside r x := by
  constructor
  · intro h
    constructor
    · intro i hi
      exact (h i).mpr ((PaperAESSource.mem_maskSet r i).mp hi)
    · intro i hi hz
      exact hi ((h i).mp hz)
  · rintro ⟨hz, hn⟩ i
    constructor
    · intro hi
      by_contra hr
      exact hn i hr hi
    · intro hi
      exact hz i ((PaperAESSource.mem_maskSet r i).mpr hi)

/-- The signed residual response of the marginal is exactly the response
of the original source with the full output support indicator. -/
theorem marginal_action_eq_response (a : AES.State) (r out : Fin 16)
    (T : AES.Word → AES.Word → ℝ) :
    action (coordinateKernel (fun _ : PaperAESSource.maskSet out => T))
      (paperJointMarginal diffusion (active a) (PaperAESSource.maskSet r)
        (PaperAESSource.maskSet out) (law a) (nonzeroOutside r)) =
      tensorResponse (fun _ : PaperAESSource.maskSet out => T)
        (fun x i => diffusion x i.val) (fullSource a r) := by
  funext y
  unfold action
  simp_rw [jointMarginal_eq_grouped_initial]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold tensorResponse AESConcrete.WordColumnGram.tensorColumn fullSource
    PaperPointedSupportResponse.exactSource
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : PaperPointedSupportResponse.exactZeroPattern r (diffusion x)
  · have hh := (exactZeroPattern_diffusion r x).mp he
    have htest (u : PaperAESSource.maskSet out → AES.Word) :
        ((∀ i ∈ PaperAESSource.maskSet r, diffusion x i = 0) ∧ nonzeroOutside r x ∧
          (fun i : PaperAESSource.maskSet out => diffusion x i.val) = u) ↔
          (fun i : PaperAESSource.maskSet out => diffusion x i.val) = u :=
      ⟨fun h => h.2.2, fun h => ⟨hh.1, hh.2, h⟩⟩
    simp only [htest, if_pos he]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  · have he' (u : PaperAESSource.maskSet out → AES.Word) :
        ¬ ((∀ i ∈ PaperAESSource.maskSet r, diffusion x i = 0) ∧ nonzeroOutside r x ∧
          (fun i : PaperAESSource.maskSet out => diffusion x i.val) = u) :=
      fun h => he ((exactZeroPattern_diffusion r x).mpr ⟨h.1, h.2.1⟩)
    simp only [if_neg he, he', if_false, mul_zero, Finset.sum_const_zero]

theorem response_energy_eq_marginal (a : AES.State) (r out : Fin 16) :
    (∑ y : MaskCoordinates out → AES.Word,
      tensorResponse (fun _ : MaskCoordinates out => residualMatrix AES.wordSuperboxKernel 0)
        (fun x i => diffusion x i.val) (fullSource a r) y ^ 2) =
      ∑ y : PaperAESSource.maskSet out → AES.Word,
        action (coordinateKernel (fun _ : PaperAESSource.maskSet out =>
          residualMatrix AES.wordSuperboxKernel 0))
          (paperJointMarginal diffusion (active a) (PaperAESSource.maskSet r)
            (PaperAESSource.maskSet out) (law a) (nonzeroOutside r)) y ^ 2 := by
  rw [marginal_action_eq_response]
  exact AESConcrete.RestrictedCoordinateChoices.tensorResponse_reindex_energy
    (PaperAESSource.maskCoordinateEquiv out)
    (fun _ : PaperAESSource.maskSet out => residualMatrix AES.wordSuperboxKernel 0)
    (fun x i => diffusion x i.val) (fullSource a r)

/-- The literal restricted response, before the unmarked normalization. -/
theorem restricted_response_energy_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (r out : Fin 16) (hr : MaskDisjoint r out)
    (hz : maskSize r ≤ (active a).card) :
    (∑ y : MaskCoordinates out → AES.Word,
      tensorResponse (fun _ : MaskCoordinates out => residualMatrix AES.wordSuperboxKernel 0)
        (fun x i => diffusion x i.val) (fullSource a r) y ^ 2) ≤
      (14 / 4294967296 : ℝ) ^ (2 * maskSize r) *
      ((17 / (15 * 4294967296) : ℝ) * (52 / (5 * 65536) : ℝ)^2) ^
        min ((active a).card - maskSize r) (maskSize out) *
      (2 / (15 * 4294967296) : ℝ) ^
        (maskSize out - min ((active a).card - maskSize r) (maskSize out)) := by
  rw [response_energy_eq_marginal]
  have hd : Disjoint (PaperAESSource.maskSet r) (PaperAESSource.maskSet out) :=
    Finset.disjoint_left.mpr (fun i hi ho => hr i
      ((PaperAESSource.mem_maskSet r i).mp hi) ((PaperAESSource.mem_maskSet out i).mp ho))
  have hop (g : AES.Word → ℝ) :
      (∑ y, action (residualMatrix AES.wordSuperboxKernel 0) g y ^ 2) ≤
        (52 / (5 * 65536) : ℝ)^2 * ∑ x, g x ^ 2 := by
    have hg := SharpWordNorm.residual_energy .ordinary .ordinary false g
    rw [AESConcrete.WordOrientationClosure.ordinary_word_kernel] at hg
    apply hg.trans
    exact mul_le_mul_of_nonneg_right (by norm_num [SharpWordNorm.rho])
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have h := paper_pointed_restricted_energy diffusion diffusion_graph_isMDS
    (active a) (PaperAESSource.maskSet r) (PaperAESSource.maskSet out) hd
    (by simpa only [PaperAESSource.maskSet_card] using hz) (law a) (nonzeroOutside r)
    AES.wordSuperboxKernel AES.word_superbox_pointed AESConcrete.AES.word_card_gt_one
    (14 / 4294967296) (17 / (15 * 4294967296)) (52 / (5 * 65536)) (by norm_num)
    (fun i _ x => law_nonneg a i x) (fun i _ => law_mass_one a i)
    (fun i hi x => law_point_le raw a i hi x) (fun i hi => law_collision_le a i hi) hop
    (fun b hb => (PaperAESSource.all_nonzero_column_energy_lt_current
      .ordinary .ordinary false b hb).le)
  simp only [PaperAESSource.maskSet_card, AESConcrete.AES.word_card_exact] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by norm_num) (by norm_num)

/-- Exact support energy with its literal nonzero-alphabet normalization. -/
theorem raw_four_round_energy_eq (a : AES.State) (r out : Fin 16)
    (hr : MaskDisjoint r out) :
    (∑ y : AES.WordState,
      action (supportProduct (0 : AES.Word) (maskBit out) (maskBit r))
        (AESPaper.GroupedLaw.groupedLaw 1 a) y ^ 2) =
      (∑ y : MaskCoordinates out → AES.Word,
        tensorResponse (fun _ : MaskCoordinates out => residualMatrix AES.wordSuperboxKernel 0)
          (fun x i => diffusion x i.val) (fullSource a r) y ^ 2) /
        (4294967295 : ℝ) ^ (4-(maskSize r+maskSize out)) := by
  rw [grouped_four_round_response]
  have hfull : fullSource a r = PaperPointedSupportResponse.exactSource r diffusion
      (AESPaper.GroupedLaw.groupedLaw 0 a) := rfl
  rw [hfull]
  simpa only [AESConcrete.AES.word_card_exact, Nat.cast_ofNat,
    show (4294967296 : ℝ)-1 = 4294967295 by norm_num] using
    PaperPointedSupportResponse.support_energy AESConcrete.AES.word_card_gt_one
      AES.wordSuperboxKernel AES.word_superbox_pointed r out hr diffusion
      (AESPaper.GroupedLaw.groupedLaw 0 a)

/-- The paper's per-position factor, before the orthogonal position count. -/
def patternBound (w z j : ℕ) : ℝ :=
  (1 / 4294967295 : ℝ) ^ (4-(z+j)) *
    ((14 / 4294967296 : ℝ) ^ (2*z) *
      ((17 / (15*4294967296) : ℝ) * (52 / (5*65536) : ℝ)^2) ^ min (w-z) j *
      (2 / (15*4294967296) : ℝ) ^ (j-min (w-z) j))

/-- Source-to-component bridge; no desired startup allowance is a premise. -/
theorem raw_four_round_energy_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (r out : Fin 16) (hr : MaskDisjoint r out)
    (hz : maskSize r ≤ (active a).card) :
    (∑ y : AES.WordState,
      action (supportProduct (0 : AES.Word) (maskBit out) (maskBit r))
        (AESPaper.GroupedLaw.groupedLaw 1 a) y ^ 2) ≤
      patternBound (active a).card (maskSize r) (maskSize out) := by
  rw [raw_four_round_energy_eq a r out hr]
  have h := div_le_div_of_nonneg_right (restricted_response_energy_le raw a r out hr hz)
    (by positivity : (0 : ℝ) ≤ 4294967295 ^ (4-(maskSize r+maskSize out)))
  simpa only [patternBound, div_eq_mul_inv, one_mul, one_div, inv_pow, mul_comm] using h


theorem fullSource_nonneg (a : AES.State) (r : Fin 16) (x : AES.WordState) :
    0 ≤ fullSource a r x := by
  unfold fullSource PaperPointedSupportResponse.exactSource
  split_ifs
  · rw [← originalLaw_eq_grouped_initial]
    exact originalLaw_nonneg (active a) (law a) (fun i _ y => law_nonneg a i y) x
  · exact le_rfl

theorem fullSource_mass (a : AES.State) (r : Fin 16) :
    (∑ x, fullSource a r x) =
      eventMass diffusion (active a) (PaperAESSource.maskSet r) (law a) (nonzeroOutside r) := by
  rw [eventMass_eq_grouped_initial]
  apply Finset.sum_congr rfl
  intro x _
  unfold fullSource PaperPointedSupportResponse.exactSource
  simp only [exactZeroPattern_diffusion]

/-- When prescribed zeros exhaust the active source, every exact-event
weight is zero. This uses source support, not merely a numerical cap. -/
theorem fullSource_zero (a : AES.State) (ha : a ≠ 0) (r : Fin 16)
    (hz : (active a).card ≤ maskSize r) : fullSource a r = 0 := by
  funext x
  have hx : fullSource a r x ≤ ∑ y, fullSource a r y :=
    PaperPointedSupportResponse.source_weight_le_mass (fullSource a r)
      (fullSource_nonneg a r) x
  rw [fullSource_mass, eventMass_zero a ha _
    (by simpa only [PaperAESSource.maskSet_card] using hz)] at hx
  exact le_antisymm hx (fullSource_nonneg a r x)

theorem raw_four_round_energy_zero (a : AES.State) (ha : a ≠ 0)
    (r out : Fin 16) (hr : MaskDisjoint r out)
    (hz : (active a).card ≤ maskSize r) :
    (∑ y : AES.WordState,
      action (supportProduct (0 : AES.Word) (maskBit out) (maskBit r))
        (AESPaper.GroupedLaw.groupedLaw 1 a) y ^ 2) = 0 := by
  rw [raw_four_round_energy_eq a r out hr, fullSource_zero a ha r hz]
  simp [tensorResponse, AESConcrete.WordColumnGram.tensorColumn]

/-- Orthogonal position sum gives exactly choose(4,t) choose(t,i).
This is the unscaled positive-residual formula for the actual law. -/
theorem component_four_round_energy_le (raw : PaperWordEntryBounds.OrdinaryBound)
    (a : AES.State) (i t : Fin 5) (hit : i.val ≤ t.val)
    (hz : 4-t.val ≤ (active a).card) :
    (∑ y : AES.WordState,
      PaperSupportProjection.component (0 : AES.Word)
        (AESPaper.GroupedLaw.groupedLaw 1 a) i.val t.val y ^ 2) ≤
      ((Nat.choose 4 t.val * Nat.choose t.val i.val : ℕ) : ℝ) *
        patternBound (active a).card (4-t.val) i.val := by
  rw [PaperSupportBlockLift.component_labels]
  rw [orthogonal_family_energy _ (fun p q hpq =>
    PaperSupportProjection.raw_orthogonal (0 : AES.Word) AESConcrete.AES.word_card_gt_one
      p.val q.val (fun he => hpq (Subtype.ext he)) _ _)]
  calc
    _ ≤ ∑ _p : PaperSupportBlockLift.BlockLabel 4 i.val t.val,
        patternBound (active a).card (4-t.val) i.val := by
      apply Finset.sum_le_sum
      intro p _
      let r := maskBitsEquiv.symm p.val.2
      let out := maskBitsEquiv.symm p.val.1
      have hr : maskBit r = p.val.2 := maskBitsEquiv.apply_symm_apply _
      have ho : maskBit out = p.val.1 := maskBitsEquiv.apply_symm_apply _
      have hd : MaskDisjoint r out := by
        intro k hk ho'
        have hv := p.property.1 k (by simpa only [ho] using ho')
        have hv' : p.val.2 k = true := by simpa only [hr] using hk
        rw [hv] at hv'
        cases hv'
      have hrc : maskSize r = 4-t.val := by
        have h := PaperSupportProfileJoin.supportCount_mask r
        rw [hr, p.property.2.2] at h
        have hl := AESConcrete.RestrictedCoordinateChoices.maskSize_le_four r
        omega
      have hoc : maskSize out = i.val := by
        have h := PaperSupportProfileJoin.residualCount_mask out
        rw [ho, p.property.2.1] at h
        exact h.symm
      have h := raw_four_round_energy_le raw a r out hd (by simpa only [hrc] using hz)
      simpa only [PaperSupportProjection.raw, hr, ho, hrc, hoc] using h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
        PaperSupportBlockLift.four_word_count, nsmul_eq_mul]

end AES8.PaperAESStartupResidual
