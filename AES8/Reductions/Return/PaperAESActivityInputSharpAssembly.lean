import AES8.Math.PaperActivityInputSharpFrame
import AES8.Math.PaperActivityInputSharpArithmetic
import AES8.Reductions.Return.PaperAESActivityInputAssembly

/-! Actual AES graph-response assembly with sharp input/output frame dimensions.
Response lengths and Boolean row-Gram counts are imported unchanged; no new AES
computation or response-cap assumption is introduced. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputSharpAssembly
open AESMixing WordActivityFrame PaperActivityInputGram
open PaperActivityInputAssembly PaperActivityInputCoordinates PaperActivityInputAnalysis
open PaperActivityInputCounts PaperActivityInputCountTransport PaperActivityInputSupportAssembly
open PaperAESActivityIdentification PaperAESActivityInputResponse PaperAESActivityInputJoin
open PaperAESActivityInputPhysical PaperAESActivityInputBounds PaperAESActivityInputAssembly
open PaperActivityInputSharpArithmetic
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
attribute [local instance] Classical.propDecidable

/-- There are four input and exactly 4-|O| output activity coordinates. -/
theorem fixed_support_energy (O : Finset (Fin 4))
    (P : (↥(Oᶜ) → Bool) → (Fin 4 → Bool) → Prop) [∀ a b, Decidable (P a b)]
    (cap : ℝ) (hcap : 0 ≤ cap) (g : ℝ) (hg : 0 ≤ g)
    (hgram : ∀ a, (∑ a', ∑ b,
      (if P a b then (1 : ℝ) else 0) * (if P a' b then (1 : ℝ) else 0)) ≤ g)
    (adjoint : Bool)
    (hw : ∀ a b, (∑ y : O → AES.Word,
      frameResponse O (truthSet (extend O a)) (truthSet b) adjoint y ^ 2) ≤
        if P a b then cap else 0)
    (c : (Fin 4 → Bool) → ℝ) :
    (∑ x : AES.WordState, action (productProjection 0 (residualMask O))
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      C^(8-O.card)*(g*cap)*∑ x, synthesize c x^2 := by
  have hO : O.card ≤ 4 := by
    simpa using Finset.card_le_card (Finset.subset_univ O)
  have hout := PaperActivityInputSharpFrame.projected_energy_le_analysis (0 : AES.Word)
    AESConcrete.AES.word_card_gt_one O (action (actualStep adjoint) (synthesize c))
  simp only [Fintype.card_coe, Finset.card_compl, Fintype.card_fin] at hout
  change _ ≤ C^(4-O.card) * _ at hout
  simp_rw [projected_step_analysis] at hout
  rw [Finset.sum_comm (s := (Finset.univ : Finset (O → AES.Word)))
    (t := (Finset.univ : Finset (↥(Oᶜ) → Bool)))] at hout
  have hb := support_energy P cap hcap g hg hgram
    (fun a b y => frameResponse O (truthSet (extend O a)) (truthSet b) adjoint y) hw c
  have hin := PaperActivityArrayFrame.frame_coefficient_energy (0 : AES.Word)
    AESConcrete.AES.word_card_gt_one c
  change (∑ b, c b^2) ≤ C^4 * ∑ x, synthesize c x^2 at hin
  have hL : 0 ≤ C^(4-O.card) := pow_nonneg C_nonneg _
  have hdim : (4-O.card)+4 = 8-O.card := by omega
  have hfactor : C^(4-O.card)*C^4 = C^(8-O.card) := by rw [← pow_add, hdim]
  calc
    _ ≤ C^(4-O.card) * ((g*cap)*∑ b, c b^2) :=
      hout.trans (mul_le_mul_of_nonneg_left hb hL)
    _ ≤ C^(4-O.card) * ((g*cap)*(C^4 * ∑ x, synthesize c x^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin (mul_nonneg hg hcap)) hL
    _ = (C^(4-O.card)*C^4)*(g*cap)*∑ x, synthesize c x^2 := by ring
    _ = _ := by rw [hfactor]

theorem degree_two_fixed_energy (O : Finset (Fin 4)) (hO : O.card = 2)
    (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x : AES.WordState, action (productProjection 0 (residualMask O))
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      C^6*(12*(tau^2/wordQ^3))*∑ x, synthesize c x^2 := by
  have hc : Fintype.card ↥(Oᶜ) = 2 := by
    simp only [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hO]
  let e : ↥(Oᶜ) ≃ Fin 2 := (Fintype.equivFin ↥(Oᶜ)).trans (finCongr hc)
  have he : C^6 = C^(8-O.card) := by rw [hO]
  rw [he]
  apply fixed_support_energy O supportedTwo (tau^2/wordQ^3)
    (by norm_num [tau,wordQ]) 12 (by norm_num) (two_gram e) adjoint _ c
  intro a b
  have h := degree_two_response_energy O (truthSet (extend O a)) (truthSet b) hO adjoint
  rw [totalWeight_frames] at h
  unfold supportedTwo
  by_cases hp : weightOn a + weight b = 3 <;> simpa [hp] using h

theorem degree_three_fixed_energy (O : Finset (Fin 4)) (hO : O.card = 3)
    (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x : AES.WordState, action (productProjection 0 (residualMask O))
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      C^5*(16*(tau^2*beta/wordQ^2))*∑ x, synthesize c x^2 := by
  have hc : Fintype.card ↥(Oᶜ) = 1 := by
    simp only [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hO]
  let e : ↥(Oᶜ) ≃ Fin 1 := (Fintype.equivFin ↥(Oᶜ)).trans (finCongr hc)
  have he : C^5 = C^(8-O.card) := by rw [hO]
  rw [he]
  apply fixed_support_energy O supportedThree (tau^2*beta/wordQ^2)
    (by norm_num [tau,beta,wordQ]) 16 (by norm_num) (fun a => (three_gram e a).le) adjoint _ c
  intro a b
  have h := degree_three_response_energy O (truthSet (extend O a)) (truthSet b) hO adjoint
  rw [totalWeight_frames] at h
  unfold supportedThree
  by_cases hp : weightOn a + weight b = 2 ∨ weightOn a + weight b = 3 <;>
    simpa [hp] using h

theorem degree_four_fixed_energy (O : Finset (Fin 4)) (hO : O.card = 4)
    (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x : AES.WordState, action (productProjection 0 (residualMask O))
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      C^4*(8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)*∑ x, synthesize c x^2 := by
  have hc : Fintype.card ↥(Oᶜ) = 0 := by
    simp only [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hO]
  have ha (a : ↥(Oᶜ) → Bool) : weightOn a = 0 := by
    have h : weightOn a ≤ Fintype.card ↥(Oᶜ) := by
      simpa only [weightOn,Finset.card_univ] using
        Finset.card_le_card (Finset.filter_subset (fun j : ↥(Oᶜ) => a j = true) Finset.univ)
    omega
  have hrows : Fintype.card (↥(Oᶜ) → Bool) = 1 := by rw [Fintype.card_fun,hc,pow_zero]
  have hcap (b : Fin 4 → Bool) : 0 ≤ fourCap b := by
    unfold fourCap tau beta wordQ
    positivity
  have hw (a : ↥(Oᶜ) → Bool) (b : Fin 4 → Bool) :
      (∑ y : O → AES.Word,
        frameResponse O (truthSet (extend O a)) (truthSet b) adjoint y ^ 2) ≤ fourCap b := by
    have h := degree_four_response_energy O (truthSet (extend O a)) (truthSet b) hO adjoint
    simpa only [totalWeight_frames,ha,zero_add,fourCap] using h
  have hout := PaperActivityInputSharpFrame.projected_energy_le_analysis (0 : AES.Word)
    AESConcrete.AES.word_card_gt_one O
    (action (actualStep adjoint) (synthesize c))
  simp only [hc, pow_zero, one_mul] at hout
  simp_rw [projected_step_analysis] at hout
  rw [Finset.sum_comm (s := (Finset.univ : Finset (O → AES.Word)))
    (t := (Finset.univ : Finset (↥(Oᶜ) → Bool)))] at hout
  have hb := single_row_energy hrows fourCap hcap
    (fun a b y => frameResponse O (truthSet (extend O a)) (truthSet b) adjoint y) hw c
  rw [fourCap_sum] at hb
  have hin := PaperActivityArrayFrame.frame_coefficient_energy (0 : AES.Word)
    AESConcrete.AES.word_card_gt_one c
  change (∑ b, c b^2) ≤ C^4 * ∑ x, synthesize c x^2 at hin
  have hL : 0 ≤ C^4 := pow_nonneg C_nonneg _
  have hpos : 0 ≤ 8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2 := by
    norm_num [tau,beta,wordQ]
  calc
    _ ≤ (8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)*∑ b, c b^2 := hout.trans hb
    _ ≤ (8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)*
      (C^4 * ∑ x, synthesize c x^2) :=
      mul_le_mul_of_nonneg_left hin hpos
    _ = _ := by ring

end AES8.PaperAESActivityInputSharpAssembly
