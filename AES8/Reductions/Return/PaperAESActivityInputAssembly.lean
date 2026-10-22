import AES8.Reductions.Return.PaperAESActivityInputBounds
import AES8.Reductions.Return.PaperAESActivityInputPhysical
import AES8.Math.PaperActivityInputCountTransport
import AES8.Math.PaperActivityInputSupportAssembly

/-! Fixed-position activity-input energy for the actual grouped AES step.
Arbitrary signed frame coefficients are composed before any degree aggregation. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperAESActivityInputAssembly
open AESMixing WordActivityFrame PaperActivityInputGram PaperActivityInputArithmetic
open PaperActivityInputAssembly PaperActivityInputCoordinates PaperActivityInputAnalysis
open PaperActivityInputCounts PaperActivityInputCountTransport PaperActivityInputSupportAssembly
open PaperAESActivityIdentification PaperAESActivityInputResponse PaperAESActivityInputJoin
open PaperAESActivityInputPhysical PaperAESActivityInputBounds
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2500000
attribute [local instance] Classical.propDecidable

theorem truthSet_card (b : Fin 4 → Bool) : (truthSet b).card = weight b := rfl

theorem outside_card (O : Finset (Fin 4)) (a : ↥(Oᶜ) → Bool) :
    (truthSet (extend O a) \ O).card = weightOn a := by
  symm
  unfold weightOn
  apply Finset.card_bij (fun (j : ↥(Oᶜ)) _ => j.val)
  · intro j hj
    have ht : a j = true := (Finset.mem_filter.mp hj).2
    simp [truthSet,extend,Finset.mem_compl.mp j.property,ht]
  · intro j _ k _ h
    exact Subtype.ext h
  · intro k hk
    have hko : k ∉ O := (Finset.mem_sdiff.mp hk).2
    refine ⟨⟨k,Finset.mem_compl.mpr hko⟩,?_,rfl⟩
    simpa [truthSet,extend,hko] using (Finset.mem_sdiff.mp hk).1

theorem totalWeight_frames (O : Finset (Fin 4)) (a : ↥(Oᶜ) → Bool)
    (b : Fin 4 → Bool) :
    totalWeight O (truthSet (extend O a)) (truthSet b) = weightOn a + weight b := by
  rw [totalWeight,truthSet_card,outside_card,Nat.add_comm]

/-- Both frame losses are derived, while the response premise concerns the
literal graph response attached to each actual Boolean frame assignment. -/
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
      loss^2*(g*cap)*∑ x, synthesize c x^2 := by
  have hO : Fintype.card ↥(Oᶜ) ≤ 6 := by
    simp only [Fintype.card_coe,Finset.card_compl,Fintype.card_fin]
    omega
  have hI : Fintype.card (Fin 4) ≤ 6 := by simp
  have hout := projected_energy_le_analysis O hO (action (actualStep adjoint) (synthesize c))
  simp_rw [projected_step_analysis] at hout
  rw [Finset.sum_comm (s := (Finset.univ : Finset (O → AES.Word)))
    (t := (Finset.univ : Finset (↥(Oᶜ) → Bool)))] at hout
  have hb := support_energy P cap hcap g hg hgram
    (fun a b y => frameResponse O (truthSet (extend O a)) (truthSet b) adjoint y) hw c
  have hin := word_frame_coefficients hI c
  change (∑ b, c b^2) ≤ loss * ∑ x, synthesize c x^2 at hin
  have hL : 0 ≤ loss := by norm_num [loss]
  calc
    _ ≤ loss * ((g*cap)*∑ b, c b^2) := hout.trans (mul_le_mul_of_nonneg_left hb hL)
    _ ≤ loss * ((g*cap)*(loss * ∑ x, synthesize c x^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin (mul_nonneg hg hcap)) hL
    _ = _ := by ring

theorem degree_two_fixed_energy (O : Finset (Fin 4)) (hO : O.card = 2)
    (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x : AES.WordState, action (productProjection 0 (residualMask O))
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      loss^2*(12*(tau^2/wordQ^3))*∑ x, synthesize c x^2 := by
  have hc : Fintype.card ↥(Oᶜ) = 2 := by
    simp only [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hO]
  let e : ↥(Oᶜ) ≃ Fin 2 := (Fintype.equivFin ↥(Oᶜ)).trans (finCongr hc)
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
      loss^2*(16*(tau^2*beta/wordQ^2))*∑ x, synthesize c x^2 := by
  have hc : Fintype.card ↥(Oᶜ) = 1 := by
    simp only [Fintype.card_coe,Finset.card_compl,Fintype.card_fin,hO]
  let e : ↥(Oᶜ) ≃ Fin 1 := (Fintype.equivFin ↥(Oᶜ)).trans (finCongr hc)
  apply fixed_support_energy O supportedThree (tau^2*beta/wordQ^2)
    (by norm_num [tau,beta,wordQ]) 16 (by norm_num) (fun a => (three_gram e a).le) adjoint _ c
  intro a b
  have h := degree_three_response_energy O (truthSet (extend O a)) (truthSet b) hO adjoint
  rw [totalWeight_frames] at h
  unfold supportedThree
  by_cases hp : weightOn a + weight b = 2 ∨ weightOn a + weight b = 3 <;>
    simpa [hp] using h

/-- No one-residual response survives the actual shortening branches. -/
theorem degree_one_fixed_energy (O : Finset (Fin 4)) (hO : O.card = 1)
    (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x : AES.WordState, action (productProjection 0 (residualMask O))
      (action (actualStep adjoint) (synthesize c)) x ^ 2) = 0 := by
  have hcard : Fintype.card ↥(Oᶜ) ≤ 6 := by
    simp only [Fintype.card_coe,Finset.card_compl,Fintype.card_fin]
    omega
  have h := projected_energy_le_analysis O hcard (action (actualStep adjoint) (synthesize c))
  simp_rw [projected_step_analysis,degree_one_response O _ _ hO adjoint] at h
  norm_num at h
  exact le_antisymm h (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

def fourCap (b : Fin 4 → Bool) : ℝ :=
  (if weight b = 1 ∨ weight b = 3 then tau^2*beta^2/wordQ else 0) +
  (if weight b = 2 then tau^4/wordQ^2 else 0)

theorem weighted_choices (P : (Fin 4 → Bool) → Prop) [DecidablePred P] (v : ℝ) :
    (∑ b, if P b then v else 0) = ((∑ b, if P b then 1 else 0 : ℕ) : ℝ)*v := by
  rw [Nat.cast_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hp : P b <;> simp [hp]

theorem fourCap_sum :
    (∑ b : Fin 4 → Bool, fourCap b) =
      8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2 := by
  simp only [fourCap,Finset.sum_add_distrib]
  rw [weighted_choices,weighted_choices,line_choices,plane_choices]
  norm_num
  ring

theorem degree_four_fixed_energy (O : Finset (Fin 4)) (hO : O.card = 4)
    (adjoint : Bool) (c : (Fin 4 → Bool) → ℝ) :
    (∑ x : AES.WordState, action (productProjection 0 (residualMask O))
      (action (actualStep adjoint) (synthesize c)) x ^ 2) ≤
      loss^2*(8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)*∑ x, synthesize c x^2 := by
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
  have hout := projected_energy_le_analysis O (by omega : Fintype.card ↥(Oᶜ) ≤ 6)
    (action (actualStep adjoint) (synthesize c))
  simp_rw [projected_step_analysis] at hout
  rw [Finset.sum_comm (s := (Finset.univ : Finset (O → AES.Word)))
    (t := (Finset.univ : Finset (↥(Oᶜ) → Bool)))] at hout
  have hb := single_row_energy hrows fourCap hcap
    (fun a b y => frameResponse O (truthSet (extend O a)) (truthSet b) adjoint y) hw c
  rw [fourCap_sum] at hb
  have hin := word_frame_coefficients (by simp : Fintype.card (Fin 4) ≤ 6) c
  change (∑ b, c b^2) ≤ loss * ∑ x, synthesize c x^2 at hin
  have hL : 0 ≤ loss := by norm_num [loss]
  have hpos : 0 ≤ 8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2 := by
    norm_num [tau,beta,wordQ]
  calc
    _ ≤ loss * ((8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)*∑ b, c b^2) :=
      hout.trans (mul_le_mul_of_nonneg_left hb hL)
    _ ≤ loss * ((8*tau^2*beta^2/wordQ + 6*tau^4/wordQ^2)*
      (loss * ∑ x, synthesize c x^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hin hpos) hL
    _ = _ := by ring

end AES8.PaperAESActivityInputAssembly
