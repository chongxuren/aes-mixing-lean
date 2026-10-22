import AES8.Math.PaperInversionCounts
import AESMixing.AffineChannel

/-! Even-degree inversion histograms, obtained from exact trace-kernel counts.
Histograms are expressed as full-field filters with zero excluded, so the
statements directly describe every row and column of the nonzero block. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperInversionHistogram
open AESMixing PaperFieldTrace
set_option autoImplicit false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
  [Algebra (ZMod 2) F]

omit [DecidableEq F] [CharP F 2] in
theorem field_card : Fintype.card F=2^Module.finrank (ZMod 2) F := by
  simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := F))

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem trace_one : trace (1 : F)=(Module.finrank (ZMod 2) F : ZMod 2) := by
  simpa [trace] using (Algebra.trace_algebraMap (R := ZMod 2) (S := F) 1)

omit [Fintype F] [DecidableEq F] [CharP F 2] in
theorem trace_one_even (h : Even (Module.finrank (ZMod 2) F)) : trace (1 : F)=0 := by
  rw [trace_one, CharTwo.natCast_eq_ite, if_pos h]

theorem trace_zero_card_twice :
    (Finset.univ.filter (fun x : F => trace x=0)).card*2=Fintype.card F := by
  have ht := (PaperArtinSchreier.traceHom (F := F)).ker.card_mul_index
  rw [AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr PaperArtinSchreier.trace_surjective] at ht
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype,
    AddMonoidHom.mem_ker, PaperArtinSchreier.traceHom, trace] using ht

theorem trace_zero_card :
    (Finset.univ.filter (fun x : F => trace x=0)).card=Fintype.card F/2 := by
  have h := trace_zero_card_twice (F := F)
  omega

def law (c : F) : ℕ := (if trace c⁻¹=0 then 2 else 0)+(if c=1 then 2 else 0)

theorem law_four_iff (he : Even (Module.finrank (ZMod 2) F)) (c : F) :
    (c ≠ 0 ∧ law c=4) ↔ c=1 := by
  by_cases hc : c=1
  · subst c; simp [law, trace_one_even he]
  · by_cases ht : trace c⁻¹=0 <;> simp [law, hc, ht]

theorem law_two_iff (he : Even (Module.finrank (ZMod 2) F)) (c : F) :
    (c ≠ 0 ∧ law c=2) ↔ c ≠ 0 ∧ c ≠ 1 ∧ trace c⁻¹=0 := by
  by_cases hc : c=1
  · subst c; simp [law, trace_one_even he]
  · by_cases ht : trace c⁻¹=0 <;> simp [law, hc, ht]

theorem law_zero_iff (he : Even (Module.finrank (ZMod 2) F)) (c : F) :
    (c ≠ 0 ∧ law c=0) ↔ trace c⁻¹ ≠ 0 := by
  by_cases hc0 : c=0
  · subst c; simp [law, trace_zero]
  by_cases hc1 : c=1
  · subst c; simp [law, trace_one_even he]
  · by_cases ht : trace c⁻¹=0 <;> simp [law, hc0, hc1, ht]

theorem law_four_card (he : Even (Module.finrank (ZMod 2) F)) :
    (Finset.univ.filter (fun c : F => c ≠ 0 ∧ law c=4)).card=1 := by
  simp_rw [law_four_iff he]
  rw [Finset.filter_eq']
  simp

theorem law_two_card (he : Even (Module.finrank (ZMod 2) F)) :
    (Finset.univ.filter (fun c : F => c ≠ 0 ∧ law c=2)).card=Fintype.card F/2-2 := by
  simp_rw [law_two_iff he]
  let s := Finset.univ.filter (fun c : F => trace c=0)
  have hc : (Finset.univ.filter (fun c : F => c ≠ 0 ∧ c ≠ 1 ∧ trace c⁻¹=0)).card =
      ((s.erase 0).erase 1).card := by
    apply Finset.card_bijective (fun c : F => c⁻¹) inv_involutive.bijective
    intro c
    simp [s, and_left_comm]
  have h0 : (0 : F) ∈ s := by simp [s, trace_zero]
  have h1 : (1 : F) ∈ s.erase 0 := by simp [s, one_ne_zero, trace_one_even he]
  rw [hc, Finset.card_erase_of_mem h1, Finset.card_erase_of_mem h0,
    show s.card=Fintype.card F/2 from trace_zero_card]
  omega

theorem law_zero_card (he : Even (Module.finrank (ZMod 2) F)) :
    (Finset.univ.filter (fun c : F => c ≠ 0 ∧ law c=0)).card=Fintype.card F/2 := by
  simp_rw [law_zero_iff he]
  have hc : (Finset.univ.filter (fun c : F => trace c⁻¹ ≠ 0)).card =
      (Finset.univ.filter (fun c : F => trace c ≠ 0)).card := by
    apply Finset.card_bijective (fun c : F => c⁻¹) inv_involutive.bijective
    intro c
    simp
  rw [hc]
  have ht : (Finset.univ.filter (fun c : F => trace c=0)).card+
      (Finset.univ.filter (fun c : F => trace c ≠ 0)).card=Fintype.card F := by
    simpa only [Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun c : F => trace c=0))
  have hz : (Finset.univ.filter (fun c : F => trace c=0)).card=Fintype.card F/2 :=
    trace_zero_card
  have hz2 : (Finset.univ.filter (fun c : F => trace c=0)).card*2=Fintype.card F :=
    trace_zero_card_twice
  omega

def count (a b : F) : ℕ :=
  (Finset.univ.filter (fun x : F => difference invPermutation a x=b)).card

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem count_scale (a b : F) (ha : a ≠ 0) : count a b=count 1 (a*b) := by
  unfold count
  rw [Finset.card_filter, Finset.card_filter]
  have he := Equiv.sum_comp (Equiv.mulLeft₀ a ha)
    (fun x => if difference invPermutation a x=b then (1 : ℕ) else 0)
  change (∑ t, if difference invPermutation a (a*t)=b then (1 : ℕ) else 0)=_ at he
  rw [← he]
  simp_rw [inversion_difference_eq a b _ ha]

theorem count_law (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) : count a b=law (a*b) := by
  rw [count_scale a b ha]
  exact PaperInversionCounts.count_one (a*b) (mul_ne_zero ha hb)

theorem column_law_card (a : F) (ha : a ≠ 0) (k : ℕ) :
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧ count a b=k)).card=
      (Finset.univ.filter (fun c : F => c ≠ 0 ∧ law c=k)).card := by
  apply Finset.card_bijective (fun b => a*b) (Equiv.mulLeft₀ a ha).bijective
  intro b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hb : b=0
  · simp [hb]
  · simp [hb, mul_ne_zero ha hb, count_law a b ha hb]

theorem row_law_card (b : F) (hb : b ≠ 0) (k : ℕ) :
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧ count a b=k)).card=
      (Finset.univ.filter (fun c : F => c ≠ 0 ∧ law c=k)).card := by
  apply Finset.card_bijective (fun a => a*b) (Equiv.mulRight₀ b hb).bijective
  intro a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : a=0
  · simp [ha]
  · simp [ha, mul_ne_zero ha hb, count_law a b ha hb]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem channel_eq_iff_count (a b : F) (k : ℕ) :
    differenceChannel invPermutation b a=(k : ℝ)/(Fintype.card F : ℝ) ↔ count a b=k := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  change ((∑ x : F, if difference invPermutation a x=b then (1 : ℝ) else 0) /
    (Fintype.card F : ℝ)=(k : ℝ)/(Fintype.card F : ℝ)) ↔ _
  rw [Finset.sum_boole, div_left_inj' hq]
  exact Nat.cast_inj

/-- Literal nonzero-column histogram in even field degree. -/
theorem column (he : Even (Module.finrank (ZMod 2) F)) (a : F) (ha : a ≠ 0) :
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel invPermutation b a=4/(Fintype.card F : ℝ))).card=1 ∧
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel invPermutation b a=2/(Fintype.card F : ℝ))).card=Fintype.card F/2-2 ∧
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel invPermutation b a=0)).card=Fintype.card F/2 := by
  have hfour := column_law_card a ha 4
  have htwo := column_law_card a ha 2
  have hzero := column_law_card a ha 0
  simp_rw [← channel_eq_iff_count] at hfour htwo hzero
  simpa using And.intro (hfour.trans (law_four_card he))
    (And.intro (htwo.trans (law_two_card he)) (hzero.trans (law_zero_card he)))

/-- Literal nonzero-row histogram in even field degree. -/
theorem row (he : Even (Module.finrank (ZMod 2) F)) (b : F) (hb : b ≠ 0) :
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel invPermutation b a=4/(Fintype.card F : ℝ))).card=1 ∧
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel invPermutation b a=2/(Fintype.card F : ℝ))).card=Fintype.card F/2-2 ∧
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel invPermutation b a=0)).card=Fintype.card F/2 := by
  have hfour := row_law_card b hb 4
  have htwo := row_law_card b hb 2
  have hzero := row_law_card b hb 0
  simp_rw [← channel_eq_iff_count] at hfour htwo hzero
  simpa using And.intro (hfour.trans (law_four_card he))
    (And.intro (htwo.trans (law_two_card he)) (hzero.trans (law_zero_card he)))

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem affine_column_count (A : F ≃+ F) (c a : F) (r : ℝ) :
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=r)).card=
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel invPermutation b a=r)).card := by
  apply Finset.card_bijective A.symm A.symm.bijective
  intro b
  have hb : A.symm b=0 ↔ b=0 := by
    constructor
    · intro h
      have h' := congrArg A h
      simpa using h'
    · intro h; simp [h]
  simp [affineOutput_channel, hb]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem affine_row_count (A : F ≃+ F) (c b : F) (r : ℝ) :
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=r)).card=
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel invPermutation (A.symm b) a=r)).card := by
  simp only [affineOutput_channel]

theorem affine_column (he : Even (Module.finrank (ZMod 2) F))
    (A : F ≃+ F) (c a : F) (ha : a ≠ 0) :
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=4/(Fintype.card F : ℝ))).card=1 ∧
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=2/(Fintype.card F : ℝ))).card=Fintype.card F/2-2 ∧
    (Finset.univ.filter (fun b : F => b ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=0)).card=Fintype.card F/2 := by
  simp_rw [affine_column_count]
  exact column he a ha

theorem affine_row (he : Even (Module.finrank (ZMod 2) F))
    (A : F ≃+ F) (c b : F) (hb : b ≠ 0) :
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=4/(Fintype.card F : ℝ))).card=1 ∧
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=2/(Fintype.card F : ℝ))).card=Fintype.card F/2-2 ∧
    (Finset.univ.filter (fun a : F => a ≠ 0 ∧
      differenceChannel (affineOutput invPermutation A c) b a=0)).card=Fintype.card F/2 := by
  have hb' : A.symm b ≠ 0 := by
    intro h
    apply hb
    have h' := congrArg A h
    simpa using h'
  simp_rw [affine_row_count]
  exact row he (A.symm b) hb'

end AES8.PaperInversionHistogram
