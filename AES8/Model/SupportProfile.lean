/- Module role: Concrete AES support definitions and coordinate/projection interfaces.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Model.Profile
import AESPaper.GroupedLaw
import AESMixing.SupportOrthogonality
import AESMixing.L2Sums

/-!
# The actual fourteen-coordinate support profile

Each coordinate is the counting-measure norm of an orthogonal projection of
the actual grouped error.  Two four-bit masks specify the residual positions
and inactive positions.  Overlapping masks give the zero projection.  Grouping
the remaining projections by residual degree and active support size produces
the paper's triangular fifteen-coordinate family; the zero-state coordinate
vanishes for a zero-extended error, leaving the fourteen coordinates in `Data`.

This module supplies projection identities only.  It does not assume or assert
an AES initialization, transfer estimate, or mixing bound.  Constructive proof
work only; no predecessor sources or manuscripts are modified.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

noncomputable section
open scoped BigOperators

namespace AES8.SupportProfile
open AESMixing AESMixing.AES

abbrev State := AESMixing.AES.WordState
abbrev Label := Fin 16 × Fin 16

def Valid (p : Label) : Prop :=
  ∀ k : Fin 4, maskBit p.1 k = true → maskBit p.2 k = false

instance (p : Label) : Decidable (Valid p) := inferInstanceAs
  (Decidable (∀ k : Fin 4, maskBit p.1 k = true → maskBit p.2 k = false))

/-- Number of nonzero 32-bit words, not number of nonzero bytes. -/
def activeCount (x : State) : ℕ :=
  (Finset.univ.filter (fun i : Fin 4 => x i ≠ 0)).card

def supportSize : Fin 14 → ℕ := ![1,2,3,4,1,2,3,4,2,3,4,3,4,4]
def residualDegree : Fin 14 → ℕ := ![0,0,0,0,1,1,1,1,2,2,2,3,3,4]

private def offset (i : ℕ) : ℕ :=
  if i = 0 then 0 else if i = 1 then 4 else if i = 2 then 7 else
    if i = 3 then 9 else 10

/-- Index zero is `(0,0)`; successors have exactly the order in `Data`. -/
def coord (p : Label) : Fin 15 :=
  if maskSize p.1 ≤ 4 - maskSize p.2 then
    Fin.ofNat 15 (offset (maskSize p.1) + (4 - maskSize p.2)) else 0

def raw (p : Label) (f : State → ℝ) : State → ℝ :=
  action (supportProduct (0 : AES.Word) (maskBit p.1) (maskBit p.2)) f

def fullComponent (f : State → ℝ) (c : Fin 15) : State → ℝ :=
  groupedFamily coord (fun p => raw p f) c

def component (f : State → ℝ) (c : Fin 14) : State → ℝ :=
  fullComponent f c.succ

def profile (f : State → ℝ) : AES8.Profile := fun c => l2 (component f c)

def actual (a : AES.State) (j : ℕ) : AES8.Profile :=
  profile (AESPaper.GroupedLaw.error (j + 1) a)

theorem profile_nonneg (f : State → ℝ) (c : Fin 14) : 0 ≤ profile f c :=
  l2_nonneg _

theorem actual_nonneg (a : AES.State) (j : ℕ) (c : Fin 14) :
    0 ≤ actual a j c := profile_nonneg _ _

theorem word_card_gt_one : 1 < Fintype.card AES.Word := by
  rw [AES.word_card]
  norm_num

theorem raw_invalid (p : Label) (hp : ¬ Valid p) (f : State → ℝ) : raw p f = 0 := by
  unfold Valid at hp
  push Not at hp
  obtain ⟨k, hk, hi⟩ := hp
  have hi' : maskBit p.2 k = true := by
    cases he : maskBit p.2 k <;> simp_all
  funext y
  unfold raw action
  apply Finset.sum_eq_zero
  intro x _
  have hz : supportProduct (0 : AES.Word) (maskBit p.1) (maskBit p.2) y x = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [supportPiece, hk, hi']
  rw [hz, zero_mul]

theorem raw_orthogonal (p q : Label) (hpq : p ≠ q) (f g : State → ℝ) :
    (∑ x, raw p f x * raw q g x) = 0 := by
  apply supportProduct_mixed_orthogonal (0 : AES.Word) word_card_gt_one
  rintro ⟨hm, hi⟩
  apply hpq
  exact Prod.ext (maskBits_injective hm) (maskBits_injective hi)

theorem raw_decomposition (f : State → ℝ) (x : State) :
    (∑ p : Label, raw p f x) = f x := by
  rw [Fintype.sum_prod_type]
  have h (m : Fin 16) : (∑ n : Fin 16, raw (m,n) f x) =
      action (productProjection (0 : AES.Word) (maskBit m)) f x := by
    have hd := congrFun (supportProduct_decomposition (0 : AES.Word) (maskBit m) f) x
    rw [← maskBitsEquiv.sum_comp] at hd
    exact hd
  simp_rw [h]
  exact (maskBitsEquiv.sum_comp
    (fun a => action (productProjection (0 : AES.Word) a) f x)).trans
      (congrFun (productProjection_decomposition (0 : AES.Word) f) x)

theorem fullComponent_decomposition (f : State → ℝ) (x : State) :
    (∑ c : Fin 15, fullComponent f c x) = f x := by
  unfold fullComponent
  rw [groupedFamily_sum]
  exact raw_decomposition f x

theorem fullComponent_orthogonal (f g : State → ℝ) (i j : Fin 15) (hij : i ≠ j) :
    (∑ x, fullComponent f i x * fullComponent g j x) = 0 := by
  unfold fullComponent groupedFamily
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hp : coord p = i
  · by_cases hq : coord q = j
    · have hpq : p ≠ q := by
        intro he
        subst q
        exact hij (hp.symm.trans hq)
      simpa only [hp, hq, if_true] using raw_orthogonal p q hpq f g
    · simp [hq]
  · simp [hp]

theorem component_orthogonal (f g : State → ℝ) (i j : Fin 14) (hij : i ≠ j) :
    (∑ x, component f i x * component g j x) = 0 := by
  exact fullComponent_orthogonal f g i.succ j.succ
    (fun h => hij (Fin.ext (Nat.succ.inj (congrArg Fin.val h))))

private theorem supportPiece_row_zero (marked inactive : Bool) (y x : AES.Word)
    (h : inactive ≠ decide (y = 0)) :
    supportPiece 0 marked inactive y x = 0 := by
  cases marked <;> cases inactive <;> by_cases hy : y = 0 <;>
    simp_all [supportPiece, constantMatrix, zeroMatrix, activityMatrix, identityKernel,
      residualProjection_zero_row]

private theorem inactive_complement_card : ∀ m : Fin 16,
    (Finset.univ.filter (fun i : Fin 4 => maskBit m i = false)).card = 4 - maskSize m := by
  decide

theorem raw_supported (p : Label) (f : State → ℝ) (x : State)
    (hx : activeCount x ≠ 4 - maskSize p.2) : raw p f x = 0 := by
  have hm : ∃ k : Fin 4, maskBit p.2 k ≠ decide (x k = 0) := by
    by_contra h
    push Not at h
    apply hx
    unfold activeCount
    have he : (Finset.univ.filter (fun k : Fin 4 => x k ≠ 0)) =
        Finset.univ.filter (fun k : Fin 4 => maskBit p.2 k = false) := by
      ext k
      simp [h k]
    rw [he]
    exact inactive_complement_card p.2
  obtain ⟨k,hk⟩ := hm
  unfold raw action
  apply Finset.sum_eq_zero
  intro y _
  have hz : supportProduct (0 : AES.Word) (maskBit p.1) (maskBit p.2) x y = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ k) (supportPiece_row_zero _ _ _ _ hk)
  rw [hz, zero_mul]

private theorem coord_support : ∀ (p : Label) (c : Fin 14), Valid p →
    coord p = c.succ → 4 - maskSize p.2 = supportSize c := by decide

theorem coord_type : ∀ (p : Label) (c : Fin 14), Valid p →
    (coord p = c.succ ↔
      maskSize p.1 = residualDegree c ∧ 4 - maskSize p.2 = supportSize c) := by decide

/-- The coordinate names record the residual count and exact active support. -/
theorem component_eq_support_residual (f : State → ℝ) (c : Fin 14) (x : State) :
    component f c x = ∑ p : Label,
      if maskSize p.1 = residualDegree c ∧ 4 - maskSize p.2 = supportSize c
        then raw p f x else 0 := by
  unfold component fullComponent groupedFamily
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : Valid p
  · simp only [coord_type p c hp]
  · simp [raw_invalid p hp f]

private theorem coord_zero_support : ∀ p : Label, Valid p → coord p = 0 →
    4 - maskSize p.2 = 0 := by decide

theorem component_supported (f : State → ℝ) (c : Fin 14) (x : State)
    (hx : activeCount x ≠ supportSize c) : component f c x = 0 := by
  unfold component fullComponent groupedFamily
  apply Finset.sum_eq_zero
  intro p _
  by_cases hp : Valid p
  · by_cases hc : coord p = c.succ
    · rw [if_pos hc]
      exact raw_supported p f x (by simpa [coord_support p c hp hc] using hx)
    · simp [hc]
  · simp [raw_invalid p hp f]

theorem activeCount_zero_iff (x : State) : activeCount x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    change x i = 0
    have he : (Finset.univ.filter (fun k : Fin 4 => x k ≠ 0)) = ∅ :=
      Finset.card_eq_zero.mp h
    by_contra hi
    have hm : i ∈ Finset.univ.filter (fun k : Fin 4 => x k ≠ 0) := by simp [hi]
    rw [he] at hm
    simpa using hm
  · rintro rfl
    simp [activeCount]

theorem supportSize_pos (c : Fin 14) : 0 < supportSize c := by
  fin_cases c <;> decide

theorem component_at_zero (f : State → ℝ) (c : Fin 14) : component f c 0 = 0 := by
  apply component_supported
  rw [(activeCount_zero_iff (0 : State)).mpr rfl]
  exact ne_of_lt (supportSize_pos c)

theorem fullComponent_zero (f : State → ℝ) (hf : f 0 = 0) : fullComponent f 0 = 0 := by
  funext x
  by_cases hx : x = 0
  · subst x
    have h := fullComponent_decomposition f 0
    rw [Fin.sum_univ_succ] at h
    have hz : (∑ c : Fin 14, fullComponent f c.succ 0) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      exact component_at_zero f c
    rw [hz, add_zero, hf] at h
    exact h
  · unfold fullComponent groupedFamily
    apply Finset.sum_eq_zero
    intro p _
    by_cases hp : Valid p
    · by_cases hc : coord p = 0
      · rw [if_pos hc]
        apply raw_supported
        rw [coord_zero_support p hp hc]
        exact fun h => hx ((activeCount_zero_iff x).mp h)
      · simp [hc]
    · simp [raw_invalid p hp f]

theorem component_decomposition (f : State → ℝ) (hf : f 0 = 0) (x : State) :
    (∑ c : Fin 14, component f c x) = f x := by
  have h := fullComponent_decomposition f x
  rw [Fin.sum_univ_succ, fullComponent_zero f hf] at h
  simpa [component] using h

theorem profile_energy (f : State → ℝ) (hf : f 0 = 0) :
    (∑ c : Fin 14, profile f c ^ 2) = ∑ x, f x ^ 2 := by
  have he := orthogonal_family_energy (fun c => component f c)
    (fun i j hij => component_orthogonal f f i j hij)
  simpa only [profile, l2_sq, component_decomposition f hf] using he.symm

def activity (f : State → ℝ) : State → ℝ :=
  action (productProjection (0 : AES.Word) (fun _ : Fin 4 => false)) f

private theorem coord_activity : ∀ p : Label, Valid p →
    ((coord p).val < 5 ↔ p.1 = 0) := by decide

private theorem activity_selector (p : Label) (hp : Valid p) (v : ℝ) :
    (∑ c : Fin 5, if coord p = Fin.castAdd 10 c then v else 0) =
      if p.1 = 0 then v else 0 := by
  by_cases hz : p.1 = 0
  · rw [if_pos hz]
    have hc : (coord p).val < 5 := (coord_activity p hp).mpr hz
    let c : Fin 5 := ⟨(coord p).val, hc⟩
    have he : coord p = Fin.castAdd 10 c := Fin.ext rfl
    rw [Finset.sum_eq_single c]
    · simp [he]
    · intro b _ hbc
      have hb : coord p ≠ Fin.castAdd 10 b := by
        intro h
        apply hbc
        apply Fin.ext
        have hv := congrArg (fun a : Fin 15 => a.val) (h.symm.trans he)
        exact hv
      simp [hb]
    · simp
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro c _
    have hc : coord p ≠ Fin.castAdd 10 c := by
      intro he
      apply hz
      apply (coord_activity p hp).mp
      rw [he]
      exact c.isLt
    simp [hc]

theorem activity_decomposition (f : State → ℝ) (hf : f 0 = 0) (x : State) :
    activity f x = ∑ c : Fin 4, component f (Fin.castAdd 10 c) x := by
  have hgroup : (∑ c : Fin 5, fullComponent f (Fin.castAdd 10 c) x) =
      ∑ p : Label, if p.1 = 0 then raw p f x else 0 := by
    unfold fullComponent groupedFamily
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : Valid p
    · exact activity_selector p hp (raw p f x)
    · simp [raw_invalid p hp f]
  have hsum : (∑ p : Label, if p.1 = 0 then raw p f x else 0) = activity f x := by
    rw [Fintype.sum_prod_type]
    change (∑ m : Fin 16, ∑ n : Fin 16, if m = 0 then raw (m,n) f x else 0) = _
    have ho : (∑ m : Fin 16, ∑ n : Fin 16, if m = 0 then raw (m,n) f x else 0) =
        ∑ n : Fin 16, raw (0,n) f x := by
      rw [Finset.sum_eq_single (0 : Fin 16)]
      · simp only [if_true]
      · intro b _ hb
        simp only [hb, if_false, Finset.sum_const_zero]
      · simp
    rw [ho]
    change (∑ n : Fin 16, action (supportProduct (0 : AES.Word)
      (maskBit 0) (maskBit n)) f x) = _
    have hm : maskBit 0 = (fun _ : Fin 4 => false) := by decide
    rw [hm]
    exact (maskBitsEquiv.sum_comp (fun b => action
      (supportProduct (0 : AES.Word) (fun _ : Fin 4 => false) b) f x)).trans
        (congrFun (supportProduct_decomposition (0 : AES.Word)
          (fun _ : Fin 4 => false) f) x)
  rw [hsum, Fin.sum_univ_succ] at hgroup
  have hz : fullComponent f (Fin.castAdd 10 (0 : Fin 5)) x = 0 := by
    exact congrFun (fullComponent_zero f hf) x
  rw [hz, zero_add] at hgroup
  exact hgroup.symm

theorem activity_sum (f : State → ℝ) (hf : (∑ x, f x) = 0) :
    (∑ x, activity f x) = 0 := by
  exact ((coordinateKernel_pointed _ _
    (fun _ : Fin 4 => activityMatrix_pointed (0 : AES.Word) word_card_gt_one)).action_sum f).trans hf

theorem activity_zero (f : State → ℝ) (hf : f 0 = 0) : activity f 0 = 0 := by
  exact ((coordinateKernel_pointed _ _
    (fun _ : Fin 4 => activityMatrix_pointed (0 : AES.Word) word_card_gt_one)).action_zero f).trans hf

theorem activity_allActive (f : State → ℝ) (x y : State)
    (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0) : activity f x = activity f y := by
  unfold activity action
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg (fun a : ℝ => a * f z)
  apply Finset.prod_congr rfl
  intro i _
  simp [degreePiece, activityMatrix, hx i, hy i]

end AES8.SupportProfile
