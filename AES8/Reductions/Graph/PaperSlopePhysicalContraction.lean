import AES8.Reductions.Return.PaperWordGraphCode
import AES8.Math.PaperSlopeLineGram
import AES8.Math.PaperSlopePhysicalLabels

/-!
# Literal two-marked contraction of a linear MDS graph

The original code, zero positions, and uniform positions remain physical
objects.  MDS gives the two vanishing branches and the one-coordinate
parametrization of the surviving shortening.  Linearity gives its nonzero
slope.  No Gram bound or analytic endpoint is a premise.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSlopePhysicalContraction
open AESMixing PaperMDSGram PaperWordGraphCode WordActivityFrame
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
abbrev Position := Fin 8
abbrev R : F → F → ℝ := residualProjection (0 : F)

def marks (m₀ m₁ : Position) : Finset Position := {m₀,m₁}
def zeroPositions (m₀ m₁ : Position) (U : Finset Position) : Finset Position :=
  (marks m₀ m₁ ∪ U)ᶜ

theorem marks_card {m₀ m₁ : Position} (hne : m₀ ≠ m₁) :
    (marks m₀ m₁).card = 2 := by simp [marks,hne]

theorem zero_mark_disjoint (m₀ m₁ : Position) (U : Finset Position) :
    Disjoint (zeroPositions m₀ m₁ U) (marks m₀ m₁) := by
  exact Finset.disjoint_left.mpr (by
    intro i hi hj
    exact (Finset.mem_compl.mp hi) (Finset.mem_union_left U hj))

theorem zero_card_plus {m₀ m₁ : Position} (hne : m₀ ≠ m₁)
    (U : Finset Position) (hd : Disjoint (marks m₀ m₁) U) :
    (zeroPositions m₀ m₁ U).card + U.card = 6 := by
  have h := Finset.card_compl_add_card (marks m₀ m₁ ∪ U)
  rw [Finset.card_union_of_disjoint hd, marks_card hne] at h
  simp only [Fintype.card_fin] at h
  change ((marks m₀ m₁ ∪ U)ᶜ).card + U.card = 6
  omega

theorem mark_not_zero (m₀ m₁ : Position) (U : Finset Position) :
    m₀ ∉ zeroPositions m₀ m₁ U ∧ m₁ ∉ zeroPositions m₀ m₁ U := by
  simp [zeroPositions,marks]

theorem residual_zero_column (y : F) : R y 0 = 0 := by
  have h := degreePiece_symmetric (0 : F) true y 0
  simpa only [degreePiece,if_true,residualProjection_zero_row] using h

theorem residual_row_sum (y : F) : (∑ x : F, R y x) = 0 := by
  have h := degreePiece_column_sum (0 : F)
    (PaperSlopeLineGram.card_gt_one (K := F)) true y
  calc
    (∑ x : F, R y x) = ∑ x : F, R x y := by
      apply Finset.sum_congr rfl
      intro x _
      exact PaperSlopeLineGram.symmetric y x
    _ = 0 := by simpa only [degreePiece,if_true] using h

theorem residual_pair_sum (y : F × F) :
    (∑ z : F × F, R y.1 z.1 * R y.2 z.2) = 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, residual_row_sum, mul_zero]
  simp

def rawContraction (C : AddSubgroup (Position → F)) (Z : Finset Position)
    (m₀ m₁ : Position) (y : F × F) : ℝ :=
  ∑ c : C, if ∀ i ∈ Z, c.val i = 0
    then R y.1 (c.val m₀) * R y.2 (c.val m₁) else 0

/-- Eight literal graph legs: two residuals, uniform legs, and zero legs. -/
def contraction (C : AddSubgroup (Position → F))
    (m₀ m₁ : Position) (U : Finset Position) (y : F × F) : ℝ :=
  ∑ c : C, R y.1 (c.val m₀) * R y.2 (c.val m₁) *
    (∏ i : U, wordFrame 0 true (c.val i.val)) *
    ∏ i : zeroPositions m₀ m₁ U, wordFrame 0 false (c.val i.val)

theorem zero_frame_product (Z : Finset Position) (x : Position → F) :
    (∏ i : Z, wordFrame 0 false (x i.val)) =
      if ∀ i ∈ Z, x i = 0 then 1 else 0 := by
  by_cases hz : ∀ i ∈ Z, x i = 0
  · rw [if_pos hz]
    apply Finset.prod_eq_one
    intro i _
    simp [wordFrame,identityKernel,hz i.val i.property]
  · rw [if_neg hz]
    push_neg at hz
    obtain ⟨i,hi,hx⟩ := hz
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨i,hi⟩ : Z))
    simp [wordFrame,identityKernel,hx]

theorem contraction_factor (C : AddSubgroup (Position → F))
    (m₀ m₁ : Position) (U : Finset Position) (y : F × F) :
    contraction C m₀ m₁ U y =
      xi F ^ U.card * rawContraction C (zeroPositions m₀ m₁ U) m₀ m₁ y := by
  unfold contraction rawContraction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [zero_frame_product]
  have hu : (∏ i : U, wordFrame 0 true (c.val i.val)) = xi F ^ U.card := by
    simp [wordFrame]
  rw [hu]
  by_cases hz : ∀ i ∈ zeroPositions m₀ m₁ U, c.val i = 0 <;> simp [hz]
  <;> ring

/-- The finite-sum grouping uses the actual marked observation, not an
assumed distribution on line labels. -/
theorem weighted_pair_fibers (C : AddSubgroup (Position → F))
    (Z : Finset Position) (m₀ m₁ : Position) (f : F × F → ℝ) :
    (∑ c : C, if ∀ i ∈ Z, c.val i = 0 then f (c.val m₀,c.val m₁) else 0) =
      ∑ z : F × F, f z * ∑ c : C,
        if (∀ i ∈ Z, c.val i = 0) ∧ (c.val m₀,c.val m₁) = z then 1 else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hz : ∀ i ∈ Z, c.val i = 0
  · have hc (z : F × F) :
        ((∀ i ∈ Z, c.val i = 0) ∧ (c.val m₀,c.val m₁) = z) ↔ (c.val m₀,c.val m₁) = z :=
      ⟨And.right,fun h => ⟨hz,h⟩⟩
    simp_rw [hc]
    simp only [if_pos hz,mul_ite,mul_one,mul_zero]
    simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  · have hc (z : F × F) : ¬((∀ i ∈ Z, c.val i = 0) ∧ (c.val m₀,c.val m₁) = z) :=
      fun h => hz h.1
    simp only [if_neg hz,if_neg (hc _),mul_zero,Finset.sum_const_zero]

def pairLabel (m₀ m₁ : Position) (z : F × F) : marks m₀ m₁ → F :=
  fun i => if i.val = m₀ then z.1 else z.2

theorem pair_observation_iff {m₀ m₁ : Position} (hne : m₀ ≠ m₁)
    (c : Position → F) (z : F × F) :
    (fun i : marks m₀ m₁ => c i.val) = pairLabel m₀ m₁ z ↔ (c m₀,c m₁) = z := by
  constructor
  · intro h
    apply Prod.ext
    · simpa [pairLabel] using congrFun h (⟨m₀,by simp [marks]⟩ : marks m₀ m₁)
    · simpa [pairLabel,Ne.symm hne] using
        congrFun h (⟨m₁,by simp [marks]⟩ : marks m₀ m₁)
  · intro h
    have hz₀ : c m₀ = z.1 := congrArg Prod.fst h
    have hz₁ : c m₁ = z.2 := congrArg Prod.snd h
    funext i
    have hi : i.val = m₀ ∨ i.val = m₁ := by
      exact Finset.mem_insert.mp i.property |>.imp_right Finset.mem_singleton.mp
    rcases hi with hi | hi
    · simp [pairLabel,hi,hz₀]
    · simp [pairLabel,hi,Ne.symm hne,hz₁]

theorem pair_fiber_full (C : AddSubgroup (Position → F)) (hC : IsMDS C 4)
    (Z : Finset Position) {m₀ m₁ : Position} (hne : m₀ ≠ m₁)
    (hd : Disjoint Z (marks m₀ m₁)) (hsmall : Z.card + 2 ≤ 4) (z : F × F) :
    (∑ c : C, if (∀ i ∈ Z, c.val i = 0) ∧ (c.val m₀,c.val m₁) = z
      then (1 : ℝ) else 0) = (Fintype.card F : ℝ) ^ (4-(Z.card+2)) := by
  have h := raw_indicator_full C 4 (by decide) hC Z (marks m₀ m₁) hd
    (by simpa only [marks_card hne] using hsmall) (pairLabel m₀ m₁ z)
  simpa only [pair_observation_iff hne,marks_card hne] using h

theorem raw_zero_branch (C : AddSubgroup (Position → F)) (hC : IsMDS C 4)
    (Z : Finset Position) (hZ : 4 ≤ Z.card) (m₀ m₁ : Position) (y : F × F) :
    rawContraction C Z m₀ m₁ y = 0 := by
  apply Finset.sum_eq_zero
  intro c _
  split_ifs with hz
  · have h := zeroShortening_eq_zero C 4 hC Z hZ ⟨c.val,c.property,hz⟩
    have hm : c.val m₀ = 0 := congrFun h m₀
    rw [hm,residual_zero_column,zero_mul]
  · rfl

theorem raw_full_branch (C : AddSubgroup (Position → F)) (hC : IsMDS C 4)
    (Z : Finset Position) {m₀ m₁ : Position} (hne : m₀ ≠ m₁)
    (hd : Disjoint Z (marks m₀ m₁)) (hsmall : Z.card+2 ≤ 4) (y : F × F) :
    rawContraction C Z m₀ m₁ y = 0 := by
  unfold rawContraction
  rw [weighted_pair_fibers C Z m₀ m₁ (fun z => R y.1 z.1 * R y.2 z.2)]
  simp_rw [pair_fiber_full C hC Z hne hd hsmall]
  rw [← Finset.sum_mul,residual_pair_sum,zero_mul]

/-- MDS vanishing leaves exactly three uniform legs for two marked legs. -/
theorem contraction_vanishes (C : AddSubgroup (Position → F)) (hC : IsMDS C 4)
    {m₀ m₁ : Position} (hne : m₀ ≠ m₁) (U : Finset Position)
    (hd : Disjoint (marks m₀ m₁) U) (hU : U.card ≠ 3) (y : F × F) :
    contraction C m₀ m₁ U y = 0 := by
  rw [contraction_factor]
  have hc := zero_card_plus hne U hd
  by_cases hu : U.card ≤ 2
  · rw [raw_zero_branch C hC _ (by omega),mul_zero]
  · rw [raw_full_branch C hC _ hne (zero_mark_disjoint m₀ m₁ U) (by omega),mul_zero]

/-- One original information set supplies the literal remaining coordinate. -/
theorem coordinate_bijective (C : AddSubgroup (Position → F)) (hC : IsMDS C 4)
    (Z : Finset Position) (hZ : Z.card = 3) (m : Position) (hm : m ∉ Z) :
    Function.Bijective (fun x : zeroShortening C Z => x.val m) := by
  have hd : Disjoint Z ({m} : Finset Position) := by simpa using hm
  have hb := selected_projection_bijective C 4 hC Z {m} hd
    (fun _ : Unit => (⟨m,by simp⟩ : ({m} : Finset Position)))
    (fun _ _ _ => Subsingleton.elim _ _) (by simp [hZ])
  constructor
  · intro x y hxy
    apply hb.injective
    funext a
    exact hxy
  · intro t
    obtain ⟨x,hx⟩ := hb.surjective (fun _ => t)
    exact ⟨x,congrFun hx ()⟩

def coordinateEquiv (C : AddSubgroup (Position → F)) (hC : IsMDS C 4)
    (Z : Finset Position) (hZ : Z.card = 3) (m : Position) (hm : m ∉ Z) :
    zeroShortening C Z ≃ F := Equiv.ofBijective _ (coordinate_bijective C hC Z hZ m hm)

theorem rawContraction_shortened (C : AddSubgroup (Position → F))
    (Z : Finset Position) (m₀ m₁ : Position) (y : F × F) :
    rawContraction C Z m₀ m₁ y =
      ∑ x : zeroShortening C Z, R y.1 (x.val m₀) * R y.2 (x.val m₁) := by
  have hs : rawContraction C Z m₀ m₁ y =
      ∑ x : PaperMDSFiber.Fiber C Z (0 : Position → F),
        R y.1 (x.val.val m₀) * R y.2 (x.val.val m₁) := by
    unfold rawContraction
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  rw [hs]
  exact ((zeroShorteningEquiv C Z).sum_comp
    (fun x => R y.1 (x.val.val m₀) * R y.2 (x.val.val m₁))).symm

theorem raw_line (C : AddSubgroup (Position → F)) (hC : IsMDS C 4)
    (Z : Finset Position) (hZ : Z.card = 3) (m₀ m₁ : Position) (hm₀ : m₀ ∉ Z)
    (a : F) (hline : ∀ x : zeroShortening C Z, x.val m₁ = a*x.val m₀)
    (y : F × F) : rawContraction C Z m₀ m₁ y = PaperSlopeLineGram.rawResponse a y := by
  rw [rawContraction_shortened]
  let e := coordinateEquiv C hC Z hZ m₀ hm₀
  calc
    (∑ x : zeroShortening C Z, R y.1 (x.val m₀) * R y.2 (x.val m₁)) =
        ∑ t : F, R y.1 ((e.symm t).val m₀) * R y.2 ((e.symm t).val m₁) :=
      (e.symm.sum_comp (fun x => R y.1 (x.val m₀) * R y.2 (x.val m₁))).symm
    _ = PaperSlopeLineGram.rawResponse a y := by
      apply Finset.sum_congr rfl
      intro t _
      have ht : (e.symm t).val m₀ = t := e.apply_symm_apply t
      rw [hline,ht]

def scaleShortened (C : Submodule F (Position → F)) (Z : Finset Position)
    (t : F) (x : zeroShortening C.toAddSubgroup Z) : zeroShortening C.toAddSubgroup Z :=
  ⟨t • x.val,C.smul_mem t x.property.1,by
    intro i hi
    simp only [Pi.smul_apply,smul_eq_mul,x.property.2 i hi,mul_zero]⟩

def lineSlope (C : Submodule F (Position → F)) (hC : IsMDS C.toAddSubgroup 4)
    (Z : Finset Position) (hZ : Z.card = 3) (m₀ m₁ : Position) (hm₀ : m₀ ∉ Z) : F :=
  ((coordinateEquiv C.toAddSubgroup hC Z hZ m₀ hm₀).symm 1).val m₁

theorem shortened_line (C : Submodule F (Position → F)) (hC : IsMDS C.toAddSubgroup 4)
    (Z : Finset Position) (hZ : Z.card = 3) (m₀ m₁ : Position) (hm₀ : m₀ ∉ Z)
    (x : zeroShortening C.toAddSubgroup Z) :
    x.val m₁ = lineSlope C hC Z hZ m₀ m₁ hm₀ * x.val m₀ := by
  let e := coordinateEquiv C.toAddSubgroup hC Z hZ m₀ hm₀
  let w := e.symm 1
  have hw : w.val m₀ = 1 := e.apply_symm_apply 1
  have hx : x = scaleShortened C Z (x.val m₀) w := by
    apply e.injective
    change x.val m₀ = (x.val m₀) * w.val m₀
    rw [hw,mul_one]
  have h := congrArg (fun v : zeroShortening C.toAddSubgroup Z => v.val m₁) hx
  change x.val m₁ = x.val m₀ * w.val m₁ at h
  change x.val m₁ = w.val m₁ * x.val m₀
  rw [h,mul_comm]

theorem lineSlope_ne_zero (C : Submodule F (Position → F)) (hC : IsMDS C.toAddSubgroup 4)
    (Z : Finset Position) (hZ : Z.card = 3) (m₀ m₁ : Position)
    (hm₀ : m₀ ∉ Z) (hm₁ : m₁ ∉ Z) : lineSlope C hC Z hZ m₀ m₁ hm₀ ≠ 0 := by
  let e := coordinateEquiv C.toAddSubgroup hC Z hZ m₀ hm₀
  let w := e.symm 1
  intro ha
  have he : w = 0 := (coordinate_bijective C.toAddSubgroup hC Z hZ m₁ hm₁).injective
    (show w.val m₁ = (0 : zeroShortening C.toAddSubgroup Z).val m₁ from ha)
  have hw : w.val m₀ = 1 := e.apply_symm_apply 1
  have hz : w.val m₀ = 0 := congrArg (fun v : zeroShortening C.toAddSubgroup Z => v.val m₀) he
  exact one_ne_zero (hw.symm.trans hz)

/-- A symbolic shortening equation identifies the canonical physical slope
by evaluating the derived first-coordinate-one witness. -/
theorem lineSlope_eq_of_equation (C : Submodule F (Position → F))
    (hC : IsMDS C.toAddSubgroup 4) (Z : Finset Position) (hZ : Z.card = 3)
    (m₀ m₁ : Position) (hm₀ : m₀ ∉ Z) (a : F)
    (ha : ∀ x : zeroShortening C.toAddSubgroup Z, x.val m₁ = a*x.val m₀) :
    lineSlope C hC Z hZ m₀ m₁ hm₀ = a := by
  let e := coordinateEquiv C.toAddSubgroup hC Z hZ m₀ hm₀
  have hw : (e.symm 1).val m₀ = 1 := e.apply_symm_apply 1
  change (e.symm 1).val m₁ = a
  rw [ha,hw,mul_one]

theorem xi_cube : xi F ^ 3 = 1 / ((Fintype.card F : ℝ)*Real.sqrt (Fintype.card F)) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have hs : Real.sqrt (Fintype.card F : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  calc
    xi F ^ 3 = xi F ^ 2 * xi F := by ring
    _ = (1/(Fintype.card F : ℝ)) * (1/Real.sqrt (Fintype.card F)) := by
      rw [xi_sq (PaperSlopeLineGram.card_gt_one (K := F))]
      rfl
    _ = _ := by field_simp [ne_of_gt hq,hs]

/-- The surviving line has exactly the paper normalization q^(-3/2). -/
theorem contraction_line (C : Submodule F (Position → F)) (hC : IsMDS C.toAddSubgroup 4)
    {m₀ m₁ : Position} (hne : m₀ ≠ m₁) (U : Finset Position)
    (hd : Disjoint (marks m₀ m₁) U) (hU : U.card = 3) (y : F × F) :
    contraction C.toAddSubgroup m₀ m₁ U y = PaperSlopeLineGram.response
      (lineSlope C hC (zeroPositions m₀ m₁ U) (by have := zero_card_plus hne U hd; omega)
        m₀ m₁ (mark_not_zero m₀ m₁ U).1) y := by
  have hZ : (zeroPositions m₀ m₁ U).card = 3 := by
    have := zero_card_plus hne U hd
    omega
  rw [contraction_factor]
  have hpow : xi F ^ U.card = xi F ^ 3 := congrArg (fun n => xi F ^ n) hU
  rw [hpow,raw_line C.toAddSubgroup hC _ hZ m₀ m₁
    (mark_not_zero m₀ m₁ U).1 _ (shortened_line C hC _ hZ m₀ m₁
      (mark_not_zero m₀ m₁ U).1),xi_cube]
  unfold PaperSlopeLineGram.response
  ring

end AES8.PaperSlopePhysicalContraction
