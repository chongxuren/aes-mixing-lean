import AES8.Reductions.Support.PaperSupportOutside
import AES8.Math.PaperActivityMinorTransport
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Physical frame positions for the support expansion

The chosen full-uniform coordinates are the actual positions of the selected
constant-nonzero outside factors. Residual and prescribed-zero positions are
kept distinct. No alphabet values are enumerated.
-/
noncomputable section
open scoped BigOperators
namespace AES8.PaperSupportFrameJoin
open AESMixing PaperSupportProjection PaperSupportCoordinates PaperSupportOutside
open PaperActivityExpansion WordActivityFrame PaperKernelBounds PaperTensorCompression
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

def residualSet (p : Label n) : Finset (Fin n) :=
  Finset.univ.filter (fun k => p.1 k = true)

def residualEquiv (p : Label n) : Residual p ≃ residualSet p :=
  { toFun := fun k => ⟨k.val, by simp [residualSet, k.property]⟩
    invFun := fun k => ⟨k.val, (Finset.mem_filter.mp k.property).2⟩
    left_inv := by intro k; rfl
    right_inv := by intro k; rfl }

def fullEmbedding (p : Label n) : Active p ↪ Fin n :=
  ⟨fun k => k.val.val, fun _ _ h => Subtype.ext (Subtype.ext h)⟩

def fullSet (p : Label n) (s : Finset (Active p)) : Finset (Fin n) :=
  s.map (fullEmbedding p)

theorem full_card (p : Label n) (s : Finset (Active p)) : (fullSet p s).card = s.card :=
  Finset.card_map _

theorem full_mem_iff (p : Label n) (s : Finset (Active p)) (k : Active p) :
    k.val.val ∈ fullSet p s ↔ k ∈ s := by
  constructor
  · intro h
    obtain ⟨a,ha,he⟩ := Finset.mem_map.mp h
    have hk : a = k := (fullEmbedding p).injective he
    simpa only [hk] using ha
  · intro h
    exact Finset.mem_map.mpr ⟨k,h,rfl⟩

theorem zero_not_mem (p : Label n) (s : Finset (Active p)) (k : Inactive p) :
    k.val.val ∉ fullSet p s := by
  intro h
  obtain ⟨a,_,he⟩ := Finset.mem_map.mp h
  apply k.property
  have ha := a.property
  change p.2 a.val.val = false at ha
  change a.val.val = k.val.val at he
  simpa only [he] using ha

theorem full_disjoint (p : Label n) (s : Finset (Active p)) :
    Disjoint (fullSet p s) (residualSet p) := by
  apply Finset.disjoint_left.mpr
  intro k hk hr
  obtain ⟨a,_,he⟩ := Finset.mem_map.mp hk
  have hm := (Finset.mem_filter.mp hr).2
  apply a.val.property
  change a.val.val = k at he
  simpa only [he] using hm

theorem frameProduct_as_product {I : Type*} [Fintype I] [DecidableEq I]
    (z : V) (s : Finset I) (x : I → V) :
    frameProduct z s x = ∏ k, wordFrame z (decide (k ∈ s)) (x k) := by
  have he (k : I) : wordFrame z (decide (k ∈ s)) (x k) =
      if k ∈ s then wordFrame z true (x k) else wordFrame z false (x k) := by
    by_cases h : k ∈ s <;> simp [h]
  simp_rw [he]
  rw [Finset.prod_ite]
  have hs : Finset.univ.filter (fun k => k ∈ s) = s := by ext; simp
  have hc : Finset.univ.filter (fun k => k ∉ s) = Finset.univ \ s := by ext; simp
  rw [hs, hc]
  rfl

theorem outside_as_product (z : V) (p : Label n) (s : Finset (Active p))
    (x : Outside p → V) :
    frameOutside z p s x = ∏ k : Outside p,
      wordFrame z (decide (k.val ∈ fullSet p s)) (x k) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun k : Outside p => p.2 k.val = false)]
  unfold frameOutside
  apply congrArg₂ (· * ·)
  · rw [frameProduct_as_product]
    apply Finset.prod_congr rfl
    intro k _
    simp only [full_mem_iff]
  · unfold zeroFactor
    apply Finset.prod_congr rfl
    intro k _
    simp only [zero_not_mem, decide_false]

def maskedAnalysis (z : V) (p : Label n) (s : Finset (Active p))
    (y : Residual p → V) (x : Fin n → V) : ℝ :=
  residualKernel z p y ((split p) x).1 * frameOutside z p s ((split p) x).2

/-- Physical retained-coordinate analysis and the split-coordinate expression
are literally the same, without a normalization scalar. -/
theorem analysis_eq [AddCommGroup V] (p : Label n) (s : Finset (Active p))
    (y : Residual p → V) (x : Fin n → V) :
    PaperActivityMinorTransport.analysis (residualSet p)
      (fun k => decide (k ∈ fullSet p s)) (fun k => y ((residualEquiv p).symm k)) x =
      maskedAnalysis (0 : V) p s y x := by
  unfold PaperActivityMinorTransport.analysis
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun k : Fin n => p.1 k = true)]
  unfold maskedAnalysis residualKernel
  rw [outside_as_product]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro k _
    have hk : k.val ∈ residualSet p := by simp [residualSet,k.property]
    simp only [dif_pos hk]
    rfl
  · apply Finset.prod_congr rfl
    intro k _
    have hk : k.val ∉ residualSet p := by simp [residualSet,k.property]
    simp only [dif_neg hk]
    rfl

end AES8.PaperSupportFrameJoin
