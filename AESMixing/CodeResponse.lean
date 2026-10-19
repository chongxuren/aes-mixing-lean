import AESMixing.CodeMoment
import AESMixing.Block

/-! The low-dimensional code-moment bound as an actual tensor response.
The two information sets may be dependent; their bijectivity is sufficient.
The high-dimensional dual-code branch remains a separate obligation. -/
noncomputable section
open scoped BigOperators
namespace AESMixing

variable {C V I J : Type*} [Fintype C] [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

abbrev CodePosition (I J : Type*) := I ⊕ (I ⊕ J)

def codeCoordinates (e f : C ≃ (I → V)) (rest : C → J → V)
    (c : C) : CodePosition I J → V :=
  Sum.elim (e c) (Sum.elim (f c) (rest c))

def codeKernel (T : V → V → ℝ) (e f : C ≃ (I → V)) (rest : C → J → V)
    (y : CodePosition I J → V) (c : C) : ℝ :=
  ∏ i, T (y i) (codeCoordinates e f rest c i)

def codeResponse (T : V → V → ℝ) (e f : C ≃ (I → V)) (rest : C → J → V)
    (y : CodePosition I J → V) : ℝ :=
  (∑ c, codeKernel T e f rest y c) / Real.sqrt (Fintype.card C)

omit [Fintype C] in
theorem codeKernel_gram (T : V → V → ℝ) (e f : C ≃ (I → V))
    (rest : C → J → V) (c d : C) :
    gram (codeKernel T e f rest) c d =
      (∏ i, gram T (e c i) (e d i)) *
      (∏ i, gram T (f c i) (f d i)) *
      (∏ j, gram T (rest c j) (rest d j)) := by
  have h := product_gram (fun (_ : CodePosition I J) => T)
    (codeCoordinates e f rest c) (codeCoordinates e f rest d)
  change gram (codeKernel T e f rest) c d = _ at h
  rw [h]
  simp only [Fintype.prod_sum_type, codeCoordinates, Sum.elim_inl, Sum.elim_inr]
  ring

theorem codeKernel_energy (T : V → V → ℝ) (e f : C ≃ (I → V)) (rest : C → J → V) :
    (∑ y, (∑ c, codeKernel T e f rest y c)^2) =
      ∑ cd : C × C,
        (∏ i, gram T (e cd.1 i) (e cd.2 i)) *
        (∏ i, gram T (f cd.1 i) (f cd.2 i)) *
        (∏ j, gram T (rest cd.1 j) (rest cd.2 j)) := by
  have h := gram_quadratic (codeKernel T e f rest) (fun _ => 1)
  simpa only [mul_one, one_mul, codeKernel_gram, Fintype.sum_prod_type] using h

theorem low_code_response_bound (T : V → V → ℝ) (e f : C ≃ (I → V))
    (rest : C → J → V) (delta : ℝ) (hd : 0 ≤ delta)
    (hdiag : ∀ x, gram T x x ≤ delta) :
    (∑ y, codeResponse T e f rest y^2) ≤
      ((∑ ab : V × V, gram T ab.1 ab.2^2)^Fintype.card I *
        delta^Fintype.card J) / Fintype.card C := by
  have hraw := low_dimension_code_moment e f rest (gram T) delta hd
    (gram_entry_bound T delta hd hdiag)
  have hb : (∑ y, (∑ c, codeKernel T e f rest y c)^2) ≤
      (∑ ab : V × V, gram T ab.1 ab.2^2)^Fintype.card I * delta^Fintype.card J := by
    rw [codeKernel_energy]
    exact (le_abs_self _).trans hraw
  unfold codeResponse
  simp_rw [div_pow]
  rw [← Finset.sum_div, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)

end AESMixing
