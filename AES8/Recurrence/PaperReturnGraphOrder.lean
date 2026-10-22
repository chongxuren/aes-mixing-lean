import AES8.Recurrence.PaperComparisonOrder

/-! Positivity of the graph formulas for arbitrary natural indices.
These scalar facts are separate from physical operator estimates. -/
namespace AES8.PaperComparison
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem overlapLarge_nonneg (i j c s t r z af bf : ℕ) :
    0 ≤ overlapLarge i j c s t r z af bf := by
  unfold overlapLarge
  dsimp only
  apply mul_nonneg _ (qp_pos _).le
  unfold C E H
  positivity

theorem overlapHS_nonneg (i j c s t r z : ℕ) :
    0 ≤ overlapHS i j c s t r z := by
  unfold overlapHS
  dsimp only
  apply mul_nonneg _ (qp_pos _).le
  unfold C E H
  positivity

theorem overlapThin_nonneg (i j c s t r af bf : ℕ) (same : Bool) :
    0 ≤ overlapThin i j c s t r af bf same := by
  unfold overlapThin
  dsimp only
  split
  · apply mul_nonneg _ (qp_pos _).le
    simp only [C, E, H]
    positivity
  · apply mul_nonneg _ (qp_pos _).le
    simp only [C, E, H]
    positivity

theorem wholeGraph_nonneg (i j c s z : ℕ) : 0 ≤ wholeGraph i j c s z := by
  unfold wholeGraph
  apply mul_nonneg _ (qp_pos _).le
  unfold E
  positivity

theorem returnTerm_nonneg (i a j b c mu lam : ℕ) :
    0 ≤ returnTerm i a j b c mu lam := by
  unfold returnTerm
  dsimp only
  split
  · apply le_min (wholeGraph_nonneg _ _ _ _ _)
    split
    · apply le_min _ (overlapHS_nonneg _ _ _ _ _ _ _)
      split
      · exact overlapLarge_nonneg _ _ _ _ _ _ _ _ _
      · exact overlapThin_nonneg _ _ _ _ _ _ _ _ _
    · split
      · exact overlapLarge_nonneg _ _ _ _ _ _ _ _ _
      · exact overlapThin_nonneg _ _ _ _ _ _ _ _ _
  · exact le_rfl

theorem returnGraph_nonneg (i a j b : ℕ) : 0 ≤ returnGraph i a j b := by
  unfold returnGraph
  have h00 := returnTerm_nonneg i a j b 3 0 0
  have h01 := returnTerm_nonneg i a j b 3 0 1
  have h10 := returnTerm_nonneg i a j b 3 1 0
  have h11 := returnTerm_nonneg i a j b 3 1 1
  have h4 := returnTerm_nonneg i a j b 4 0 0
  have he := eta_pos
  have hx := xi_pos
  positivity

end AES8.PaperComparison
