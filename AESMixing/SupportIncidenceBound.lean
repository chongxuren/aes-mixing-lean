import AESMixing.SupportIncidence
import AESMixing.RestrictedIncidenceNorm

/-! An incidence bound for genuine support components of the original
four-coordinate diffusion. The normalization factors are supplied by
supportEmbedding_energy; this theorem controls arbitrary joint residuals. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem support_residual_diffusion_bilinear_bound
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (k : MaskCoordinates inp) (f : (MaskCoordinates inp → V) → ℝ)
    (g : (MaskCoordinates out → V) → ℝ) :
    |∑ x : Fin 4 → V, supportEmbedding r out (markedResidual out g) (L x) *
      supportEmbedding z inp (markedResidual inp f) x| ≤
      shorteningNormSum (Fintype.card V) r z (unmarkedGraphPositions r z out inp) out inp *
        l2 f * l2 g := by
  rw [supportEmbedding_diffusion_bilinear L r z out inp hr hz, markedResidual_inner]
  have hb := restricted_incidence_l2 L hL hn r z out inp (unmarkedGraphPositions r z out inp)
    (unmarked_shortening_disjoint r z out inp hr hz) k f
  calc
    _ ≤ l2 g * l2 (markedResidual out (action
        (restrictedGraphIncidence L r z (unmarkedGraphPositions r z out inp) out inp)
        (markedResidual inp f))) := abs_inner_le_l2 _ _
    _ ≤ l2 g * (shorteningNormSum (Fintype.card V) r z
        (unmarkedGraphPositions r z out inp) out inp * l2 f) :=
      mul_le_mul_of_nonneg_left hb (l2_nonneg _)
    _ = _ := by ring

end AESMixing
