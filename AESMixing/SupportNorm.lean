import AESMixing.SupportRepresentation
import AESMixing.SupportIncidenceBound

/-! The exact embedding energy supplies the normalization of a genuine
support block. Bounds are relative to the norm of the projected input,
not to a chosen factorization or to an unrelated coefficient vector. -/
noncomputable section
open scoped BigOperators
namespace AESMixing
open AES (maskBit maskSize)
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

def supportNormFactor (V : Type*) [Fintype V] (r out : Fin 16) : ℝ :=
  Real.sqrt (((Fintype.card V : ℝ)-1)^(4-(maskSize r+maskSize out)))

omit [AddCommGroup V] [DecidableEq V] in
theorem supportNormFactor_pos (hn : 1 < Fintype.card V) (r out : Fin 16) :
    0 < supportNormFactor V r out := by
  have hm : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  unfold supportNormFactor
  apply Real.sqrt_pos.2
  exact pow_pos (by linarith) _

theorem supportEmbedding_l2 (hn : 1 < Fintype.card V) (r out : Fin 16)
    (hr : MaskDisjoint r out) (f : (MaskCoordinates out → V) → ℝ) :
    l2 (supportEmbedding r out f) = supportNormFactor V r out * l2 f := by
  have hm' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hm : (0 : ℝ) < Fintype.card V-1 := by linarith
  unfold l2 supportNormFactor
  rw [supportEmbedding_energy r out hr,Real.sqrt_mul (le_of_lt (pow_pos hm _))]

theorem normalized_support_diffusion_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (k : MaskCoordinates inp)
    (f : (MaskCoordinates inp → V) → ℝ) (hf : markedResidual inp f = f)
    (g : (MaskCoordinates out → V) → ℝ) (hg : markedResidual out g = g) :
    |∑ x : Fin 4 → V, supportEmbedding r out g (L x) * supportEmbedding z inp f x| ≤
      (shorteningNormSum (Fintype.card V) r z (unmarkedGraphPositions r z out inp) out inp /
        (supportNormFactor V r out * supportNormFactor V z inp)) *
          l2 (supportEmbedding z inp f) * l2 (supportEmbedding r out g) := by
  have h := support_residual_diffusion_bilinear_bound L hL hn r z out inp hr hz k f g
  rw [hf,hg] at h
  rw [supportEmbedding_l2 hn z inp hz,supportEmbedding_l2 hn r out hr]
  have ho := ne_of_gt (supportNormFactor_pos (V := V) hn r out)
  have hi := ne_of_gt (supportNormFactor_pos (V := V) hn z inp)
  convert h using 1
  field_simp [ho,hi]

theorem supportProduct_diffusion_bilinear
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (hn : 1 < Fintype.card V) (r z out inp : Fin 16)
    (hr : MaskDisjoint r out) (hz : MaskDisjoint z inp)
    (k : MaskCoordinates inp) (f g : (Fin 4 → V) → ℝ) :
    |∑ x : Fin 4 → V,
      action (supportProduct 0 (maskBit out) (maskBit r)) g (L x) *
      action (supportProduct 0 (maskBit inp) (maskBit z)) f x| ≤
      (shorteningNormSum (Fintype.card V) r z (unmarkedGraphPositions r z out inp) out inp /
        (supportNormFactor V r out * supportNormFactor V z inp)) *
          l2 (action (supportProduct 0 (maskBit inp) (maskBit z)) f) *
          l2 (action (supportProduct 0 (maskBit out) (maskBit r)) g) := by
  obtain ⟨f',hf,hef⟩ := supportProduct_residual_representation hn z inp hz f
  obtain ⟨g',hg,heg⟩ := supportProduct_residual_representation hn r out hr g
  rw [hef,heg]
  exact normalized_support_diffusion_bilinear L hL hn r z out inp hr hz k f' hf g' hg

end AESMixing
