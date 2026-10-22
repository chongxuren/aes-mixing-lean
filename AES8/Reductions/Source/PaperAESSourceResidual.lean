import AES8.Reductions.Source.PaperAESSourceLaw
import AES8.Reductions.Source.PaperAESSourceMDS
import AES8.Math.PaperRestrictedDiffusionLabels
import AESConcrete.RestrictedCoordinateChoices
import AESConcrete.ColumnSupportResponse

/-!
# The current restricted-response theorem on the actual AES source

This specializes `lem:marginals` (b) with the literal byte laws and the
checked AES MDS map. The marginal keeps every further indicator and its
mass. A separate exact sum identity identifies its signed response with
the established full-word source; no pointwise comparison of signed
responses is used. Constructive verification only; no attacks or searches.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperAESSource
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordColumnGram (Byte Word inputColumn tensorResponse)
open AESConcrete.ShortenedLineResponse (byteDiffusionHom)
open AESConcrete.RestrictedSourcePushforward (fullOutputCoordinates fullWordSource)
open PaperRestrictedDiffusion

attribute [local instance] Classical.propDecidable

/-- Original physical labels, specialized to the actual AES byte resources. -/
theorem restricted_residual_energy_le
    (left right : Orientation) (inverse : Bool) (a : Word)
    (r out : Fin 16) (hd : Disjoint (maskSet r) (maskSet out))
    (hz : maskSize r ≤ (active a).card) (event : Word → Prop) :
    (∑ y : maskSet out → Byte,
      action (coordinateKernel (fun _ : maskSet out => residualMatrix (channel left) 0))
        (paperJointMarginal (byteDiffusionHom inverse) (active a)
          (maskSet r) (maskSet out) (law right a) event) y ^ 2) ≤
      (1 / 64 : ℝ) ^ (2 * maskSize r) *
      ((65 / 8192 : ℝ) * (9 / 128 : ℝ)^2) ^
        min ((active a).card - maskSize r) (maskSize out) *
      ((65 / 8192 : ℝ) - 1 / 255) ^
        (maskSize out - min ((active a).card - maskSize r) (maskSize out)) := by
  have hq : (Fintype.card Byte - 1 : ℝ) = 255 := by norm_num [Byte, BinaryWord.card]
  simpa only [maskSet_card, hq] using
    paper_pointed_restricted_energy (byteDiffusionHom inverse)
      (byteDiffusion_graph_isMDS inverse) (active a) (maskSet r) (maskSet out) hd
      (by simpa using hz) (law right a) event (channel left)
      (channel_resources left).pointed (by norm_num [Byte, BinaryWord.card])
      (1 / 64) (65 / 8192) (9 / 128) (by norm_num)
      (fun i _ x => law_nonneg right a i x) (fun i _ => law_mass_one right a i)
      (fun i hi x => law_point_le right a i hi x)
      (fun i hi => (law_collision right a i hi).le)
      (fun g => residualMatrix_energy (channel_resources left).pointed
        (by norm_num [Byte, BinaryWord.card]) (9 / 128) (channel_resources left).residual g)
      (fun b hb => ((channel_resources left).collision_column b hb).le)

/-- The finite-set labels and the legacy mask-coordinate labels name the
same positions, with unchanged physical coordinate values. -/
def maskCoordinateEquiv (out : Fin 16) : MaskCoordinates out ≃ maskSet out :=
  Equiv.subtypeEquivRight (fun i => (mem_maskSet out i).symm)

/-- Exact pushforward action for an arbitrary signed coordinate kernel.
The source is still the unnormalized full-word event law. -/
theorem jointMarginal_action_eq_response
    (right : Orientation) (inverse : Bool) (a : Word) (r out : Fin 16)
    (event : Word → Prop) (T : Byte → Byte → ℝ) :
    action (coordinateKernel (fun _ : maskSet out => T))
      (paperJointMarginal (byteDiffusionHom inverse) (active a)
        (maskSet r) (maskSet out) (law right a) event) =
      tensorResponse (fun _ : maskSet out => T)
        (fun x i => byteDiffusionOrientation inverse x i.val)
        (fullWordSource right inverse a r event) := by
  funext y
  unfold action
  simp_rw [jointMarginal_eq_concrete]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold tensorResponse AESConcrete.WordColumnGram.tensorColumn fullWordSource
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : AESConcrete.RestrictedSourcePushforward.outputZeros inverse r x ∧ event x
  · simp only [he.1, he.2, true_and, if_pos]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  · have he' (u : maskSet out → Byte) :
        ¬ (AESConcrete.RestrictedSourcePushforward.outputZeros inverse r x ∧ event x ∧
          (fun i : maskSet out => byteDiffusionOrientation inverse x i.val) = u) :=
        fun h => he ⟨h.1, h.2.1⟩
    simp only [if_neg he, he', if_false, mul_zero, Finset.sum_const_zero]

/-- The current generic response is literally the existing full-word
response, including arbitrary extra event mass, after coordinate reindexing. -/
theorem jointMarginal_response_energy_eq
    (left right : Orientation) (inverse : Bool) (a : Word) (r out : Fin 16)
    (event : Word → Prop) :
    (∑ y : maskSet out → Byte,
      action (coordinateKernel (fun _ : maskSet out => residualMatrix (channel left) 0))
        (paperJointMarginal (byteDiffusionHom inverse) (active a)
          (maskSet r) (maskSet out) (law right a) event) y ^ 2) =
      ∑ y : MaskCoordinates out → Byte,
        tensorResponse (fun _ : MaskCoordinates out => residualMatrix (channel left) 0)
          (fullOutputCoordinates inverse out) (fullWordSource right inverse a r event) y ^ 2 := by
  rw [jointMarginal_action_eq_response]
  symm
  exact AESConcrete.RestrictedCoordinateChoices.tensorResponse_reindex_energy
    (maskCoordinateEquiv out) (fun _ : maskSet out => residualMatrix (channel left) 0)
    (fun x i => byteDiffusionOrientation inverse x i.val)
    (fullWordSource right inverse a r event)

/-- The literal full-word response bound obtained solely through the current
MDS source theorem, with all actual byte resource premises discharged. -/
theorem full_residual_energy_le
    (left right : Orientation) (inverse : Bool) (a : Word)
    (r out : Fin 16) (hr : MaskDisjoint r out)
    (hz : maskSize r ≤ (active a).card) (event : Word → Prop) :
    (∑ y : MaskCoordinates out → Byte,
      tensorResponse (fun _ : MaskCoordinates out => residualMatrix (channel left) 0)
        (fullOutputCoordinates inverse out) (fullWordSource right inverse a r event) y ^ 2) ≤
      (1 / 64 : ℝ) ^ (2 * maskSize r) *
      ((65 / 8192 : ℝ) * (9 / 128 : ℝ)^2) ^
        min ((active a).card - maskSize r) (maskSize out) *
      ((65 / 8192 : ℝ) - 1 / 255) ^
        (maskSize out - min ((active a).card - maskSize r) (maskSize out)) := by
  rw [← jointMarginal_response_energy_eq left right inverse a r out event]
  apply restricted_residual_energy_le left right inverse a r out _ hz event
  exact Finset.disjoint_left.mpr (fun i hi ho => hr i
    ((mem_maskSet r i).mp hi) ((mem_maskSet out i).mp ho))

end AES8.PaperAESSource
