import AESConcrete.WordColumnGram
import AESConcrete.AllColumnBound
import AESConcrete.ShortenedLineResponse
import AESConcrete.InverseFrameEnergy

/-!
# Exact physical graph formula for word entries

External zero bytes impose actual input/output zero constraints on the
diffusion graph. Every other byte contributes its actual nonnegative row
or column law. This module proves the exact restriction and factorization;
it assumes no entry bound and does not identify a whole-word Fourier map.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
open scoped BigOperators
namespace AESConcrete.WordEntryGraph
open AESMixing
open AESConcrete.ByteOrientations (Orientation channel channel_resources)
open AESConcrete.WordColumnGram (Byte Word)
open AESConcrete.WordOrientationClosure (wordKernel)
open AESConcrete.AllColumnBound (inputZeroMask inputZeroMask_bit)
open AESConcrete.ShortenedLineResponse
  (remaining byteDiffusionHom byteDiffusionHom_apply)
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000

def leg (left right : Orientation) (a b : Word) : GraphPosition → Byte → ℝ
  | Sum.inl i, v => channel left (b i) v
  | Sum.inr i, v => channel right v (a i)

abbrev Active (a b : Word) :=
  {p : GraphPosition // remaining (inputZeroMask b) (inputZeroMask a) p}

theorem leg_nonneg (left right : Orientation) (a b : Word)
    (p : GraphPosition) (v : Byte) : 0 ≤ leg left right a b p v := by
  cases p with
  | inl i => exact (channel_resources left).nonnegative _ _
  | inr i => exact (channel_resources right).nonnegative _ _

theorem leg_mass (left right : Orientation) (a b : Word) (p : GraphPosition) :
    (∑ v : Byte, leg left right a b p v) = 1 := by
  cases p with
  | inl i => exact (channel_resources left).row_sum _
  | inr i => exact (channel_resources right).column_sum _

theorem active_leg_zero (left right : Orientation) (a b : Word) (p : Active a b) :
    leg left right a b p.val 0 = 0 := by
  rcases p with ⟨p,hp⟩
  cases p with
  | inl i =>
    have hb : b i ≠ 0 := fun h => hp ((inputZeroMask_bit b i).mpr h)
    exact ((channel_resources left).zero_column _).trans (if_neg hb)
  | inr i =>
    have ha : a i ≠ 0 := fun h => hp ((inputZeroMask_bit a i).mpr h)
    exact ((channel_resources right).zero_row _).trans (if_neg ha)

theorem actual_graph_formula (left right : Orientation) (inverse : Bool) (a b : Word) :
    wordKernel left right inverse b a =
      ∑ x : Word, ∏ p : GraphPosition,
        leg left right a b p (graphCoordinate (byteDiffusionHom inverse) x p) := by
  rw [congrFun (WordColumnGram.actual_word_column_response left right inverse a) b]
  unfold WordColumnGram.tensorResponse WordColumnGram.tensorColumn
    WordColumnGram.inputColumn
  apply Finset.sum_congr rfl
  intro x _
  simp only [Fintype.prod_sum_type, leg, graphCoordinate, Sum.elim_inl,
    Sum.elim_inr, byteDiffusionHom_apply]
  rfl

theorem graph_product_zero_outside (left right : Orientation) (inverse : Bool)
    (a b x : Word)
    (hx : ¬ graphZeroConditions (byteDiffusionHom inverse)
      (inputZeroMask b) (inputZeroMask a) x) :
    (∏ p : GraphPosition,
      leg left right a b p (graphCoordinate (byteDiffusionHom inverse) x p)) = 0 := by
  rcases not_and_or.mp hx with ho | hi
  · push Not at ho
    obtain ⟨i,hi,hne⟩ := ho
    apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inl i))
    change channel left (b i) (byteDiffusionHom inverse x i) = 0
    rw [(inputZeroMask_bit b i).mp hi, (channel_resources left).zero_row, if_neg hne]
  · push Not at hi
    obtain ⟨i,hi,hne⟩ := hi
    apply Finset.prod_eq_zero (Finset.mem_univ (Sum.inr i))
    change channel right (x i) (a i) = 0
    rw [(inputZeroMask_bit a i).mp hi, (channel_resources right).zero_column, if_neg hne]

theorem graph_product_on_source (left right : Orientation) (inverse : Bool)
    (a b : Word)
    (c : ShortenedGraph (byteDiffusionHom inverse) (inputZeroMask b) (inputZeroMask a)) :
    (∏ p : GraphPosition,
      leg left right a b p (graphCoordinate (byteDiffusionHom inverse) c.val p)) =
      ∏ p : Active a b,
        leg left right a b p.val (graphCoordinate (byteDiffusionHom inverse) c.val p.val) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype
    (remaining (inputZeroMask b) (inputZeroMask a))]
  have hone : (∏ p : {p : GraphPosition //
      ¬ remaining (inputZeroMask b) (inputZeroMask a) p},
      leg left right a b p.val (graphCoordinate (byteDiffusionHom inverse) c.val p.val)) = 1 := by
    apply Finset.prod_eq_one
    intro p _
    rcases p with ⟨p,hp⟩
    cases p with
    | inl i =>
      have hi : AES.maskBit (inputZeroMask b) i = true := not_not.mp hp
      have hz := c.property.1 i hi
      change channel left (b i) (byteDiffusionHom inverse c.val i) = 1
      rw [(inputZeroMask_bit b i).mp hi, hz, (channel_resources left).zero_row]
      simp
    | inr i =>
      have hi : AES.maskBit (inputZeroMask a) i = true := not_not.mp hp
      have hz := c.property.2 i hi
      change channel right (c.val i) (a i) = 1
      rw [(inputZeroMask_bit a i).mp hi, hz, (channel_resources right).zero_row]
      simp
  rw [hone, mul_one]

/-- The exact sum keeps the same physical shortened graph and counting measure. -/
theorem actual_shortened_formula (left right : Orientation) (inverse : Bool)
    (a b : Word) :
    wordKernel left right inverse b a =
      ∑ c : ShortenedGraph (byteDiffusionHom inverse) (inputZeroMask b) (inputZeroMask a),
        ∏ p : Active a b,
          leg left right a b p.val (graphCoordinate (byteDiffusionHom inverse) c.val p.val) := by
  rw [actual_graph_formula]
  rw [InverseFrameEnergy.sum_subtype_of_zero
    (graphZeroConditions (byteDiffusionHom inverse) (inputZeroMask b) (inputZeroMask a))
    _ (graph_product_zero_outside left right inverse a b)]
  have huniv (f g : Fintype
      (ShortenedGraph (byteDiffusionHom inverse) (inputZeroMask b) (inputZeroMask a))) :
      @Finset.univ _ f = @Finset.univ _ g :=
    congrArg (fun t : Fintype
      (ShortenedGraph (byteDiffusionHom inverse) (inputZeroMask b) (inputZeroMask a)) => t.elems)
      (Subsingleton.elim f g)
  apply Finset.sum_congr (huniv _ _)
  intro c _
  exact graph_product_on_source left right inverse a b c

theorem active_nonempty_of_input_ne_zero (a b : Word) (ha : a ≠ 0) :
    Nonempty (Active a b) := by
  by_contra hn
  apply ha
  funext i
  by_contra hi
  apply hn
  exact ⟨⟨Sum.inr i, fun hz => hi ((inputZeroMask_bit a i).mp hz)⟩⟩

end AESConcrete.WordEntryGraph
