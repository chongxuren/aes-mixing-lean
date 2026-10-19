import AESConcrete.MarkedBlockVectorization
import AESConcrete.MixedCodeMoment

/-!
# Actual shortened sources of two-sided marked contractions

Zero frame choices impose actual physical graph zeros. Uniform choices
contribute exactly 1/16 per coordinate. The normalized source is a unit
finite-source indicator, not a probability law. This module assumes no
desired code or block energy. Constructive mathematics only; no attacks,
manuscript changes or edits to frozen sources.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.MarkedBlockShortening
open AESMixing AESMixing.AES
open AESConcrete.ActivityFrame
open AESConcrete.MarkedBlockVectorization
open AESConcrete.ShortenedLineResponse

attribute [local instance] Classical.propDecidable

section FrameWeight
variable {I V : Type*} [Fintype I] [DecidableEq I] [Zero V] [DecidableEq V]

def uniformCount (s : I → Bool) : ℕ := Fintype.card {i : I // s i = true}

/-- Exact weight of zero/uniform choices in the normalized byte frame. -/
theorem frame_weight (s : I → Bool) (x : I → V) :
    frameColumn s x =
      (if ∀ i : I, s i = false → x i = 0 then (1 : ℝ) else 0) /
        (16 : ℝ)^uniformCount s := by
  have hp (i : I) : byteFrame (s i) (x i) =
      (if s i = false → x i = 0 then (1 : ℝ) else 0) /
        (if s i then (16 : ℝ) else 1) := by
    cases hs : s i <;> simp [byteFrame, identityKernel, hs]
  unfold frameColumn
  simp_rw [hp]
  rw [Finset.prod_div_distrib, product_indicator]
  congr 1
  simp [uniformCount, Fintype.card_subtype, Finset.prod_ite]

end FrameWeight

def zeroPositions (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Finset GraphPosition :=
  Finset.univ.filter (fun p => ∃ h : m p ≠ true, s ⟨p,h⟩ = false)

def outputZeros (m : GraphPosition → Bool) (s : Activity m → Bool) : Fin 16 :=
  outputPositionMask (zeroPositions m s)

def inputZeros (m : GraphPosition → Bool) (s : Activity m → Bool) : Fin 16 :=
  inputPositionMask (zeroPositions m s)

theorem mem_zeroPositions (m : GraphPosition → Bool) (s : Activity m → Bool)
    (p : GraphPosition) :
    p ∈ zeroPositions m s ↔ ∃ h : m p ≠ true, s ⟨p,h⟩ = false := by
  simp [zeroPositions]

theorem outputZeros_bit (m : GraphPosition → Bool) (s : Activity m → Bool)
    (i : Fin 4) :
    maskBit (outputZeros m s) i = true ↔
      ∃ h : m (Sum.inl i) ≠ true, s ⟨Sum.inl i,h⟩ = false := by
  rw [outputZeros, outputPositionMask_bit, mem_zeroPositions]

theorem inputZeros_bit (m : GraphPosition → Bool) (s : Activity m → Bool)
    (i : Fin 4) :
    maskBit (inputZeros m s) i = true ↔
      ∃ h : m (Sum.inr i) ≠ true, s ⟨Sum.inr i,h⟩ = false := by
  rw [inputZeros, inputPositionMask_bit, mem_zeroPositions]

section Shortened
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem graph_conditions (L : (Fin 4 → V) →+ (Fin 4 → V))
    (m : GraphPosition → Bool) (s : Activity m → Bool) (x : Fin 4 → V) :
    graphZeroConditions L (outputZeros m s) (inputZeros m s) x ↔
      ∀ i : Activity m, s i = false → graphCoordinate L x i.val = 0 := by
  constructor
  · rintro ⟨ho,hi⟩ ⟨p,hp⟩ hs
    cases p with
    | inl i => exact ho i ((outputZeros_bit m s i).mpr ⟨hp,hs⟩)
    | inr i => exact hi i ((inputZeros_bit m s i).mpr ⟨hp,hs⟩)
  · intro h
    constructor
    · intro i hi
      obtain ⟨hp,hs⟩ := (outputZeros_bit m s i).mp hi
      exact h ⟨Sum.inl i,hp⟩ hs
    · intro i hi
      obtain ⟨hp,hs⟩ := (inputZeros_bit m s i).mp hi
      exact h ⟨Sum.inr i,hp⟩ hs

def sourceCoordinates (L : (Fin 4 → V) →+ (Fin 4 → V))
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (c : ShortenedGraph L (outputZeros m s) (inputZeros m s)) : Marked m → V :=
  fun p => graphCoordinate L c.val p.val

def rawResponse (L : (Fin 4 → V) →+ (Fin 4 → V))
    (m : GraphPosition → Bool) (s : Activity m → Bool)
    (T : Marked m → V → V → ℝ) (y : Marked m → V) : ℝ :=
  ∑ c : ShortenedGraph L (outputZeros m s) (inputZeros m s),
    ∏ p : Marked m, T p (y p) (sourceCoordinates L m s c p)

/-- Every zero condition and every 1/16 factor belongs to the actual graph. -/
theorem contractedResponse_shortened (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (m : GraphPosition → Bool)
    (s : Activity m → Bool) (T : Marked m → V → V → ℝ) (y : Marked m → V) :
    contractedResponse m T (graphCoordinate L) s y =
      rawResponse L m s T y / (16 : ℝ)^uniformCount s := by
  rw [contractedResponse_formula hV]
  have hw (x : Fin 4 → V) :
      (∏ i : Activity m, byteFrame (s i) (graphCoordinate L x i.val)) =
        (if graphZeroConditions L (outputZeros m s) (inputZeros m s) x
          then (1 : ℝ) else 0) / (16 : ℝ)^uniformCount s := by
    change frameColumn s (fun i => graphCoordinate L x i.val) = _
    rw [frame_weight]
    by_cases hx : graphZeroConditions L (outputZeros m s) (inputZeros m s) x
    · rw [if_pos ((graph_conditions L m s x).mp hx), if_pos hx]
    · have hf : ¬ ∀ i : Activity m, s i = false → graphCoordinate L x i.val = 0 :=
        fun h => hx ((graph_conditions L m s x).mpr h)
      rw [if_neg hf, if_neg hx]
  simp_rw [hw, ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  calc
    _ = ∑ x : Fin 4 → V,
        (if graphZeroConditions L (outputZeros m s) (inputZeros m s) x
          then (1 : ℝ) else 0) *
          ∏ p : Marked m, T p (y p) (graphCoordinate L x p.val) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = rawResponse L m s T y := by
      rw [shortened_graph_weight]
      rfl

theorem source_card (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s)) =
      Fintype.card V ^ (4-(maskSize (outputZeros m s) + maskSize (inputZeros m s))) :=
  mds_graph_zero_count L hL (outputZeros m s) (inputZeros m s)

/-- The code response used by the mixed-moment interface is normalized by
the square root of the actual source cardinality. -/
theorem contractedResponse_normalized (hV : Fintype.card V = 256)
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (m : GraphPosition → Bool)
    (s : Activity m → Bool) (T : Marked m → V → V → ℝ) (y : Marked m → V) :
    contractedResponse m T (graphCoordinate L) s y =
      (Real.sqrt (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s))) /
        (16 : ℝ)^uniformCount s) *
        MixedCodeMoment.normalizedResponse T (sourceCoordinates L m s) y := by
  have hc : 0 < Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s)) :=
    Fintype.card_pos_iff.mpr ⟨zeroGraph L (outputZeros m s) (inputZeros m s)⟩
  have hs : 0 < Real.sqrt
      (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s)) : ℝ) :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hc)
  rw [contractedResponse_shortened hV]
  unfold MixedCodeMoment.normalizedResponse MixedCodeMoment.responseKernel rawResponse
  field_simp [ne_of_gt hs]

theorem normalization_square (L : (Fin 4 → V) →+ (Fin 4 → V))
    (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (Real.sqrt (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s))) /
      (16 : ℝ)^uniformCount s)^2 =
      (Fintype.card (ShortenedGraph L (outputZeros m s) (inputZeros m s)) : ℝ) /
        (256 : ℝ)^uniformCount s := by
  have hp : ((16 : ℝ)^uniformCount s)^2 = (256 : ℝ)^uniformCount s := by
    rw [← pow_mul, Nat.mul_comm (uniformCount s) 2, pow_mul]
    norm_num
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), hp]

end Shortened

theorem actual_contractedResponse_shortened
    (left right : AESConcrete.ByteOrientations.Orientation) (inverse : Bool)
    (m : GraphPosition → Bool) (s : Activity m → Bool) (y : Marked m → BinaryWord 8) :
    contractedResponse m (markedLeg (AESConcrete.ByteOrientations.channel left)
      (AESConcrete.ByteOrientations.channel right) m)
      (graphCoordinate (byteDiffusionHom inverse)) s y =
      rawResponse (byteDiffusionHom inverse) m s
        (markedLeg (AESConcrete.ByteOrientations.channel left)
          (AESConcrete.ByteOrientations.channel right) m) y /
        (16 : ℝ)^uniformCount s :=
  contractedResponse_shortened (by norm_num [BinaryWord.card]) _ _ _ _ _

end AESConcrete.MarkedBlockShortening
