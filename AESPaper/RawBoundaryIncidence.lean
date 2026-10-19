import AESPaper.WordMarkedMoment
import AESPaper.WordMarkedSplit
import AESPaper.RectangularFourier
import AESConcrete.ActualMarkedUniform
import AESMixing.ShortenedIncidence
import AESMixing.IncidenceKernel

/-!
# Actual marked-coordinate incidence of the shortened raw boundary graph

The source point and both physical coordinate maps are retained exactly.
The mask equivalences only rename the same marked coordinate subtypes.
The generic MDS fiber estimates and incidence Schur estimate apply to
arbitrary signed joint inputs, including empty marked coordinate types.
Residual projection, activity-frame normalization, position aggregation,
and identification with the raw boundary operator are separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.RawBoundaryIncidence
open AESMixing AESConcrete
open AESMixing.AES (maskBit maskSize)
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked)
open AESPaper.WordMarkedMoment (Source)
open AESPaper.RectangularFourier (EnergyBound)
-- Keep physical coordinate equalities on their standard decidable instances.

def q : ℝ := 2 ^ 32

theorem q_positive : 0 < q := by norm_num [q]

theorem q_eq_word_card : q = (Fintype.card AES.Word : ℝ) :=
  WordMarkedMoment.word_card_real.symm

def outputMask (m : GraphPosition → Bool) : Fin 16 :=
  outputPositionMask (ActualMarkedUniform.markedPositions m)

def inputMask (m : GraphPosition → Bool) : Fin 16 :=
  inputPositionMask (ActualMarkedUniform.markedPositions m)

theorem outputMask_bit (m : GraphPosition → Bool) (i : Fin 4) :
    maskBit (outputMask m) i = true ↔ m (Sum.inl i) = true := by
  rw [outputMask, outputPositionMask_bit]
  simp [ActualMarkedUniform.markedPositions]

theorem inputMask_bit (m : GraphPosition → Bool) (i : Fin 4) :
    maskBit (inputMask m) i = true ↔ m (Sum.inr i) = true := by
  rw [inputMask, inputPositionMask_bit]
  simp [ActualMarkedUniform.markedPositions]

/-- Both sides of this equivalence retain the same physical output index. -/
def outputEquiv (m : GraphPosition → Bool) :
    OutputMarked m ≃ MaskCoordinates (outputMask m) where
  toFun i := ⟨i.val, (outputMask_bit m i.val).mpr i.property⟩
  invFun i := ⟨i.val, (outputMask_bit m i.val).mp i.property⟩
  left_inv i := Subtype.ext rfl
  right_inv i := Subtype.ext rfl

/-- Both sides of this equivalence retain the same physical input index. -/
def inputEquiv (m : GraphPosition → Bool) :
    InputMarked m ≃ MaskCoordinates (inputMask m) where
  toFun i := ⟨i.val, (inputMask_bit m i.val).mpr i.property⟩
  invFun i := ⟨i.val, (inputMask_bit m i.val).mp i.property⟩
  left_inv i := Subtype.ext rfl
  right_inv i := Subtype.ext rfl

@[simp] theorem outputEquiv_val (m : GraphPosition → Bool) (i : OutputMarked m) :
    (outputEquiv m i).val = i.val := rfl

@[simp] theorem outputEquiv_symm_val (m : GraphPosition → Bool)
    (i : MaskCoordinates (outputMask m)) :
    ((outputEquiv m).symm i).val = i.val := rfl

@[simp] theorem inputEquiv_val (m : GraphPosition → Bool) (i : InputMarked m) :
    (inputEquiv m i).val = i.val := rfl

@[simp] theorem inputEquiv_symm_val (m : GraphPosition → Bool)
    (i : MaskCoordinates (inputMask m)) :
    ((inputEquiv m).symm i).val = i.val := rfl

theorem outputMask_size (m : GraphPosition → Bool) :
    maskSize (outputMask m) = Fintype.card (OutputMarked m) := by
  calc
    _ = Fintype.card (MaskCoordinates (outputMask m)) :=
      (maskCoordinates_card (outputMask m)).symm
    _ = _ := (Fintype.card_congr (outputEquiv m)).symm

theorem inputMask_size (m : GraphPosition → Bool) :
    maskSize (inputMask m) = Fintype.card (InputMarked m) := by
  calc
    _ = Fintype.card (MaskCoordinates (inputMask m)) :=
      (maskCoordinates_card (inputMask m)).symm
    _ = _ := (Fintype.card_congr (inputEquiv m)).symm

theorem outputZeros_disjoint_outputMask (m : GraphPosition → Bool)
    (s : Activity m → Bool) : MaskDisjoint (outputZeros m s) (outputMask m) := by
  intro i hi hm
  have hp : m (Sum.inl i) = true := (outputMask_bit m i).mp hm
  have hf := ActualMarkedCodeMoment.marked_remaining m s (⟨Sum.inl i, hp⟩ : Marked m)
  change maskBit (outputZeros m s) i ≠ true at hf
  exact hf hi

theorem inputZeros_disjoint_inputMask (m : GraphPosition → Bool)
    (s : Activity m → Bool) : MaskDisjoint (inputZeros m s) (inputMask m) := by
  intro i hi hm
  have hp : m (Sum.inr i) = true := (inputMask_bit m i).mp hm
  have hf := ActualMarkedCodeMoment.marked_remaining m s (⟨Sum.inr i, hp⟩ : Marked m)
  change maskBit (inputZeros m s) i ≠ true at hf
  exact hf hi

def zeroCount (m : GraphPosition → Bool) (s : Activity m → Bool) : ℕ :=
  maskSize (outputZeros m s) + maskSize (inputZeros m s)

/-- Output labels are taken from the actual forward boundary of the source. -/
def outputSource (m : GraphPosition → Bool) (s : Activity m → Bool)
    (c : Source m s) : OutputMarked m → AES.Word :=
  fun i => GroupedRecurrence.boundary c.val i.val

/-- Input labels are the corresponding coordinates of that same source. -/
def inputSource (m : GraphPosition → Bool) (s : Activity m → Bool)
    (c : Source m s) : InputMarked m → AES.Word := fun i => c.val i.val

theorem outputSource_eq_shortenedOutput (m : GraphPosition → Bool)
    (s : Activity m → Bool) (c : Source m s) (i : OutputMarked m) :
    outputSource m s c i =
      shortenedOutput GroupedRecurrence.boundary.toAddMonoidHom
        (outputZeros m s) (inputZeros m s) (outputMask m) c (outputEquiv m i) := rfl

theorem inputSource_eq_shortenedInput (m : GraphPosition → Bool)
    (s : Activity m → Bool) (c : Source m s) (i : InputMarked m) :
    inputSource m s c i =
      shortenedInput GroupedRecurrence.boundary.toAddMonoidHom
        (outputZeros m s) (inputZeros m s) (inputMask m) c (inputEquiv m i) := rfl

theorem output_fiber_bound (m : GraphPosition → Bool) (s : Activity m → Bool)
    (y : OutputMarked m → AES.Word) :
    Fintype.card {c : Source m s // outputSource m s c = y} ≤
      (2 ^ 32 : ℕ) ^ (4 - (zeroCount m s + Fintype.card (OutputMarked m))) := by
  let y' : MaskCoordinates (outputMask m) → AES.Word :=
    fun i => y ((outputEquiv m).symm i)
  have he (c : Source m s) : outputSource m s c = y ↔
      shortenedOutput GroupedRecurrence.boundary.toAddMonoidHom
        (outputZeros m s) (inputZeros m s) (outputMask m) c = y' := by
    constructor
    · intro hc
      funext i
      exact congrFun hc ((outputEquiv m).symm i)
    · intro hc
      funext i
      have hv := congrFun hc (outputEquiv m i)
      change GroupedRecurrence.boundary c.val i.val =
        y ((outputEquiv m).symm (outputEquiv m i)) at hv
      change GroupedRecurrence.boundary c.val i.val = y i
      simpa only [Equiv.symm_apply_apply] using hv
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  have h := shortened_output_fiber_bound GroupedRecurrence.boundary.toAddMonoidHom
    ActivityKernel.aesBoundary_zeroMDS (outputZeros m s) (inputZeros m s)
    (outputMask m) (outputZeros_disjoint_outputMask m s) y'
  simpa only [zeroCount, outputMask_size, AES.word_card] using h

theorem input_fiber_bound (m : GraphPosition → Bool) (s : Activity m → Bool)
    (x : InputMarked m → AES.Word) :
    Fintype.card {c : Source m s // inputSource m s c = x} ≤
      (2 ^ 32 : ℕ) ^ (4 - (zeroCount m s + Fintype.card (InputMarked m))) := by
  let x' : MaskCoordinates (inputMask m) → AES.Word :=
    fun i => x ((inputEquiv m).symm i)
  have he (c : Source m s) : inputSource m s c = x ↔
      shortenedInput GroupedRecurrence.boundary.toAddMonoidHom
        (outputZeros m s) (inputZeros m s) (inputMask m) c = x' := by
    constructor
    · intro hc
      funext i
      exact congrFun hc ((inputEquiv m).symm i)
    · intro hc
      funext i
      have hv := congrFun hc (inputEquiv m i)
      change c.val i.val = x ((inputEquiv m).symm (inputEquiv m i)) at hv
      change c.val i.val = x i
      simpa only [Equiv.symm_apply_apply] using hv
  rw [Fintype.card_congr (Equiv.subtypeEquivRight he)]
  have h := shortened_input_fiber_bound GroupedRecurrence.boundary.toAddMonoidHom
    ActivityKernel.aesBoundary_zeroMDS (outputZeros m s) (inputZeros m s)
    (inputMask m) (inputZeros_disjoint_inputMask m s) x'
  simpa only [zeroCount, inputMask_size, AES.word_card] using h

def incidenceKernel (m : GraphPosition → Bool) (s : Activity m → Bool) :
    (OutputMarked m → AES.Word) → (InputMarked m → AES.Word) → ℝ :=
  incidenceMultiplicity (outputSource m s) (inputSource m s)

theorem incidence_nonnegative (m : GraphPosition → Bool) (s : Activity m → Bool)
    (y : OutputMarked m → AES.Word) (x : InputMarked m → AES.Word) :
    0 ≤ incidenceKernel m s y x :=
  incidenceMultiplicity_nonnegative (outputSource m s) (inputSource m s) y x

/-- Literal natural powers retain truncation until surviving dimensions
and the separate activity-frame divisor have been matched. -/
theorem incidence_energy (m : GraphPosition → Bool) (s : Activity m → Bool)
    (f : (InputMarked m → AES.Word) → ℝ) :
    (∑ y : OutputMarked m → AES.Word, action (incidenceKernel m s) f y ^ 2) ≤
      q ^ (4 - (zeroCount m s + Fintype.card (OutputMarked m))) *
        q ^ (4 - (zeroCount m s + Fintype.card (InputMarked m))) *
          ∑ x : InputMarked m → AES.Word, f x ^ 2 := by
  have h := incidenceMultiplicity_schur (outputSource m s) (inputSource m s)
    ((2 ^ 32 : ℕ) ^ (4 - (zeroCount m s + Fintype.card (OutputMarked m))))
    ((2 ^ 32 : ℕ) ^ (4 - (zeroCount m s + Fintype.card (InputMarked m))))
    (output_fiber_bound m s) (input_fiber_bound m s) f
  simpa only [incidenceKernel, Nat.cast_pow, Nat.cast_ofNat, q] using h

theorem incidence_energyBound (m : GraphPosition → Bool) (s : Activity m → Bool) :
    EnergyBound (incidenceKernel m s)
      (Real.sqrt (q ^ (4 - (zeroCount m s + Fintype.card (OutputMarked m))) *
        q ^ (4 - (zeroCount m s + Fintype.card (InputMarked m))))) := by
  intro f
  rw [Real.sq_sqrt (mul_nonneg (pow_nonneg q_positive.le _)
    (pow_nonneg q_positive.le _))]
  exact incidence_energy m s f

end AESPaper.RawBoundaryIncidence
