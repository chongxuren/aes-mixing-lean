import AESPaper.WordOperatorDuality
import AESPaper.RectangularBounds
import AESPaper.WordEncodingOperator

/-!
# Physical encodings of a common actual marked source

The output and input encodings have one common finite source. The exact
matrix factorization uses the transpose of the input encoding, separately
from the residual legs' already fixed physical adjoint flags. Actual core
equivalences come from physical primal or annihilator information sets.
Cardinality alone is never substituted for these bijections.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.WordPhysicalEncoding
open AESMixing AESConcrete
open AESConcrete.MarkedBlockVectorization (Marked Activity)
open AESConcrete.MarkedBlockShortening (outputZeros inputZeros uniformCount sourceCoordinates)
open AESConcrete.WordFourierVariants (variant)
open AESPaper.WordMarkedSplit (OutputMarked InputMarked outputPosition inputPosition join)
open AESPaper.RectangularFourier (EnergyBound)
open AESPaper.WordEncodingOperator (encodingKernel)
open AESPaper.WordMarkedMoment (Source)
attribute [local instance] Classical.propDecidable

def sideCoefficient (A J : Type*) [Fintype A] [Fintype J] : ℝ :=
  WeightedEncoding.nu ^ Fintype.card A * Real.sqrt (WeightedEncoding.delta ^ Fintype.card J)

theorem sideCoefficient_nonnegative (A J : Type*) [Fintype A] [Fintype J] :
    0 ≤ sideCoefficient A J :=
  mul_nonneg (pow_nonneg WeightedEncoding.nu_nonnegative _) (Real.sqrt_nonneg _)

section CommonSource
variable {C A B JO JI : Type*} [Fintype C]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype JO] [DecidableEq JO] [Fintype JI] [DecidableEq JI]

def outputEncoding (m : GraphPosition → Bool) (adjoint fourier : Marked m → Bool)
    (coord : C → Marked m → AES.Word) : (OutputMarked m → AES.Word) → C → ℝ :=
  encodingKernel (fun o => adjoint (outputPosition m o))
    (fun o => fourier (outputPosition m o)) (fun c o => coord c (outputPosition m o))

def inputEncoding (m : GraphPosition → Bool) (adjoint fourier : Marked m → Bool)
    (coord : C → Marked m → AES.Word) : (InputMarked m → AES.Word) → C → ℝ :=
  encodingKernel (fun i => adjoint (inputPosition m i))
    (fun i => fourier (inputPosition m i)) (fun c i => coord c (inputPosition m i))

def rawResponse (m : GraphPosition → Bool) (adjoint fourier : Marked m → Bool)
    (coord : C → Marked m → AES.Word) (v : Marked m → AES.Word) : ℝ :=
  ∑ c : C, ∏ p : Marked m, variant (adjoint p) (fourier p) (v p) (coord c p)

def rawMatrix (m : GraphPosition → Bool) (adjoint fourier : Marked m → Bool)
    (coord : C → Marked m → AES.Word) :
    (OutputMarked m → AES.Word) → (InputMarked m → AES.Word) → ℝ :=
  WordOperatorDuality.reshape m (rawResponse m adjoint fourier coord)

/-- Both encodings retain the same source point in the exact matrix sum. -/
theorem rawMatrix_factorization (m : GraphPosition → Bool)
    (adjoint fourier : Marked m → Bool) (coord : C → Marked m → AES.Word) :
    rawMatrix m adjoint fourier coord =
      kernelCompose (outputEncoding m adjoint fourier coord)
        (RectangularBounds.transpose (inputEncoding m adjoint fourier coord)) := by
  funext y x
  unfold rawMatrix WordOperatorDuality.reshape rawResponse kernelCompose
  apply Finset.sum_congr rfl
  intro c _
  unfold outputEncoding inputEncoding encodingKernel RectangularBounds.transpose
  rw [WordMarkedSplit.prod_positions]
  simp only [WordMarkedSplit.join_output, WordMarkedSplit.join_input]

/-- The two signed-source encoding bounds compose through a genuine
matrix transpose; no independent-source premise occurs. -/
theorem rawMatrix_bound (m : GraphPosition → Bool)
    (adjoint fourier : Marked m → Bool) (coord : C → Marked m → AES.Word)
    (idxO : A ⊕ JO ≃ OutputMarked m) (idxI : B ⊕ JI ≃ InputMarked m)
    (heO : Function.Bijective (fun c : C => fun a : A =>
      coord c (outputPosition m (idxO (Sum.inl a)))))
    (heI : Function.Bijective (fun c : C => fun b : B =>
      coord c (inputPosition m (idxI (Sum.inl b))))) :
    EnergyBound (rawMatrix m adjoint fourier coord)
      (sideCoefficient A JO * sideCoefficient B JI) := by
  have ho := WordEncodingOperator.encoding_energyBound
    (fun o => adjoint (outputPosition m o)) (fun o => fourier (outputPosition m o))
    (fun c o => coord c (outputPosition m o)) idxO heO
  have hi := WordEncodingOperator.encoding_energyBound
    (fun i => adjoint (inputPosition m i)) (fun i => fourier (inputPosition m i))
    (fun c i => coord c (inputPosition m i)) idxI heI
  rw [rawMatrix_factorization]
  exact RectangularBounds.energyBound_compose _ _ (sideCoefficient A JO)
    (sideCoefficient B JI) ho (RectangularBounds.energyBound_transpose _ _ hi)

end CommonSource

def primalCoordinates (m : GraphPosition → Bool) (s : Activity m → Bool) :
    Source m s → Marked m → AES.Word :=
  sourceCoordinates GroupedRecurrence.boundary.toAddMonoidHom m s

abbrev DualSource (m : GraphPosition → Bool) (s : Activity m → Bool) :=
  (WordFourierCore.wordPairing.product (Marked m)).annihilator (WordMarkedCode.markedCode m s)

def dualCoordinates (m : GraphPosition → Bool) (s : Activity m → Bool) :
    DualSource m s → Marked m → AES.Word := fun c => c.val

theorem outputPosition_injective (m : GraphPosition → Bool) :
    Function.Injective (outputPosition m) := by
  intro i j h
  apply Subtype.ext
  exact Sum.inl.inj (congrArg Subtype.val h)

theorem inputPosition_injective (m : GraphPosition → Bool) :
    Function.Injective (inputPosition m) := by
  intro i j h
  apply Subtype.ext
  exact Sum.inr.inj (congrArg Subtype.val h)

section PhysicalSelections
variable {A : Type*} [Fintype A]

/-- The selected physical output restriction of the actual primal source. -/
theorem primal_output_projection_bijective (m : GraphPosition → Bool)
    (s : Activity m → Bool) (p : A → OutputMarked m) (hp : Function.Injective p)
    (hsize : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card A = 4) :
    Function.Bijective (fun c : Source m s => fun a : A =>
      primalCoordinates m s c (outputPosition m (p a))) := by
  apply WordMarkedMoment.actual_selected_projection_bijective m s
    (fun a => outputPosition m (p a)) _ hsize
  intro a b h
  exact hp (outputPosition_injective m h)

theorem primal_input_projection_bijective (m : GraphPosition → Bool)
    (s : Activity m → Bool) (p : A → InputMarked m) (hp : Function.Injective p)
    (hsize : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card A = 4) :
    Function.Bijective (fun c : Source m s => fun a : A =>
      primalCoordinates m s c (inputPosition m (p a))) := by
  apply WordMarkedMoment.actual_selected_projection_bijective m s
    (fun a => inputPosition m (p a)) _ hsize
  intro a b h
  exact hp (inputPosition_injective m h)

/-- The selected physical output restriction of the actual annihilator. -/
theorem dual_output_projection_bijective (m : GraphPosition → Bool)
    (s : Activity m → Bool) (p : A → OutputMarked m) (hp : Function.Injective p)
    (hsize : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      (Fintype.card (Marked m) - Fintype.card A) = 4) :
    Function.Bijective (fun c : DualSource m s => fun a : A =>
      dualCoordinates m s c (outputPosition m (p a))) := by
  apply WordMarkedCode.actual_dual_projection_bijective m s
    (fun a => outputPosition m (p a)) _ hsize
  intro a b h
  exact hp (outputPosition_injective m h)

theorem dual_input_projection_bijective (m : GraphPosition → Bool)
    (s : Activity m → Bool) (p : A → InputMarked m) (hp : Function.Injective p)
    (hsize : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      (Fintype.card (Marked m) - Fintype.card A) = 4) :
    Function.Bijective (fun c : DualSource m s => fun a : A =>
      dualCoordinates m s c (inputPosition m (p a))) := by
  apply WordMarkedCode.actual_dual_projection_bijective m s
    (fun a => inputPosition m (p a)) _ hsize
  intro a b h
  exact hp (inputPosition_injective m h)

end PhysicalSelections

section ActualBounds
variable {A B JO JI : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype JO] [DecidableEq JO]
  [Fintype JI] [DecidableEq JI]

theorem primal_raw_bound (m : GraphPosition → Bool) (s : Activity m → Bool)
    (adjoint fourier : Marked m → Bool)
    (idxO : A ⊕ JO ≃ OutputMarked m) (idxI : B ⊕ JI ≃ InputMarked m)
    (hO : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card A = 4)
    (hI : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card B = 4) :
    EnergyBound (rawMatrix m adjoint fourier (primalCoordinates m s))
      (sideCoefficient A JO * sideCoefficient B JI) := by
  apply rawMatrix_bound m adjoint fourier (primalCoordinates m s) idxO idxI
  · exact primal_output_projection_bijective m s (fun a => idxO (Sum.inl a))
      (fun _ _ h => Sum.inl.inj (idxO.injective h)) hO
  · exact primal_input_projection_bijective m s (fun a => idxI (Sum.inl a))
      (fun _ _ h => Sum.inl.inj (idxI.injective h)) hI

theorem dual_raw_bound (m : GraphPosition → Bool) (s : Activity m → Bool)
    (adjoint fourier : Marked m → Bool)
    (idxO : A ⊕ JO ≃ OutputMarked m) (idxI : B ⊕ JI ≃ InputMarked m)
    (hO : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      (Fintype.card (Marked m) - Fintype.card A) = 4)
    (hI : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      (Fintype.card (Marked m) - Fintype.card B) = 4) :
    EnergyBound (rawMatrix m adjoint fourier (dualCoordinates m s))
      (sideCoefficient A JO * sideCoefficient B JI) := by
  apply rawMatrix_bound m adjoint fourier (dualCoordinates m s) idxO idxI
  · exact dual_output_projection_bijective m s (fun a => idxO (Sum.inl a))
      (fun _ _ h => Sum.inl.inj (idxO.injective h)) hO
  · exact dual_input_projection_bijective m s (fun a => idxI (Sum.inl a))
      (fun _ _ h => Sum.inl.inj (idxI.injective h)) hI

/-- The actual primal response contributes one inverse 65536 per uniform
activity choice, with no probability-density normalization. -/
theorem boundary_primal_factorization (m : GraphPosition → Bool) (s : Activity m → Bool) :
    WordOperatorDuality.reshape m (WordMarkedResponse.boundaryContractedResponse m s) =
      fun y x => (1 / (65536 : ℝ)^uniformCount s) *
        rawMatrix m (WordShorteningBridge.inputAdjoint m) (fun _ => false)
          (primalCoordinates m s) y x := by
  funext y x
  change WordMarkedResponse.boundaryContractedResponse m s (join m y x) = _
  rw [WordMarkedResponse.boundaryContractedResponse_shortened,
    WordShorteningBridge.wordMarkedLeg_eq_variant]
  change rawMatrix m (WordShorteningBridge.inputAdjoint m) (fun _ => false)
      (primalCoordinates m s) y x / (65536 : ℝ)^uniformCount s = _
  ring

theorem boundary_primal_bound (m : GraphPosition → Bool) (s : Activity m → Bool)
    (idxO : A ⊕ JO ≃ OutputMarked m) (idxI : B ⊕ JI ≃ InputMarked m)
    (hO : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card A = 4)
    (hI : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      Fintype.card B = 4) :
    EnergyBound
      (WordOperatorDuality.reshape m (WordMarkedResponse.boundaryContractedResponse m s))
      ((1 / (65536 : ℝ)^uniformCount s) * (sideCoefficient A JO * sideCoefficient B JI)) := by
  rw [boundary_primal_factorization]
  exact RectangularBounds.energyBound_scale _ _ _
    (primal_raw_bound m s (WordShorteningBridge.inputAdjoint m) (fun _ => false)
      idxO idxI hO hI)

/-- Fourier transport supplies the actual raw annihilator and its exact
zero-count scalar before the two physical encodings are bounded. -/
theorem boundary_dual_bound (m : GraphPosition → Bool) (s : Activity m → Bool)
    (d : ℕ) (hd : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) + d = 4)
    (hle : d ≤ Fintype.card (Marked m))
    (idxO : A ⊕ JO ≃ OutputMarked m) (idxI : B ⊕ JI ≃ InputMarked m)
    (hO : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      (Fintype.card (Marked m) - Fintype.card A) = 4)
    (hI : AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s) +
      (Fintype.card (Marked m) - Fintype.card B) = 4) :
    EnergyBound
      (WordOperatorDuality.reshape m (WordMarkedResponse.boundaryContractedResponse m s))
      ((1 / (65536 : ℝ)^(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))) *
        (sideCoefficient A JO * sideCoefficient B JI)) := by
  apply (WordOperatorDuality.boundary_raw_dual_bound_iff m s d hd hle _).mpr
  change EnergyBound (fun y x =>
    (1 / (65536 : ℝ)^(AES.maskSize (outputZeros m s) + AES.maskSize (inputZeros m s))) *
      rawMatrix m (WordShorteningBridge.inputAdjoint m) (fun _ => true)
        (dualCoordinates m s) y x) _
  exact RectangularBounds.energyBound_scale _ _ _
    (dual_raw_bound m s (WordShorteningBridge.inputAdjoint m) (fun _ => true)
      idxO idxI hO hI)

end ActualBounds
end AESPaper.WordPhysicalEncoding
