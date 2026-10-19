import AESPaper.StartingWordDegrees
import AESPaper.SingleByteSourceDegrees
import AESPaper.BoundarySourceCoordinates
import AESConcrete.WordDegreeOperator
import AESMixing.DegreeMatrixNorm

/-!
# Actual residual second response from source byte-degree envelopes

The input degree and output degree are byte degrees inside one word. The
actual residual AES channel is bounded block by block, retaining the norm
of each projected input. Its five output degrees are then assembled by
orthogonality. No factorization of an arbitrary joint source is assumed.

The generic composition accepts all five source-energy estimates. The
actual specializations supply them from the separate actual source-degree
modules for every nonzero input word, including its physical boundary
coordinate maps. No complete startup profile or full mixing theorem is
claimed here.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.SecondResponse
open AESMixing AESConcrete
open AESPaper.StartingWord (q wordLaw)
open AESPaper.StartingWordDegrees (centeredWordLaw byteDegreeEnergy inputByteWeight)
open AESPaper.SourceNumbers (sourceZ responseY)
open AESConcrete.WordMomentNumbers (op)

abbrev Byte := BinaryWord 8

/-- The actual whole-word residual channel, including its activity removal. -/
def response (f : AES.Word → ℝ) : AES.Word → ℝ :=
  action (residualMatrix AES.wordSuperboxKernel 0) f

theorem q_pos : 0 < q := by norm_num [q]

/-- Scalar conversion uses exactly sqrt(q)=65536 and counting-measure energy. -/
theorem scaled_l2_le_of_energy (f : AES.Word → ℝ) (Z : ℝ) (hZ : 0 ≤ Z)
    (h : q * (∑ y, f y ^ 2) ≤ Z ^ 2) :
    65536 * l2 f ≤ Z := by
  apply (sq_le_sq₀ (mul_nonneg (by norm_num) (l2_nonneg f)) hZ).mp
  calc
    (65536 * l2 f) ^ 2 = q * (∑ y, f y ^ 2) := by
      rw [mul_pow, l2_sq]
      norm_num [q]
    _ ≤ Z ^ 2 := h

/-- The retained input projection avoids replacing its norm by the total norm. -/
theorem degree_block_l2 (i j : Fin 5) (f : AES.Word → ℝ) :
    l2 (degreeComponent (0 : Byte) i
      (response (degreeComponent (0 : Byte) j f))) ≤
      (op i j / 65536) * l2 (degreeComponent (0 : Byte) j f) := by
  have h := WordDegreeOperator.residual_block_table_l2 .ordinary .ordinary false
    i j (degreeComponent (0 : Byte) j f)
  rw [DegreeHilbertSchmidt.block_action, WordDegreeOperator.degree_idempotent,
    WordOrientationClosure.ordinary_word_kernel] at h
  exact h

/-- The source envelope and the actual residual degree blocks give each Y entry. -/
theorem degree_response_l2_le (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 4)
    (f : AES.Word → ℝ)
    (hf : ∀ j : Fin 5, q * (∑ y, degreeComponent (0 : Byte) j f y ^ 2) <
      sourceZ t j ^ 2) (i : Fin 5) :
    q * l2 (degreeComponent (0 : Byte) i (response f)) ≤ responseY t i := by
  have hsource (j : Fin 5) :
      65536 * l2 (degreeComponent (0 : Byte) j f) ≤ sourceZ t j :=
    scaled_l2_le_of_energy _ _ (SourceNumbers.sourceZ_pos t ht j).le (hf j).le
  have hblock (j : Fin 5) :
      q * l2 (degreeComponent (0 : Byte) i
        (response (degreeComponent (0 : Byte) j f))) ≤ op i j * sourceZ t j := by
    calc
      _ ≤ q * ((op i j / 65536) * l2 (degreeComponent (0 : Byte) j f)) :=
        mul_le_mul_of_nonneg_left (degree_block_l2 i j f) q_pos.le
      _ = op i j * (65536 * l2 (degreeComponent (0 : Byte) j f)) := by
        norm_num [q] <;> ring
      _ ≤ op i j * sourceZ t j :=
        mul_le_mul_of_nonneg_left (hsource j) (WordMomentNumbers.op_nonneg i j)
  have htriangle :
      l2 (degreeComponent (0 : Byte) i (response f)) ≤
        ∑ j : Fin 5, l2 (degreeComponent (0 : Byte) i
          (response (degreeComponent (0 : Byte) j f))) := by
    rw [response, degree_action_decomposition (0 : Byte)]
    exact l2_finset_sum_le Finset.univ
      (fun j => degreeComponent (0 : Byte) i
        (action (residualMatrix AES.wordSuperboxKernel 0)
          (degreeComponent (0 : Byte) j f)))
  calc
    _ ≤ q * ∑ j : Fin 5, l2 (degreeComponent (0 : Byte) i
        (response (degreeComponent (0 : Byte) j f))) :=
      mul_le_mul_of_nonneg_left htriangle q_pos.le
    _ = ∑ j : Fin 5, q * l2 (degreeComponent (0 : Byte) i
        (response (degreeComponent (0 : Byte) j f))) := by rw [Finset.mul_sum]
    _ ≤ ∑ j : Fin 5, op i j * sourceZ t j :=
      Finset.sum_le_sum (fun j _ => hblock j)
    _ ≤ responseY t i := SourceNumbers.op_sourceZ_le t ht i

/-- Orthogonality of the five output byte degrees yields the strict 49/5 cap. -/
theorem response_energy_lt (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 4)
    (f : AES.Word → ℝ)
    (hf : ∀ j : Fin 5, q * (∑ y, degreeComponent (0 : Byte) j f y ^ 2) <
      sourceZ t j ^ 2) :
    (∑ y, response f y ^ 2) < 49 / (5 * q ^ 2) := by
  have hi (i : Fin 5) :
      q ^ 2 * (∑ y, degreeComponent (0 : Byte) i (response f) y ^ 2) ≤
        responseY t i ^ 2 := by
    have hs := mul_self_le_mul_self
      (mul_nonneg q_pos.le (l2_nonneg _)) (degree_response_l2_le t ht f hf i)
    simpa only [← pow_two, mul_pow, l2_sq] using hs
  have htotal : q ^ 2 * (∑ y, response f y ^ 2) < 49 / 5 := by
    calc
      _ = ∑ i : Fin 5, q ^ 2 *
          (∑ y, degreeComponent (0 : Byte) i (response f) y ^ 2) := by
        rw [← degreeComponent_pythagoras (0 : Byte)
          (by norm_num [BinaryWord.card]) (response f), Finset.mul_sum]
      _ ≤ ∑ i : Fin 5, responseY t i ^ 2 :=
        Finset.sum_le_sum (fun i _ => hi i)
      _ < 49 / 5 := SourceNumbers.responseY_sq_sum_lt t ht
  apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 5) (pow_pos q_pos 2))).2
  nlinarith

/-- Coordinate maps preserve every input energy; no channel invariance is used. -/
theorem transported_response_energy_lt
    (p : Equiv.Perm (Fin 4)) (e : Fin 4 → Equiv.Perm Byte)
    (he : ∀ i, e i 0 = 0) (t : ℕ) (ht : 1 ≤ t ∧ t ≤ 4)
    (f : AES.Word → ℝ)
    (hf : ∀ j : Fin 5, q * (∑ y, degreeComponent (0 : Byte) j f y ^ 2) <
      sourceZ t j ^ 2) :
    (∑ y, response (lawRelabel (ByteCoordinateTransport.coordinateEquiv p e) f) y ^ 2) <
      49 / (5 * q ^ 2) := by
  apply response_energy_lt t ht
  intro j
  rw [ByteCoordinateTransport.degree_energy_transport p e (0 : Byte) he]
  exact hf j

/-- Actual multi-active source row: all source-energy premises are discharged. -/
theorem actual_centered_multi_energy_lt (a : AES.Word) (ha : a ≠ 0)
    (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (hw : inputByteWeight a = t) :
    (∑ y, response (centeredWordLaw a) y ^ 2) < 49 / (5 * q ^ 2) := by
  exact response_energy_lt t (by omega) (centeredWordLaw a)
    (fun j => StartingWordDegrees.source_degree_energy_lt_multi a ha t ht hw j)

theorem transported_centered_multi_energy_lt
    (p : Equiv.Perm (Fin 4)) (e : Fin 4 → Equiv.Perm Byte)
    (he : ∀ i, e i 0 = 0) (a : AES.Word) (ha : a ≠ 0)
    (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (hw : inputByteWeight a = t) :
    (∑ y, response (lawRelabel (ByteCoordinateTransport.coordinateEquiv p e)
      (centeredWordLaw a)) y ^ 2) < 49 / (5 * q ^ 2) := by
  exact transported_response_energy_lt p e he t (by omega) (centeredWordLaw a)
    (fun j => StartingWordDegrees.source_degree_energy_lt_multi a ha t ht hw j)

theorem response_sub (f g : AES.Word → ℝ) :
    response (f-g) = response f-response g := action_sub _ f g

/-- The uniform nonzero-word reference is killed by the actual residual channel. -/
theorem response_uniformExcept : response (uniformExcept (0 : AES.Word)) = 0 := by
  have hu : wordAverage (0 : AES.Word) (uniformExcept (0 : AES.Word)) =
      uniformExcept (0 : AES.Word) := by
    rw [← activityMatrix_action]
    exact StartingWordDegrees.pointed_uniformExcept
      (activityMatrix_pointed (0 : AES.Word) AESConcrete.AES.word_card_gt_one)
  rw [response, residualMatrix_action AES.word_superbox_pointed,
    wordResidual, hu, sub_self]
  funext y
  simp only [action, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem lawRelabel_sub (E : Equiv.Perm AES.Word) (f g : AES.Word → ℝ) :
    lawRelabel E (f-g) = lawRelabel E f-lawRelabel E g := rfl

/-- Centering is invisible to a second residual response after a zero-fixing map. -/
theorem response_relabel_centered (E : Equiv.Perm AES.Word) (hE : E 0 = 0)
    (a : AES.Word) :
    response (lawRelabel E (centeredWordLaw a)) = response (lawRelabel E (wordLaw a)) := by
  rw [centeredWordLaw, lawRelabel_sub, lawRelabel_uniformExcept E 0 hE,
    response_sub, response_uniformExcept, sub_zero]

/-- The actual uncentered word column satisfies the desired second response
after every byte-position/value map in the proved transport interface. -/
theorem transported_multi_energy_lt
    (p : Equiv.Perm (Fin 4)) (e : Fin 4 → Equiv.Perm Byte)
    (he : ∀ i, e i 0 = 0) (a : AES.Word) (ha : a ≠ 0)
    (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (hw : inputByteWeight a = t) :
    (∑ y, response (lawRelabel (ByteCoordinateTransport.coordinateEquiv p e)
      (wordLaw a)) y ^ 2) < 49 / (5 * q ^ 2) := by
  rw [← response_relabel_centered (ByteCoordinateTransport.coordinateEquiv p e)
    (ByteCoordinateTransport.coordinateEquiv_const p e (0 : Byte) he) a]
  exact transported_centered_multi_energy_lt p e he a ha t ht hw

/-- Specialization to the physical single-word source at boundary output c. -/
theorem boundary_multi_energy_lt (k c : Fin 4) (a : AES.Word) (ha : a ≠ 0)
    (t : ℕ) (ht : 2 ≤ t ∧ t ≤ 4) (hw : inputByteWeight a = t) :
    (∑ y, response (lawRelabel (BoundarySourceCoordinates.outputEquiv k c)
      (wordLaw a)) y ^ 2) < 49 / (5 * q ^ 2) := by
  exact transported_multi_energy_lt (BoundarySourceCoordinates.positionPerm k c)
    (BoundarySourceCoordinates.bytePerm k c) (BoundarySourceCoordinates.bytePerm_zero k c)
    a ha t ht hw

/-- Every nonzero actual source has the second-response bound after an
arbitrary byte-position/value map fixing zero in each coordinate. -/
theorem transported_source_energy_lt
    (p : Equiv.Perm (Fin 4)) (e : Fin 4 → Equiv.Perm Byte)
    (he : ∀ i, e i 0 = 0) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, response (lawRelabel (ByteCoordinateTransport.coordinateEquiv p e)
      (wordLaw a)) y ^ 2) < 49 / (5 * q ^ 2) := by
  rw [← response_relabel_centered (ByteCoordinateTransport.coordinateEquiv p e)
    (ByteCoordinateTransport.coordinateEquiv_const p e (0 : Byte) he) a]
  exact transported_response_energy_lt p e he (inputByteWeight a)
    (StartingWordDegrees.inputByteWeight_range a ha) (centeredWordLaw a)
    (fun j => SingleByteSourceDegrees.source_degree_energy_lt a ha j)

/-- The actual boundary output maps are in the proved transport interface,
so this specialization has no source-energy or byte-weight premise. -/
theorem boundary_source_energy_lt (k c : Fin 4) (a : AES.Word) (ha : a ≠ 0) :
    (∑ y, response (lawRelabel (BoundarySourceCoordinates.outputEquiv k c)
      (wordLaw a)) y ^ 2) < 49 / (5 * q ^ 2) := by
  exact transported_source_energy_lt (BoundarySourceCoordinates.positionPerm k c)
    (BoundarySourceCoordinates.bytePerm k c) (BoundarySourceCoordinates.bytePerm_zero k c)
    a ha

end AESPaper.SecondResponse
