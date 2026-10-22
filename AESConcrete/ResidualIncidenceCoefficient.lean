import AESConcrete.RefinedWordProjection
import AESMixing.SupportNorm
import AESMixing.ByteIncidenceFormula

/-!
# Exact size coefficients for word-support incidence

Separate candidate extension. The generic coefficient is the existing
shortening sum with the actual support-embedding normalization. Only finite
mask arithmetic is specialized at q=2^32. No vector independence or product
input assumption is made. Constructive mathematics only; no attacks,
manuscript/historical edits, goals, schedules or execution are in scope.
Independent uniform retained keys, whitening, omitted final MixColumns,
ordered distinct pairs and the 10/14/16 target are fixed.
-/

noncomputable section
open scoped BigOperators

namespace AESConcrete.ResidualIncidenceCoefficient
open AESMixing

set_option maxRecDepth 100000

abbrev SelectedSupport (d a : Fin 5) :=
  {p : SupportIndex d.val // AES.maskSize p.val.2 + a.val = 4}

def multiplicity (d a : Fin 5) : ℕ :=
  Nat.choose 4 d.val * Nat.choose (4-d.val) (a.val-d.val)

/-- These are counts of orthogonal support pieces, not state dimensions. -/
theorem selectedSupport_card : ∀ d a : Fin 5, d ≤ a →
    Fintype.card (SelectedSupport d a) = multiplicity d a := by decide

def freeCount (d a e b : Fin 5) : ℕ := (a.val-d.val)+(b.val-e.val)

def sizeSum (m : ℝ) (d a e b : Fin 5) : ℝ :=
  ∑ t ∈ Finset.range (freeCount d a e b+1),
    (Nat.choose (freeCount d a e b) t : ℝ) *
      incidenceNormCoefficient m ((4-a.val)+(4-b.val)+t) d.val e.val

def supportFactor (m : ℝ) (d a : Fin 5) : ℝ :=
  Real.sqrt ((m-1)^(a.val-d.val))

def coefficient (m : ℝ) (d a e b : Fin 5) : ℝ :=
  sizeSum m d a e b / (supportFactor m d a * supportFactor m e b)

def squaredBound (m : ℝ) (d a e b : Fin 5) : ℝ :=
  (multiplicity d a : ℝ) * (multiplicity e b : ℝ) *
    sizeSum m d a e b ^ 2 / (m-1)^freeCount d a e b

def comparisonCap (m : ℝ) (d a e b : Fin 5) : ℝ :=
  Real.sqrt (squaredBound m d a e b)

theorem sizeSum_nonneg (m : ℝ) (d a e b : Fin 5) :
    0 ≤ sizeSum m d a e b := by
  apply Finset.sum_nonneg
  intro t _
  exact mul_nonneg (Nat.cast_nonneg _)
    (incidenceNormCoefficient_nonnegative m _ _ _)

theorem coefficient_nonneg (m : ℝ) (d a e b : Fin 5) :
    0 ≤ coefficient m d a e b :=
  div_nonneg (sizeSum_nonneg m d a e b)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem squaredBound_nonneg (m : ℝ) (hm : 1 ≤ m) (d a e b : Fin 5) :
    0 ≤ squaredBound m d a e b := by
  unfold squaredBound
  exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (sq_nonneg _)) (pow_nonneg (sub_nonneg.mpr hm) _)

theorem comparisonCap_nonneg (m : ℝ) (d a e b : Fin 5) :
    0 ≤ comparisonCap m d a e b := Real.sqrt_nonneg _

theorem comparisonCap_sq (m : ℝ) (hm : 1 ≤ m) (d a e b : Fin 5) :
    comparisonCap m d a e b ^ 2 = squaredBound m d a e b :=
  Real.sq_sqrt (squaredBound_nonneg m hm d a e b)

theorem coefficient_sq (m : ℝ) (hm : 1 ≤ m) (d a e b : Fin 5) :
    coefficient m d a e b ^ 2 =
      sizeSum m d a e b ^ 2 / (m-1)^freeCount d a e b := by
  unfold coefficient supportFactor freeCount
  rw [div_pow, mul_pow, Real.sq_sqrt (pow_nonneg (sub_nonneg.mpr hm) _),
    Real.sq_sqrt (pow_nonneg (sub_nonneg.mpr hm) _), ← pow_add]

theorem multiplicity_coefficient_sq (m : ℝ) (hm : 1 ≤ m) (d a e b : Fin 5) :
    (multiplicity d a : ℝ) * (multiplicity e b : ℝ) *
      coefficient m d a e b ^ 2 = squaredBound m d a e b := by
  rw [coefficient_sq m hm]
  unfold squaredBound
  ring

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

theorem selected_supportFactor (d a : Fin 5) (p : SelectedSupport d a) :
    supportNormFactor V p.val.val.2 p.val.val.1 =
      supportFactor (Fintype.card V) d a := by
  have hs := p.property
  have hd := p.val.property.2
  have he : 4-(AES.maskSize p.val.val.2+AES.maskSize p.val.val.1) =
      a.val-d.val := by omega
  unfold supportNormFactor supportFactor
  rw [he]

theorem selected_shortening_sum (d a e b : Fin 5)
    (p : SelectedSupport d a) (r : SelectedSupport e b) :
    shorteningNormSum (Fintype.card V) p.val.val.2 r.val.val.2
      (unmarkedGraphPositions p.val.val.2 r.val.val.2 p.val.val.1 r.val.val.1)
      p.val.val.1 r.val.val.1 = sizeSum (Fintype.card V) d a e b := by
  have hp := p.property
  have hr := r.property
  have hd := p.val.property.2
  have he := r.val.property.2
  have hpzero : AES.maskSize p.val.val.2 = 4-a.val := by omega
  have hrzero : AES.maskSize r.val.val.2 = 4-b.val := by omega
  have hpfree : 4-(AES.maskSize p.val.val.2+AES.maskSize p.val.val.1) =
      a.val-d.val := by omega
  have hrfree : 4-(AES.maskSize r.val.val.2+AES.maskSize r.val.val.1) =
      b.val-e.val := by omega
  rw [shorteningNormSum_by_size _ _ _ _ _ p.val.property.1 r.val.property.1,
    hpfree, hrfree, hpzero, hrzero, hd, he]
  rfl

theorem selected_coefficient (d a e b : Fin 5)
    (p : SelectedSupport d a) (r : SelectedSupport e b) :
    shorteningNormSum (Fintype.card V) p.val.val.2 r.val.val.2
      (unmarkedGraphPositions p.val.val.2 r.val.val.2 p.val.val.1 r.val.val.1)
      p.val.val.1 r.val.val.1 /
        (supportNormFactor V p.val.val.2 p.val.val.1 *
          supportNormFactor V r.val.val.2 r.val.val.1) =
      coefficient (Fintype.card V) d a e b := by
  rw [selected_shortening_sum d a e b p r,
    selected_supportFactor d a p, selected_supportFactor e b r]
  rfl

/-- q=2^32 is square, so every surviving incidence term is an integer. -/
def wordIncidenceTerm (n d e : ℕ) : ℕ :=
  if 4 ≤ n ∨ n+d+e ≤ 4 then 0 else 65536^((4-(n+d))+(4-(n+e)))

theorem word_incidence_term (n d e : ℕ) :
    incidenceNormCoefficient ((2 : ℝ)^32) n d e = (wordIncidenceTerm n d e : ℝ) := by
  rw [show (2 : ℝ)^32 = 65536^2 by norm_num,
    incidenceNormCoefficient_square 65536 (by norm_num)]
  unfold wordIncidenceTerm
  split_ifs <;> norm_num

/-- This t-indexed form is exactly the size-counted shortening sum. -/
def wordRaw (d a e b : Fin 5) : ℕ :=
  ∑ t ∈ Finset.range (freeCount d a e b+1),
    Nat.choose (freeCount d a e b) t *
      wordIncidenceTerm ((4-a.val)+(4-b.val)+t) d.val e.val

theorem sizeSum_word (d a e b : Fin 5) :
    sizeSum ((2 : ℝ)^32) d a e b = (wordRaw d a e b : ℝ) := by
  unfold sizeSum wordRaw
  simp only [Nat.cast_sum, Nat.cast_mul, word_incidence_term]

def wordSquaredBound (d a e b : Fin 5) : ℝ :=
  (multiplicity d a : ℝ) * (multiplicity e b : ℝ) *
    (wordRaw d a e b : ℝ)^2 / (4294967295 : ℝ)^freeCount d a e b

theorem squaredBound_word (d a e b : Fin 5) :
    squaredBound ((2 : ℝ)^32) d a e b = wordSquaredBound d a e b := by
  unfold squaredBound wordSquaredBound
  rw [sizeSum_word]
  norm_num

end AESConcrete.ResidualIncidenceCoefficient
