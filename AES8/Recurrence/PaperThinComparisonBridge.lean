import AES8.Recurrence.PaperGraphComparisonBridge
import AES8.Reductions.Return.PaperAESOverlapMixedThin

/-!
# Exact scalar joins for the paper's thin overlap choices

Frozen paper f902bb94, `aesasm-overlap-lines` and
`aesasm-overlap-line-plane`. The scalar coefficient definitions below are
literally the coefficients of the ordinary and unequal-bit operator bounds.
They are separate from those operator proofs and from grouped-state assembly.

The only rounding is the three-coordinate, one-full-fiber, unequal-bit line
case: sqrt(2100 * 1200) <= 1600. At four coordinates the exact product
2100 * 1200 is retained. Every line/plane entry is an exact identity.
The same=true formulas are scalar identities; no equal-true 27/q resource
is supplied. Constructive mathematics only; no attacks or manuscript edits.
-/

noncomputable section
namespace AES8.PaperThinComparisonBridge
open AES8.PaperComparison AES8.PaperComparisonPowers

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def rowNumerator (same : Bool) : ℚ := if same then 27 else 2100
def totalNumerator (same : Bool) : ℚ := if same then 27 else 1200
def mixedNumerator (same : Bool) : ℚ := if same then 27 else 1600

def rowScale (same : Bool) : ℝ :=
  if same then PaperAESOverlapResources.entry
  else PaperAESOverlapMixedThin.rowFourthBase

def totalScale (same : Bool) : ℝ :=
  if same then PaperAESOverlapResources.entry
  else PaperAESOverlapMixedThin.totalFourthBase

def lineCap (c a : ℕ) (same : Bool) : ℝ :=
  if a = 0 then PaperAESOverlapResources.delta * rowScale same ^ (c - 2)
  else PaperAESOverlapResources.total * totalScale same ^ (c - 2)

def twoLineCoefficient (c a b : ℕ) (same : Bool) : ℝ :=
  Real.sqrt (lineCap c a same * lineCap c b same /
    (PaperAESOverlapResources.q : ℝ) ^ (a + b))

def linePlaneCoefficient (a b : ℕ) (same : Bool) : ℝ :=
  Real.sqrt ((PaperAESOverlapResources.delta ^ (2 - a) *
      PaperAESOverlapResources.total ^ a *
      PaperThinPlane.planeColCap b PaperAESOverlapResources.delta
        PaperAESOverlapResources.total (rowScale same) (totalScale same)) /
    (PaperAESOverlapResources.q : ℝ) ^ (a + b))

/-- This definition uses the same local moment resources as the actual
ordinary line operator; the equality does not require a new entry bound. -/
theorem twoLineCoefficient_ordinary (c a b : ℕ) :
    twoLineCoefficient c a b true =
      Real.sqrt (PaperAESOverlapThin.lineCap c a *
        PaperAESOverlapThin.lineCap c b /
          (PaperAESOverlapResources.q : ℝ) ^ (a + b)) := rfl

theorem twoLineCoefficient_mixed (c a b : ℕ) :
    twoLineCoefficient c a b false =
      Real.sqrt (PaperAESOverlapMixedThin.lineCap c a *
        PaperAESOverlapMixedThin.lineCap c b /
          (PaperAESOverlapResources.q : ℝ) ^ (a + b)) := rfl

theorem linePlaneCoefficient_ordinary (a b : ℕ) :
    linePlaneCoefficient a b true =
      Real.sqrt ((PaperAESOverlapResources.delta ^ (2 - a) *
        PaperAESOverlapResources.total ^ a *
        PaperThinPlane.planeColCap b PaperAESOverlapResources.delta
          PaperAESOverlapResources.total PaperAESOverlapResources.entry
            PaperAESOverlapResources.entry) /
          (PaperAESOverlapResources.q : ℝ) ^ (a + b)) := rfl

theorem linePlaneCoefficient_mixed (a b : ℕ) :
    linePlaneCoefficient a b false =
      Real.sqrt ((PaperAESOverlapResources.delta ^ (2 - a) *
        PaperAESOverlapResources.total ^ a *
        PaperThinPlane.planeColCap b PaperAESOverlapResources.delta
          PaperAESOverlapResources.total PaperAESOverlapMixedThin.rowFourthBase
            PaperAESOverlapMixedThin.totalFourthBase) /
          (PaperAESOverlapResources.q : ℝ) ^ (a + b)) := rfl

/-- The rational local multiplier, before its alphabet normalizer. -/
def lineNumerator (c a b : ℕ) (same : Bool) : ℚ :=
  if a + b = 0 then E ^ 2 * rowNumerator same ^ (c - 2)
  else if a + b = 1 then
    E * H * (if c = 3 then mixedNumerator same
      else rowNumerator same * totalNumerator same)
  else H ^ 2 * totalNumerator same ^ (c - 2)

def planeNumerator (a b : ℕ) (same : Bool) : ℚ :=
  if a = 0 then
    (if b = 0 then rowNumerator same * E ^ 3
      else if b = 1 then totalNumerator same * E ^ 2 * H else E ^ 3 * H)
  else
    (if b = 0 then rowNumerator same * E ^ 2 * H
      else if b = 1 then totalNumerator same * E * H ^ 2 else E ^ 2 * H ^ 2)

private theorem overlapThin_lines (i j c r a b : ℕ) (same : Bool) :
    overlapThin i j c 1 1 r a b same =
      C ^ r * E ^ (i - r) * lineNumerator c a b same * qp ((j : ℤ) - 2) := rfl

private theorem overlapThin_line_plane (i j r a b : ℕ) (same : Bool) :
    overlapThin i j 4 1 2 r a b same =
      C ^ r * E ^ (i - r) * planeNumerator a b same *
        qp ((j : ℤ) - 2 + (if b = 2 then 1 else 0)) := rfl

private theorem overlapThin_plane_line (i j r a b : ℕ) (same : Bool) :
    overlapThin i j 4 2 1 r a b same =
      C ^ r * E ^ (i - r) * planeNumerator b a same *
        qp ((j : ℤ) - 2 + (if a = 2 then 1 else 0)) := rfl

/-- The literal incidence product, collected into its rational monomial.
Only r=min(i,s) needs a subtraction premise, supplied by the minimum. -/
theorem incidence_product_eq (i j c s t : ℕ) :
    (q : ℝ) ^ 3 * PaperAESIncidence.leftFactor i c s *
      PaperAESIncidence.rightFactor j c t =
    ((C ^ min i s * E ^ (i - min i s) *
      qp ((j : ℤ) + 2 * c - 2 - min i s - min j t) : ℚ) : ℝ) := by
  rw [PaperGraphComparisonBridge.incidence_product]
  let r := min i s
  let z := min j t
  have hr : r ≤ i := Nat.min_le_left _ _
  have he : ((i - r : ℕ) : ℝ) = (i : ℝ) - r := Nat.cast_sub hr
  have hz : (((i : ℤ) + j + 2 * c - 2 - r - z : ℤ) : ℝ) =
      (i : ℝ) + j + 2 * c - 2 - r - z := by push_cast; rfl
  have h := certificate_monomial C E 1 (by norm_num [E]) (by norm_num)
    r (i - r) 0 ((i : ℤ) + j + 2 * c - 2 - r - z)
  simp only [Nat.cast_zero, zero_div, Real.rpow_eq_pow, Real.rpow_zero, mul_one, pow_zero] at h
  rw [he, hz] at h
  have hex : (i : ℤ) + j + 2 * c - 2 - r - z - r - (i - r : ℕ) - 0 =
      (j : ℤ) + 2 * c - 2 - r - z := by
    rw [Int.ofNat_sub hr]
    ring
  rw [hex] at h
  simpa only [Real.rpow_eq_pow, r, z, mul_comm, mul_left_comm, mul_assoc] using h

private theorem incidence_nonneg (i j c s t : ℕ) :
    0 ≤ (q : ℝ) ^ 3 * PaperAESIncidence.leftFactor i c s *
      PaperAESIncidence.rightFactor j c t := by
  rw [incidence_product_eq]
  have h : (0 : ℚ) ≤ C ^ min i s * E ^ (i - min i s) *
      qp ((j : ℤ) + 2 * c - 2 - min i s - min j t) := by
    unfold C E qp sqrtQ
    positivity
  exact_mod_cast h

/-- The only enlarged root in the thin rational array. -/
theorem mixed_root_rounding : Real.sqrt ((2100 : ℝ) * 1200) ≤ 1600 := by
  apply Real.sqrt_le_iff.mpr
  constructor <;> norm_num

/-- All four line-fiber pairs, at c=3 or c=4. The squared comparison is
exact except c=3, a+b=1, same=false, where it is the 1600 rounding. -/
theorem twoLineCoefficient_le (c a b : ℕ) (same : Bool)
    (hc : c = 3 ∨ c = 4) (ha : a ≤ 1) (hb : b ≤ 1) :
    twoLineCoefficient c a b same ≤
      ((lineNumerator c a b same *
        qp (-(2 * (c : ℤ) - 2 + a + b)) : ℚ) : ℝ) := by
  rcases hc with rfl | rfl
  all_goals
    interval_cases a <;> interval_cases b <;> cases same
  all_goals
    unfold twoLineCoefficient
    apply Real.sqrt_le_iff.mpr
    constructor <;>
      norm_num [lineCap, rowScale, totalScale, lineNumerator, rowNumerator,
        totalNumerator, mixedNumerator, qp, sqrtQ, E, H,
        PaperAESOverlapResources.delta, PaperAESOverlapResources.total,
        PaperAESOverlapResources.entry, PaperAESOverlapResources.q,
        PaperAESOverlapMixedThin.rowFourthBase, PaperAESOverlapMixedThin.totalFourthBase]

/-- Outside the single rounded family the line conversion is an equality. -/
theorem twoLineCoefficient_eq (c a b : ℕ) (same : Bool)
    (hc : c = 3 ∨ c = 4) (ha : a ≤ 1) (hb : b ≤ 1)
    (hexact : same = true ∨ c = 4 ∨ a + b ≠ 1) :
    twoLineCoefficient c a b same =
      ((lineNumerator c a b same *
        qp (-(2 * (c : ℤ) - 2 + a + b)) : ℚ) : ℝ) := by
  rcases hc with rfl | rfl
  all_goals
    interval_cases a <;> interval_cases b <;> cases same
  all_goals try { norm_num at hexact }
  all_goals
    unfold twoLineCoefficient
    apply (Real.sqrt_eq_iff_eq_sq
      (by norm_num [lineCap, rowScale, totalScale,
        PaperAESOverlapResources.delta, PaperAESOverlapResources.total,
        PaperAESOverlapResources.entry, PaperAESOverlapResources.q,
        PaperAESOverlapMixedThin.rowFourthBase, PaperAESOverlapMixedThin.totalFourthBase])
      (by norm_num [lineNumerator, rowNumerator, totalNumerator, mixedNumerator,
        qp, sqrtQ, E, H])).mpr
    norm_num [lineCap, rowScale, totalScale, lineNumerator, rowNumerator,
      totalNumerator, mixedNumerator, qp, sqrtQ, E, H,
      PaperAESOverlapResources.delta, PaperAESOverlapResources.total,
      PaperAESOverlapResources.entry, PaperAESOverlapResources.q,
      PaperAESOverlapMixedThin.rowFourthBase, PaperAESOverlapMixedThin.totalFourthBase]

/-- Each of the six line/plane cases is exactly rational after normalization. -/
theorem linePlaneCoefficient_eq (a b : ℕ) (same : Bool)
    (ha : a ≤ 1) (hb : b ≤ 2) :
    linePlaneCoefficient a b same =
      ((planeNumerator a b same *
        qp (-(5 + (a : ℤ) + (if b = 0 then 0 else 1))) : ℚ) : ℝ) := by
  interval_cases a <;> interval_cases b <;> cases same
  all_goals
    unfold linePlaneCoefficient
    apply (Real.sqrt_eq_iff_eq_sq
      (by norm_num [rowScale, totalScale, PaperThinPlane.planeColCap,
        PaperAESOverlapResources.delta, PaperAESOverlapResources.total,
        PaperAESOverlapResources.entry, PaperAESOverlapResources.q,
        PaperAESOverlapMixedThin.rowFourthBase, PaperAESOverlapMixedThin.totalFourthBase])
      (by norm_num [planeNumerator, rowNumerator, totalNumerator, qp, sqrtQ, E, H])).mpr
    norm_num [planeNumerator, rowNumerator, totalNumerator, qp, sqrtQ, E, H,
      rowScale, totalScale, PaperThinPlane.planeColCap,
      PaperAESOverlapResources.delta, PaperAESOverlapResources.total,
      PaperAESOverlapResources.entry, PaperAESOverlapResources.q,
      PaperAESOverlapMixedThin.rowFourthBase, PaperAESOverlapMixedThin.totalFourthBase]

private theorem line_power_join (j c r z a b : ℕ)
    (hrank : r + z + a + b = 2) :
    qp ((j : ℤ) + 2 * c - 2 - r - z) *
      qp (-(2 * (c : ℤ) - 2 + a + b)) = qp ((j : ℤ) - 2) := by
  unfold qp
  rw [← zpow_add₀ (by norm_num [sqrtQ] : sqrtQ ≠ 0)]
  congr 1
  omega

/-- Literal Q^3 incidence factors times the line coefficient. The two rank
equations are the exact outside-fiber dimensions, not analytic premises. -/
theorem lines_product_le (i j c a b : ℕ) (same : Bool)
    (hc : c = 3 ∨ c = 4)
    (ha : min i 1 + a = 1) (hb : min j 1 + b = 1) :
    (q : ℝ) ^ 3 * PaperAESIncidence.leftFactor i c 1 *
      PaperAESIncidence.rightFactor j c 1 * twoLineCoefficient c a b same ≤
      (overlapThin i j c 1 1 (min i 1) a b same : ℝ) := by
  have ha1 : a ≤ 1 := by omega
  have hb1 : b ≤ 1 := by omega
  calc
    _ ≤ ((C ^ min i 1 * E ^ (i - min i 1) *
        qp ((j : ℤ) + 2 * c - 2 - min i 1 - min j 1) : ℚ) : ℝ) *
        ((lineNumerator c a b same *
          qp (-(2 * (c : ℤ) - 2 + a + b)) : ℚ) : ℝ) := by
      rw [← incidence_product_eq]
      exact mul_le_mul_of_nonneg_left
        (twoLineCoefficient_le c a b same hc ha1 hb1) (incidence_nonneg i j c 1 1)
    _ = _ := by
      rw [overlapThin_lines, ← Rat.cast_mul]
      congr 1
      calc
        _ = C ^ min i 1 * E ^ (i - min i 1) * lineNumerator c a b same *
            (qp ((j : ℤ) + 2 * c - 2 - min i 1 - min j 1) *
              qp (-(2 * (c : ℤ) - 2 + a + b))) := by ring
        _ = _ := by rw [line_power_join j c _ _ a b (by omega)]

theorem lines_product_eq (i j c a b : ℕ) (same : Bool)
    (hc : c = 3 ∨ c = 4)
    (ha : min i 1 + a = 1) (hb : min j 1 + b = 1)
    (hexact : same = true ∨ c = 4 ∨ a + b ≠ 1) :
    (q : ℝ) ^ 3 * PaperAESIncidence.leftFactor i c 1 *
      PaperAESIncidence.rightFactor j c 1 * twoLineCoefficient c a b same =
      (overlapThin i j c 1 1 (min i 1) a b same : ℝ) := by
  rw [incidence_product_eq,
    twoLineCoefficient_eq c a b same hc (by omega) (by omega) hexact,
    overlapThin_lines, ← Rat.cast_mul]
  congr 1
  calc
    _ = C ^ min i 1 * E ^ (i - min i 1) * lineNumerator c a b same *
        (qp ((j : ℤ) + 2 * c - 2 - min i 1 - min j 1) *
          qp (-(2 * (c : ℤ) - 2 + a + b))) := by ring
    _ = _ := by rw [line_power_join j c _ _ a b (by omega)]

private theorem plane_product (i j s t a b : ℕ) (same : Bool)
    (ha : a ≤ 1) (hb : b ≤ 2)
    (hrank : min i s + min j t + a + b = 3) :
    (q : ℝ) ^ 3 * PaperAESIncidence.leftFactor i 4 s *
      PaperAESIncidence.rightFactor j 4 t * linePlaneCoefficient a b same =
    ((C ^ min i s * E ^ (i - min i s) * planeNumerator a b same *
      qp ((j : ℤ) - 2 + (if b = 2 then 1 else 0)) : ℚ) : ℝ) := by
  rw [incidence_product_eq, linePlaneCoefficient_eq a b same ha hb, ← Rat.cast_mul]
  have hpower : qp ((j : ℤ) + 2 * 4 - 2 - min i s - min j t) *
      qp (-(5 + (a : ℤ) + (if b = 0 then 0 else 1))) =
      qp ((j : ℤ) - 2 + (if b = 2 then 1 else 0)) := by
    unfold qp
    rw [← zpow_add₀ (by norm_num [sqrtQ] : sqrtQ ≠ 0)]
    congr 1
    split_ifs <;> omega
  congr 1
  calc
    _ = C ^ min i s * E ^ (i - min i s) * planeNumerator a b same *
        (qp ((j : ℤ) + 2 * 4 - 2 - min i s - min j t) *
          qp (-(5 + (a : ℤ) + (if b = 0 then 0 else 1)))) := by ring
    _ = _ := by rw [hpower]

theorem line_plane_product_eq (i j a b : ℕ) (same : Bool)
    (ha : min i 1 + a = 1) (hb : min j 2 + b = 2) :
    (q : ℝ) ^ 3 * PaperAESIncidence.leftFactor i 4 1 *
      PaperAESIncidence.rightFactor j 4 2 * linePlaneCoefficient a b same =
      (overlapThin i j 4 1 2 (min i 1) a b same : ℝ) := by
  rw [overlapThin_line_plane]
  exact plane_product i j 1 2 a b same (by omega) (by omega) (by omega)

/-- The plane-left operator is an actual Hilbert adjoint in the source
module. Its coefficient swaps the line/plane fiber labels here. -/
theorem plane_line_product_eq (i j a b : ℕ) (same : Bool)
    (ha : min i 2 + a = 2) (hb : min j 1 + b = 1) :
    (q : ℝ) ^ 3 * PaperAESIncidence.leftFactor i 4 2 *
      PaperAESIncidence.rightFactor j 4 1 * linePlaneCoefficient b a same =
      (overlapThin i j 4 2 1 (min i 2) a b same : ℝ) := by
  rw [overlapThin_plane_line]
  exact plane_product i j 2 1 b a same (by omega) (by omega) (by omega)

/-- Exactly the thin shapes in the frozen paper. This definition records
dimension applicability only and contains no operator or coefficient bound. -/
def ThinShape (c s t : ℕ) : Prop :=
  (s = 1 ∧ t = 1 ∧ (c = 3 ∨ c = 4)) ∨
    (c = 4 ∧ s = 1 ∧ t = 2) ∨ (c = 4 ∧ s = 2 ∧ t = 1)

def thinCoefficient (c s t a b : ℕ) (same : Bool) : ℝ :=
  if s = 1 ∧ t = 1 then twoLineCoefficient c a b same
  else if s = 1 then linePlaneCoefficient a b same else linePlaneCoefficient b a same

/-- All thin coefficient joins, including the single deliberate rounding.
For actual operators, same=true is supplied by the ordinary source bound;
the equal-true resource remains a separate obligation. -/
theorem thin_product_le (i j c s t a b : ℕ) (same : Bool)
    (hshape : ThinShape c s t)
    (ha : min i s + a = s) (hb : min j t + b = t) :
    (q : ℝ) ^ 3 * PaperAESIncidence.leftFactor i c s *
      PaperAESIncidence.rightFactor j c t * thinCoefficient c s t a b same ≤
      (overlapThin i j c s t (min i s) a b same : ℝ) := by
  rcases hshape with ⟨rfl, rfl, hc⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · simpa [thinCoefficient] using
      lines_product_le i j c a b same hc ha hb
  · simpa [thinCoefficient] using
      (line_plane_product_eq i j a b same ha hb).le
  · simpa [thinCoefficient] using
      (plane_line_product_eq i j a b same ha hb).le

end AES8.PaperThinComparisonBridge
