import AES8.Math.Imports

/-!
# Frozen paper's rational fixed-position graph arrays

Source: paper-merged f902bb94, sections 16-graph-bounds and
16-component-calculations. These are definitions of rational certificates,
not operator norm estimates and not a physical AES instantiation.

The Q^3-scaled return candidates below are the exact monomial simplifications
of the incidence/overlap and whole-graph formulas. Powers of sqrt Q are integer
powers. Thin candidates retain the prescribed 1600/Q mixed-moment rounding
before taking a minimum (only c=3 has the irrational mixed root).
-/

open scoped BigOperators
namespace AES8.PaperComparison

abbrev QProfile := Fin 14 → ℚ
abbrev QMatrix := Fin 14 → Fin 14 → ℚ

def q : ℚ := 4294967296
def sqrtQ : ℚ := 65536
def xi : ℚ := 1 / sqrtQ
def eta : ℚ := q / (q - 1)
def C : ℚ := 52 / 5
def E : ℚ := 183 / 500
def H : ℚ := 326 / 5
/-- Q^(n/2), for signed twice-exponent n. -/
def qp (n : ℤ) : ℚ := sqrtQ ^ n

/-- Literal strict shortening predicate, written without truncated subtraction. -/
def survives (n d : ℕ) : Prop := 0 < d ∧ d < n
instance (n d : ℕ) : Decidable (survives n d) := inferInstanceAs (Decidable (0 < d ∧ d < n))

/-- Q-scaled fixed-position one-step graph array, eq. step-closed-form.
The exponent simplifies using nu=C/sqrtQ and sqrt(energy)=E/sqrtQ. -/
def stepGraph (i a j b : ℕ) : ℚ :=
  let n := i + j
  let d := a + b + n - 4
  let s := min d (n - d)
  let r := min i s
  let z := min s (min i j)
  if survives n d then C ^ r * E ^ (i-r) * qp ((j : ℤ)-2-z) else 0

/-- Scaled information-set overlap, eq. aesasm-overlap-large. -/
def overlapLarge (i j c s t r z af bf : ℕ) : ℚ :=
  let m := min (c-s) af
  let n := min (c-t) bf
  C ^ (r+s+t-c) * E ^ (i-r+2*c-s-t-m-n) * H ^ (m+n) *
    qp ((j : ℤ)+c-2-r-z-m-n)

/-- Scaled equal-Fourier-bit HS candidate, eq. aesasm-overlap-hs. -/
def overlapHS (i j c s t r z : ℕ) : ℚ :=
  let hi := max s t
  let lo := min s t
  C ^ r * E ^ (i-r+hi-lo) * H ^ lo * 27 ^ (c-hi) *
    qp ((j : ℤ)+hi-2-r-z)

/-- Rational scaled line and line/plane candidates. All resource roots cancel;
for two mixed fibers at c=4 the exact product 2100*1200 is retained. -/
def overlapThin (i j c s t r af bf : ℕ) (same : Bool) : ℚ :=
  let R : ℚ := if same then 27 else 2100
  let S : ℚ := if same then 27 else 1200
  let D : ℚ := if same then 27 else 1600
  if s = 1 ∧ t = 1 then
    let k := af + bf
    let coeff := if k = 0 then E^2 * R^(c-2)
      else if k = 1 then E*H*(if c = 3 then D else R*S)
      else H^2*S^(c-2)
    C^r * E^(i-r) * coeff * qp ((j : ℤ)-2)
  else
    let aa := if s = 1 then af else bf
    let bb := if s = 1 then bf else af
    let coeff := if aa = 0 then
      (if bb = 0 then R*E^3 else if bb = 1 then S*E^2*H else E^3*H)
      else (if bb = 0 then R*E^2*H else if bb = 1 then S*E*H^2 else E^2*H^2)
    C^r * E^(i-r) * coeff * qp ((j : ℤ)-2+(if bb = 2 then 1 else 0))

/-- Scaled whole-graph candidate, eq. aesasm-whole-graph. -/
def wholeGraph (i j c s z : ℕ) : ℚ :=
  300^s * E^(i+c-2*s) * qp ((j : ℤ)+c-2-s-z)

/-- Q^3 times the common fixed-position return minimum. Strict shortening,
smaller representation, Fourier bits and applicable candidates are literal. -/
def returnTerm (i a j b c mu lam : ℕ) : ℚ :=
  let dl := a+mu+i+c-4
  let dr := b+lam+j+c-4
  let s := min dl (i+c-dl)
  let t := min dr (j+c-dr)
  let r := min i s
  let z := min j t
  let af := s-r
  let bf := t-z
  let same := decide ((2*dl > i+c) ↔ (2*dr > j+c))
  let primary := if s+t ≥ c then overlapLarge i j c s t r z af bf
    else overlapThin i j c s t r af bf same
  let overlap := if same then min primary (overlapHS i j c s t r z) else primary
  if survives (i+c) dl ∧ survives (j+c) dr then
    min (wholeGraph i j c s z) overlap else 0

/-- The five actual summands, including the single shared activity metric. -/
def returnGraph (i a j b : ℕ) : ℚ :=
  4*eta*(returnTerm i a j b 3 0 0 + xi*returnTerm i a j b 3 0 1 +
    xi*returnTerm i a j b 3 1 0 + returnTerm i a j b 3 1 1) +
    returnTerm i a j b 4 0 0

/-- Exact-support expansion, eq. aesasm-support-sum. -/
def supportSum (i t j w : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℚ) : ℚ :=
  ∑ a ∈ Finset.range (t-i+1), ∑ b ∈ Finset.range (w-j+1),
    (Nat.choose (t-i) a : ℚ) * Nat.choose (w-j) b *
      xi^(t-i+w-j-a-b) * f i a j b

def positionCount (i t : ℕ) : ℕ := Nat.choose 4 t * Nat.choose t i

def rootUpper : ℕ → ℚ
  | 1 => 1
  | 4 => 2
  | 6 => 24495/10000
  | 12 => 34642/10000
  | _ => 0

/-- The common rational support lift, eq. rational-support-bound. -/
def support (i t j w : ℕ) (f : ℕ → ℕ → ℕ → ℕ → ℚ) : ℚ :=
  rootUpper (positionCount i t) * rootUpper (positionCount j w) *
    eta^(t-i+w-j) * supportSum i t j w f

/-- Rounded resource roots and mixed moment really satisfy their squared caps. -/
theorem rational_resource_checks :
    sqrtQ^2 = q ∧ (E^2 > (2:ℚ)/15) ∧ (H^2 > 4251) ∧
      (2100:ℚ)*1200 < 1600^2 ∧
      6 ≤ (rootUpper 6)^2 ∧ 12 ≤ (rootUpper 12)^2 := by
  norm_num [sqrtQ, q, E, H, rootUpper]

end AES8.PaperComparison
