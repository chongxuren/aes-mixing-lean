import AESPaper.FiniteOutputLaw
import AESPaper.GroupedLaw

/-!
# Explicit finite programs making at most two forward queries

`Program.stop` makes no query. `Program.query x next` makes the first query;
`next` may stop after its answer or make one final query and return an arbitrary
function of that answer. Both stages are total functions and have no further
oracle interface. All private coins and independent prior information can be
included in the finite seed selecting the program.

The operational interpreter performs only the selected queries. Padding is a
proof device: initially stopped programs use input 0 twice; after a one-query
stop, the second padded query repeats the first input. The deterministic decoder
discards every answer obtained after stopping. Repeated active queries are also
allowed, without any distinct-input premise.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AESPaper.TwoQueryProgram
open AESMixing AESPaper.FiniteOutputLaw

inductive Continuation (V O : Type*) where
  | stop (output : O)
  | query (input : V) (finish : V → O)

inductive Program (V O : Type*) where
  | stop (output : O)
  | query (input : V) (next : V → Continuation V O)

variable {V O : Type*}

def runContinuation : Continuation V O → (V → V) → O
  | .stop o, _ => o
  | .query x finish, oracle => finish (oracle x)

def run : Program V O → (V → V) → O
  | .stop o, _ => o
  | .query x next, oracle => runContinuation (next (oracle x)) oracle

def continuationQueries : Continuation V O → ℕ
  | .stop _ => 0
  | .query _ _ => 1

/-- Actual calls made by the operational interpreter, rather than padded calls. -/
def queryCount : Program V O → (V → V) → ℕ
  | .stop _, _ => 0
  | .query x next, oracle => 1 + continuationQueries (next (oracle x))

theorem queryCount_le_two (p : Program V O) (oracle : V → V) :
    queryCount p oracle ≤ 2 := by
  cases p with
  | stop o => norm_num [queryCount]
  | query x next =>
    cases h : next (oracle x) <;> norm_num [queryCount, continuationQueries, h]

theorem run_stop (o : O) (oracle : V → V) :
    run (.stop o) oracle = o ∧ queryCount (.stop o) oracle = 0 := ⟨rfl, rfl⟩

theorem run_after_one (x : V) (next : V → Continuation V O) (oracle : V → V)
    (o : O) (h : next (oracle x) = .stop o) :
    run (.query x next) oracle = o ∧ queryCount (.query x next) oracle = 1 := by
  simp [run, queryCount, h, runContinuation, continuationQueries]

theorem run_after_two (x x' : V) (next : V → Continuation V O)
    (finish : V → O) (oracle : V → V) (h : next (oracle x) = .query x' finish) :
    run (.query x next) oracle = finish (oracle x') ∧
      queryCount (.query x next) oracle = 2 := by
  simp [run, queryCount, h, runContinuation, continuationQueries]

section Padding
variable [Zero V]

def paddedFirst : Program V O → V
  | .stop _ => 0
  | .query x _ => x

def paddedSecond : Program V O → V → V
  | .stop _, _ => 0
  | .query x next, y =>
      match next y with
      | .stop _ => x
      | .query x' _ => x'

def decode : Program V O → (V × V) → O
  | .stop o, _ => o
  | .query _ next, y =>
      match next y.1 with
      | .stop o => o
      | .query _ finish => finish y.2

/-- Answers after either stopping point cannot affect the output. -/
theorem decode_after_stop (o : O) (a b : V × V) :
    decode (.stop o) a = decode (.stop o) b := rfl

theorem decode_after_one (x : V) (next : V → Continuation V O) (y : V)
    (o : O) (h : next y = .stop o) (z z' : V) :
    decode (.query x next) (y, z) = o ∧ decode (.query x next) (y, z') = o := by
  simp [decode, h]

theorem padding_after_one (x : V) (next : V → Continuation V O) (y : V)
    (o : O) (h : next y = .stop o) : paddedSecond (.query x next) y = x := by
  simp [paddedSecond, h]

/-- Deterministic pathwise equality for every oracle, including repeated inputs.
The left side is the interpreter that actually stops; only the right is padded. -/
theorem run_eq_decode_padding (p : Program V O) (oracle : V → V) :
    run p oracle = decode p
      (oracle (paddedFirst p), oracle (paddedSecond p (oracle (paddedFirst p)))) := by
  cases p with
  | stop o => rfl
  | query x next =>
    cases h : next (oracle x) <;>
      simp [run, runContinuation, decode, paddedFirst, paddedSecond, h]

end Padding

section RealLaws
variable [Fintype V] [DecidableEq V] [AddCommGroup V]
  [Fintype O] [DecidableEq O]
  {R K : Type*} [Fintype R] [Fintype K]

def outputDecoder (program : R → Program V O) (view : R × (V × V)) : O :=
  decode (program view.1) view.2

def paddedRealView (E : K → V → V) (keyWeight : K → ℝ) (weight : R → ℝ)
    (program : R → Program V O) : R × (V × V) → ℝ :=
  independentView weight (fun t => retainedAdaptiveLaw E keyWeight
    (paddedFirst (program t)) (paddedSecond (program t)))

/-- Direct experiment: choose the independent private seed and one retained key,
then execute the stopping interpreter. No padded answers occur in this law. -/
def realOutputLaw (E : K → V → V) (keyWeight : K → ℝ) (weight : R → ℝ)
    (program : R → Program V O) (o : O) : ℝ :=
  ∑ t, weight t * pushLaw (fun k => run (program t) (E k)) keyWeight o

theorem retainedAdaptiveLaw_eq_push (E : K → V → V) (keyWeight : K → ℝ)
    (x : V) (choose : V → V) :
    retainedAdaptiveLaw E keyWeight x choose =
      pushLaw (fun k => (E k x, E k (choose (E k x)))) keyWeight := by
  funext y
  rcases y with ⟨y₁, y₂⟩
  simp only [retainedAdaptiveLaw, pushLaw, Prod.mk.injEq,
    mul_ite, mul_one, mul_zero]

/-- Exact real correspondence, from retained-key answers to the stopping output. -/
theorem realOutputLaw_eq_push (E : K → V → V) (keyWeight : K → ℝ)
    (weight : R → ℝ) (program : R → Program V O) :
    realOutputLaw E keyWeight weight program =
      pushLaw (outputDecoder program) (paddedRealView E keyWeight weight program) := by
  funext o
  rw [paddedRealView, pushLaw_independent]
  unfold realOutputLaw
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (fun z : ℝ => weight t * z)
  rw [retainedAdaptiveLaw_eq_push, pushLaw_comp]
  have he : (fun k => outputDecoder program
      (t, (E k (paddedFirst (program t)),
        E k (paddedSecond (program t) (E k (paddedFirst (program t))))))) =
      (fun k => run (program t) (E k)) := by
    funext k
    exact (run_eq_decode_padding (program t) (E k)).symm
  rw [he]

theorem realOutputLaw_nonnegative (E : K → V → V) (keyWeight : K → ℝ)
    (hk : ∀ k, 0 ≤ keyWeight k) (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t)
    (program : R → Program V O) (o : O) :
    0 ≤ realOutputLaw E keyWeight weight program o :=
  Finset.sum_nonneg (fun t _ => mul_nonneg (hw t) (pushLaw_nonnegative _ _ hk o))

theorem realOutputLaw_total (E : K → V → V) (keyWeight : K → ℝ)
    (hk : (∑ k, keyWeight k) = 1) (weight : R → ℝ)
    (hw : (∑ t, weight t) = 1) (program : R → Program V O) :
    (∑ o, realOutputLaw E keyWeight weight program o) = 1 := by
  unfold realOutputLaw
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, pushLaw_total, hk, mul_one, hw]

end RealLaws

section IdealLaws
variable [Fintype V] [DecidableEq V] [AddCommGroup V]
  [Fintype O] [DecidableEq O]
  {R : Type*} [Fintype R]

/-- Difference form of the two-query random-permutation response interface. -/
def permutationDifference (a : V) : V → ℝ :=
  if a = 0 then differencePoint 0 else uniformExcept 0

/-- Lazy ideal answer after the first input x has returned y. -/
def freshRepeat (x x' y : V) : V → ℝ :=
  if x' = x then differencePoint y else uniformExcept y

theorem permutationDifference_eq_response (x x' y y' : V) :
    permutationDifference (x' - x) (y' - y) = freshRepeat x x' y y' := by
  by_cases hx : x' = x <;> by_cases hy : y' = y <;>
    simp [permutationDifference, freshRepeat, hx, hy, differencePoint,
      uniformExcept, sub_eq_zero, eq_comm] <;> aesop

def idealContinuationLaw (x y : V) : Continuation V O → O → ℝ
  | .stop o => differencePoint o
  | .query x' finish => pushLaw finish (freshRepeat x x' y)

/-- Direct stopped ideal experiment. Its first response is uniform; the
continuation either stops immediately or samples a fresh/repeated response. -/
def idealRunLaw : Program V O → O → ℝ
  | .stop o => differencePoint o
  | .query x next => fun o =>
      (∑ y, idealContinuationLaw x y (next y) o) / Fintype.card V

def paddedIdealView (weight : R → ℝ) (program : R → Program V O) :
    R × (V × V) → ℝ :=
  independentView weight (fun t => adaptiveDifferenceView permutationDifference
    (fun y => paddedSecond (program t) y - paddedFirst (program t)))

def idealOutputLaw (weight : R → ℝ) (program : R → Program V O) (o : O) : ℝ :=
  ∑ t, weight t * idealRunLaw (program t) o

theorem ideal_view_push_formula (x : V) (choose : V → V)
    (decodeAnswers : V × V → O) (o : O) :
    pushLaw decodeAnswers
      (adaptiveDifferenceView permutationDifference (fun y => choose y - x)) o =
      (∑ y, pushLaw (fun y' => decodeAnswers (y, y'))
        (freshRepeat x (choose y) y) o) / Fintype.card V := by
  unfold pushLaw adaptiveDifferenceView
  simp only [Fintype.sum_prod_type]
  simp_rw [permutationDifference_eq_response]
  simp only [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro y' _
  by_cases h : decodeAnswers (y, y') = o <;> simp [h]

/-- Exact stopped-ideal correspondence. The initial and one-query stopping
branches remove padded answers by normalization of point masses. -/
theorem idealRunLaw_eq_push (p : Program V O) :
    pushLaw (decode p)
      (adaptiveDifferenceView permutationDifference
        (fun y => paddedSecond p y - paddedFirst p)) = idealRunLaw p := by
  funext o
  rw [ideal_view_push_formula]
  cases p with
  | stop a =>
    change (∑ y : V, pushLaw (fun _ : V => a) (freshRepeat 0 0 y) o) /
      (Fintype.card V : ℝ) = differencePoint a o
    simp only [freshRepeat, ite_true, pushLaw_point]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hn : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card V))
    field_simp [hn]
  | query x next =>
    change (∑ y : V,
      pushLaw (fun y' => decode (.query x next) (y, y'))
        (freshRepeat x (paddedSecond (.query x next) y) y) o) /
      (Fintype.card V : ℝ) =
        (∑ y : V, idealContinuationLaw x y (next y) o) / Fintype.card V
    apply congrArg (fun z : ℝ => z / Fintype.card V)
    apply Finset.sum_congr rfl
    intro y _
    cases h : next y <;>
      simp only [decode, paddedSecond, h, idealContinuationLaw,
        freshRepeat, ite_true, pushLaw_point]

theorem idealOutputLaw_eq_push (weight : R → ℝ) (program : R → Program V O) :
    idealOutputLaw weight program =
      pushLaw (outputDecoder program) (paddedIdealView weight program) := by
  funext o
  rw [paddedIdealView, pushLaw_independent]
  unfold idealOutputLaw
  apply Finset.sum_congr rfl
  intro t _
  apply congrArg (fun z : ℝ => weight t * z)
  exact (congrFun (idealRunLaw_eq_push (program t)) o).symm

theorem freshRepeat_nonnegative (hn : 1 < Fintype.card V) (x x' y y' : V) :
    0 ≤ freshRepeat x x' y y' := by
  have hn' : (1 : ℝ) < Fintype.card V := by exact_mod_cast hn
  unfold freshRepeat differencePoint uniformExcept
  split_ifs <;> positivity

theorem freshRepeat_total (hn : 1 < Fintype.card V) (x x' y : V) :
    (∑ y', freshRepeat x x' y y') = 1 := by
  by_cases hx : x' = x
  · simp [freshRepeat, hx, differencePoint]
  · simpa only [freshRepeat, if_neg hx] using AESPaper.GroupedLaw.uniform_total y hn

theorem idealContinuationLaw_nonnegative (hn : 1 < Fintype.card V)
    (x y : V) (c : Continuation V O) (o : O) : 0 ≤ idealContinuationLaw x y c o := by
  cases c with
  | stop a => simp only [idealContinuationLaw, differencePoint]; split_ifs <;> norm_num
  | query x' finish =>
    exact pushLaw_nonnegative finish _ (freshRepeat_nonnegative hn x x' y) o

theorem idealContinuationLaw_total (hn : 1 < Fintype.card V)
    (x y : V) (c : Continuation V O) : (∑ o, idealContinuationLaw x y c o) = 1 := by
  cases c with
  | stop a => simp [idealContinuationLaw, differencePoint]
  | query x' finish =>
    rw [idealContinuationLaw, pushLaw_total, freshRepeat_total hn]

theorem idealRunLaw_nonnegative (hn : 1 < Fintype.card V)
    (p : Program V O) (o : O) : 0 ≤ idealRunLaw p o := by
  cases p with
  | stop a => simp only [idealRunLaw, differencePoint]; split_ifs <;> norm_num
  | query x next =>
    exact div_nonneg
      (Finset.sum_nonneg (fun y _ => idealContinuationLaw_nonnegative hn x y (next y) o))
      (Nat.cast_nonneg _)

theorem idealRunLaw_total (hn : 1 < Fintype.card V) (p : Program V O) :
    (∑ o, idealRunLaw p o) = 1 := by
  cases p with
  | stop a => simp [idealRunLaw, differencePoint]
  | query x next =>
    simp only [idealRunLaw, ← Finset.sum_div]
    rw [Finset.sum_comm]
    simp only [idealContinuationLaw_total hn, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    have hcard : (Fintype.card V : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_trans (by norm_num : 0 < 1) hn))
    exact div_self hcard

theorem idealOutputLaw_nonnegative (hn : 1 < Fintype.card V)
    (weight : R → ℝ) (hw : ∀ t, 0 ≤ weight t)
    (program : R → Program V O) (o : O) : 0 ≤ idealOutputLaw weight program o :=
  Finset.sum_nonneg (fun t _ => mul_nonneg (hw t) (idealRunLaw_nonnegative hn _ o))

theorem idealOutputLaw_total (hn : 1 < Fintype.card V)
    (weight : R → ℝ) (hw : (∑ t, weight t) = 1) (program : R → Program V O) :
    (∑ o, idealOutputLaw weight program o) = 1 := by
  unfold idealOutputLaw
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, idealRunLaw_total hn, mul_one, hw]

end IdealLaws
end AESPaper.TwoQueryProgram
