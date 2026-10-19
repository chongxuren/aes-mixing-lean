import AESMixing.IncidenceCounting

/-!
# Exact graph-support counts for the fixed v9 AES target
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators

namespace AESPaper.ActivityMDSCounts
open AESMixing
open AESMixing.AES (maskBit maskSize)

set_option maxRecDepth 100000
attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- Unnormalized indicator of the exact zero mask r. -/
def supportWeight (r : Fin 16) (y : Fin 4 → V) : ℝ :=
  ∏ i, supportConstant (maskBit r i) (y i)

def exactSupport (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16)
    (x : Fin 4 → V) : Prop :=
  (∀ i, L x i = 0 ↔ maskBit r i = true) ∧
    (∀ i, x i = 0 ↔ maskBit z i = true)

instance (L : (Fin 4 → V) →+ (Fin 4 → V)) (r z : Fin 16) :
    DecidablePred (exactSupport L r z) := by
  intro x
  unfold exactSupport
  infer_instance

def activePositions (r z : Fin 16) : Finset GraphPosition :=
  unmarkedGraphPositions r z 0 0

def activeCount (r z : Fin 16) : ℕ :=
  (4-maskSize r) + (4-maskSize z)

/-- Exact finite polynomial, including the unique zero point once every
set of at least four graph coordinates is forced to zero. -/
def supportCount (q : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (n+1), (-1 : ℝ)^t * (Nat.choose n t : ℝ) *
    q^(4-(8-n+t))

theorem activeCount_balance (r z : Fin 16) :
    maskSize r + maskSize z + activeCount r z = 8 := by
  have hr := maskSize_le_four r
  have hz := maskSize_le_four z
  unfold activeCount
  omega

theorem activePositions_card (r z : Fin 16) :
    (activePositions r z).card = activeCount r z := by
  simpa only [activePositions, activeCount, show maskSize (0 : Fin 16) = 0 by decide,
    Nat.add_zero] using
    unmarkedGraphPositions_card r z 0 0 (mask_disjoint_empty r) (mask_disjoint_empty z)

theorem exactSupport_iff_graph (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z : Fin 16) (x : Fin 4 → V) :
    exactSupport L r z x ↔ graphZeroConditions L r z x ∧
      ∀ j ∈ activePositions r z, graphCoordinate L x j ≠ 0 := by
  constructor
  · rintro ⟨hr,hz⟩
    refine ⟨⟨fun i hi => (hr i).mpr hi, fun i hi => (hz i).mpr hi⟩, ?_⟩
    intro j hj
    cases j with
    | inl i =>
      have hi := (unmarkedGraphPositions_output r z 0 0 i).mp hj
      exact fun h => hi.1 ((hr i).mp h)
    | inr i =>
      have hi := (unmarkedGraphPositions_input r z 0 0 i).mp hj
      exact fun h => hi.1 ((hz i).mp h)
  · rintro ⟨⟨hr,hz⟩,hs⟩
    constructor
    · intro i
      constructor
      · intro hi
        by_contra hm
        have hmem : Sum.inl i ∈ activePositions r z :=
          (unmarkedGraphPositions_output r z 0 0 i).mpr
            ⟨hm, by rw [empty_mask_bit]; decide⟩
        exact hs (Sum.inl i) hmem hi
      · exact hr i
    · intro i
      constructor
      · intro hi
        by_contra hm
        have hmem : Sum.inr i ∈ activePositions r z :=
          (unmarkedGraphPositions_input r z 0 0 i).mpr
            ⟨hm, by rw [empty_mask_bit]; decide⟩
        exact hs (Sum.inr i) hmem hi
      · exact hz i

theorem supportWeight_indicator (r : Fin 16) (y : Fin 4 → V) :
    supportWeight r y = if ∀ i, y i = 0 ↔ maskBit r i = true then 1 else 0 := by
  have hp (i : Fin 4) : supportConstant (maskBit r i) (y i) =
      if y i = 0 ↔ maskBit r i = true then 1 else 0 := by
    cases h : maskBit r i <;> by_cases hy : y i = 0 <;>
      simp [supportConstant, identityKernel, h, hy]
  unfold supportWeight
  simp_rw [hp]
  by_cases h : ∀ i : Fin 4, y i = 0 ↔ maskBit r i = true
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i _
    exact if_pos (h i)
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem supportWeight_product (L : (Fin 4 → V) →+ (Fin 4 → V))
    (r z : Fin 16) (x : Fin 4 → V) :
    supportWeight r (L x) * supportWeight z x =
      if exactSupport L r z x then 1 else 0 := by
  rw [supportWeight_indicator, supportWeight_indicator]
  unfold exactSupport
  split_ifs <;> simp_all

theorem shortened_real_card (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z : Fin 16) :
    (Fintype.card (ShortenedGraph L r z) : ℝ) =
      (Fintype.card V : ℝ)^(4-(maskSize r+maskSize z)) := by
  simpa only [Nat.cast_pow] using
    congrArg (fun k : ℕ => (k : ℝ)) (mds_graph_zero_count L hL r z)

/-- Exact cardinality depends only on the total number of active graph
positions, without a field or independent-coordinate hypothesis. -/
theorem exact_support_card (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z : Fin 16) :
    (Fintype.card {x : Fin 4 → V // exactSupport L r z x} : ℝ) =
      supportCount (Fintype.card V) (activeCount r z) := by
  have hexp := graph_nonzero_expansion L r z (activePositions r z)
    (fun _ : Fin 4 → V => (1 : ℝ))
  have hstart :
      (Fintype.card {x : Fin 4 → V // exactSupport L r z x} : ℝ) =
      ∑ t ∈ (activePositions r z).powerset, (-1 : ℝ)^t.card *
        (Fintype.card (ShortenedGraph L (maskUnion r (outputPositionMask t))
          (maskUnion z (inputPositionMask t))) : ℝ) := by
    simpa only [← exactSupport_iff_graph, mul_one, real_indicator_sum_card,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hexp
  have hbalance := activeCount_balance r z
  have hzero : maskSize r+maskSize z = 8-activeCount r z := by omega
  calc
    _ = ∑ t ∈ (activePositions r z).powerset, (-1 : ℝ)^t.card *
        (Fintype.card V : ℝ)^(4-(maskSize r+maskSize z+t.card)) := by
      rw [hstart]
      apply Finset.sum_congr rfl
      intro t ht
      rw [shortened_real_card L hL,
        shortening_constraint_count r z 0 0 t ht]
    _ = ∑ t ∈ Finset.range (activeCount r z+1),
        (Nat.choose (activeCount r z) t : ℝ) *
          ((-1 : ℝ)^t * (Fintype.card V : ℝ)^(4-(maskSize r+maskSize z+t))) := by
      simpa only [activePositions_card] using
        powerset_size_sum (activePositions r z)
          (fun t => (-1 : ℝ)^t * (Fintype.card V : ℝ)^(4-(maskSize r+maskSize z+t)))
    _ = _ := by
      unfold supportCount
      apply Finset.sum_congr rfl
      intro t ht
      rw [hzero]
      ring

theorem exact_support_card_of_active_sizes
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (a b : Fin 5) (ha : maskSize r+a.val = 4) (hb : maskSize z+b.val = 4) :
    (Fintype.card {x : Fin 4 → V // exactSupport L r z x} : ℝ) =
      supportCount (Fintype.card V) (a.val+b.val) := by
  rw [exact_support_card L hL]
  have hn : activeCount r z = a.val+b.val := by unfold activeCount; omega
  rw [hn]

/-- The unnormalized support weights count the genuine MDS support
intersection exactly. This is the interface for projected-kernel assembly. -/
theorem supportWeight_graph_sum (L : (Fin 4 → V) →+ (Fin 4 → V))
    (hL : ZeroMDS L) (r z : Fin 16) :
    (∑ x : Fin 4 → V, supportWeight r (L x) * supportWeight z x) =
      supportCount (Fintype.card V) (activeCount r z) := by
  simp_rw [supportWeight_product]
  rw [real_indicator_sum_card, exact_support_card L hL]

theorem supportWeight_graph_sum_of_active_sizes
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L) (r z : Fin 16)
    (a b : Fin 5) (ha : maskSize r+a.val = 4) (hb : maskSize z+b.val = 4) :
    (∑ x : Fin 4 → V, supportWeight r (L x) * supportWeight z x) =
      supportCount (Fintype.card V) (a.val+b.val) := by
  simp_rw [supportWeight_product]
  rw [real_indicator_sum_card, exact_support_card_of_active_sizes L hL r z a b ha hb]

theorem supportCount_zero (q : ℝ) : supportCount q 0 = 1 := by
  simp [supportCount]

theorem supportCount_small (q : ℝ) (n : Fin 5) (hn : n ≠ 0) :
    supportCount q n.val = 0 := by
  fin_cases n
  · exact (hn rfl).elim
  all_goals norm_num [supportCount, Finset.sum_range_succ, Nat.choose]

theorem supportCount_five (q : ℝ) : supportCount q 5 = q-1 := by
  norm_num [supportCount, Finset.sum_range_succ, Nat.choose] <;> ring

theorem supportCount_six (q : ℝ) : supportCount q 6 = q^2-6*q+5 := by
  norm_num [supportCount, Finset.sum_range_succ, Nat.choose] <;> ring

theorem supportCount_seven (q : ℝ) : supportCount q 7 = q^3-7*q^2+21*q-15 := by
  norm_num [supportCount, Finset.sum_range_succ, Nat.choose] <;> ring

theorem supportCount_eight (q : ℝ) : supportCount q 8 = q^4-8*q^3+28*q^2-56*q+35 := by
  norm_num [supportCount, Finset.sum_range_succ, Nat.choose] <;> ring

end AESPaper.ActivityMDSCounts
