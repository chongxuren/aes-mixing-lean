import AESPaper.StartingWord
import AESPaper.BoundarySourceCoordinates
import AESConcrete.WordColumnGram

/-!
# The actual four-round law with one active source word

The fixed input has one active word after its initial ShiftRows. After the
first parallel superbox layer, its only random label is one whole source
word. The actual forward boundary sends that same label to all four word
coordinates. The final parallel layer therefore gives one common-source
tensor response, without independence of its current input words.

`law` is the stable interface for the separate residual-word-degree proof.
Its actual physical identification is at grouped index one, which is four
physical rounds. `Pi` uses inverse probability weights; the tensor response
uses forward boundary coordinates after a proved change of summation label.
No profile projection, norm estimate, or complete initialization is asserted.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators

namespace AESPaper.OneSourceLaw
open AESMixing AESConcrete
open AESPaper.StartingWord (wordLaw sourceInput)
open AESPaper.BoundarySourceCoordinates (singleWord outputEquiv)
open AESConcrete.WordColumnGram (tensorColumn tensorResponse)

/-- The four-round output retains one common whole-word source label. -/
def law (k : Fin 4) (a : AES.Word) : AES.WordState → ℝ :=
  tensorResponse (fun _ : Fin 4 => AES.wordSuperboxKernel)
    (fun x : AES.Word => fun c => outputEquiv k c x) (wordLaw a)

/-- The initial two-round product, before the physical inter-word boundary. -/
def initialLaw (k : Fin 4) (a : AES.Word) : AES.WordState → ℝ :=
  fun y => ∏ c : Fin 4, wordLaw (singleWord k a c) (y c)

section GenericEmbedding
variable {X Z W : Type*}
variable [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- A supported finite sum is reindexed by an injective source label. -/
theorem sum_supported_embedding (e : Z → X) (he : Function.Injective e)
    (f : X → ℝ) (hz : ∀ x, x ∉ Finset.univ.image e → f x = 0) :
    (∑ x : X, f x) = ∑ z : Z, f (e z) := by
  calc
    _ = ∑ x ∈ Finset.univ.image e, f x := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hz x hx)
    _ = _ := Finset.sum_image (fun x _ y _ hxy => he hxy)

/-- Reindex the inverse weights of a law transport to its forward map,
then retain only the source embedding. The input weights may be signed. -/
theorem action_relabel_supported_embedding
    (K : W → X → ℝ) (L : Equiv.Perm X)
    (e : Z → X) (he : Function.Injective e) (f : X → ℝ)
    (hz : ∀ x, x ∉ Finset.univ.image e → f x = 0) :
    action K (lawRelabel L f) =
      fun y => ∑ z : Z, K y (L (e z)) * f (e z) := by
  funext y
  have h := Equiv.sum_comp L (fun x => K y x * f (L.symm x))
  calc
    _ = ∑ x : X, K y (L x) * f x := by
      simpa only [action, lawRelabel, L.symm_apply_apply] using h.symm
    _ = ∑ z : Z, K y (L (e z)) * f (e z) := by
      apply sum_supported_embedding e he
      intro x hx
      rw [hz x hx, mul_zero]

end GenericEmbedding

/-- Tensor-response mass is computed before any concrete alphabet is exposed. -/
theorem tensorResponse_mass {I V X : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [Fintype X]
    (T : I → V → V → ℝ) (coords : X → I → V) (mu : X → ℝ)
    (hT : ∀ i x, (∑ y, T i y x) = 1) :
    (∑ y, tensorResponse T coords mu y) = ∑ x, mu x := by
  unfold tensorResponse
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_mul]
  have hc : (∑ y, tensorColumn T coords y x) = 1 := by
    unfold tensorColumn
    rw [← Fintype.prod_sum (fun i y => T i y (coords x i))]
    simp only [hT, Finset.prod_const_one]
  rw [hc, one_mul]

theorem singleWord_injective (k : Fin 4) : Function.Injective (singleWord k) := by
  intro x z h
  simpa only [BoundarySourceCoordinates.singleWord_same] using congrFun h k

/-- Inactive inputs give actual zero point masses, not a source assumption. -/
theorem wordLaw_zero_input (y : AES.Word) :
    wordLaw 0 y = if y = 0 then 1 else 0 :=
  AES.word_superbox_pointed.zero_column y

theorem initialLaw_at_singleWord (k : Fin 4) (a x : AES.Word) :
    initialLaw k a (singleWord k x) = wordLaw a x := by
  unfold initialLaw
  calc
    _ = ∏ c : Fin 4, if c = k then wordLaw a x else 1 := by
      apply Finset.prod_congr rfl
      intro c _
      by_cases hc : c = k
      · subst c
        simp only [BoundarySourceCoordinates.singleWord_same, if_true]
      · rw [if_neg hc, BoundarySourceCoordinates.singleWord_other k c hc a,
          BoundarySourceCoordinates.singleWord_other k c hc x]
        simp only [wordLaw_zero_input, if_true]
    _ = wordLaw a x := by simp

theorem initialLaw_zero_outside (k : Fin 4) (a : AES.Word) (y : AES.WordState)
    (hy : y ∉ Finset.univ.image (singleWord k)) : initialLaw k a y = 0 := by
  by_contra hmu
  have hz (c : Fin 4) (hc : c ≠ k) : y c = 0 := by
    by_contra hyc
    apply hmu
    unfold initialLaw
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    rw [BoundarySourceCoordinates.singleWord_other k c hc a,
      wordLaw_zero_input, if_neg hyc]
  have he : singleWord k (y k) = y := by
    funext c
    by_cases hc : c = k
    · subst c
      exact BoundarySourceCoordinates.singleWord_same k (y k)
    · rw [BoundarySourceCoordinates.singleWord_other k c hc, hz c hc]
  exact hy (Finset.mem_image.mpr ⟨y k, Finset.mem_univ _, he⟩)

/-- The two-round product is identified from the fixed physical input. -/
theorem groupedLaw_initial_eq_initialLaw (b : AES.State) (k : Fin 4) (a : AES.Word)
    (hsource : sourceInput b = singleWord k a) :
    GroupedLaw.groupedLaw 0 b = initialLaw k a := by
  funext y
  rw [StartingWord.grouped_initial_product, hsource]
  rfl

/-- This changes inverse law weights to the actual forward boundary images. -/
theorem H_Pi_initialLaw (k : Fin 4) (a : AES.Word) :
    GroupedRecurrence.H (GroupedRecurrence.Pi (initialLaw k a)) = law k a := by
  have h := action_relabel_supported_embedding AES.parallelSuperboxKernel
    GroupedRecurrence.boundary.toEquiv (singleWord k) (singleWord_injective k)
    (initialLaw k a) (initialLaw_zero_outside k a)
  change action AES.parallelSuperboxKernel
    (lawRelabel GroupedRecurrence.boundary.toEquiv (initialLaw k a)) = law k a
  rw [h]
  funext y
  change (∑ x : AES.Word, AES.parallelSuperboxKernel y
    (GroupedRecurrence.boundary (singleWord k x)) * initialLaw k a (singleWord k x)) = _
  simp only [initialLaw_at_singleWord, law, tensorResponse, tensorColumn,
    AES.parallelSuperboxKernel, coordinateKernel,
    BoundarySourceCoordinates.boundary_singleWord]

/-- Grouped index one is exactly four physical rounds, after H Pi H. -/
theorem groupedLaw_one_eq_law (b : AES.State) (k : Fin 4) (a : AES.Word)
    (hsource : sourceInput b = singleWord k a) :
    GroupedLaw.groupedLaw 1 b = law k a := by
  rw [show (1 : ℕ) = 0+1 by rfl, GroupedRecurrence.groupedLaw_succ,
    groupedLaw_initial_eq_initialLaw b k a hsource]
  exact H_Pi_initialLaw k a

theorem physical_four_round_eq_law (b : AES.State) (k : Fin 4) (a : AES.Word)
    (hsource : sourceInput b = singleWord k a) :
    (fun y => AES.physicalDifferenceLaw 4 b (GroupedLaw.outputCoordinates y)) = law k a := by
  exact groupedLaw_one_eq_law b k a hsource

theorem law_nonnegative (k : Fin 4) (a : AES.Word) (y : AES.WordState) :
    0 ≤ law k a y := by
  unfold law tensorResponse tensorColumn
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg
    (Finset.prod_nonneg (fun c _ => AES.word_superbox_pointed.nonnegative _ _))
    (StartingWord.wordLaw_nonnegative a x)

theorem law_mass (k : Fin 4) (a : AES.Word) : (∑ y, law k a y) = 1 := by
  rw [law, tensorResponse_mass _ _ _ (fun _ x => AES.word_superbox_pointed.column_sum x)]
  exact StartingWord.wordLaw_total a

/-- Nonzero source labels give nonzero input differences at all four outputs. -/
theorem outputEquiv_ne_zero (k c : Fin 4) (x : AES.Word) (hx : x ≠ 0) :
    outputEquiv k c x ≠ 0 := by
  intro h
  exact hx ((outputEquiv k c).injective
    (h.trans (BoundarySourceCoordinates.outputEquiv_zero k c).symm))

/-- The final word channels preserve nonzero differences in every coordinate. -/
theorem law_zero_of_coordinate_zero (k : Fin 4) (a : AES.Word) (ha : a ≠ 0)
    (y : AES.WordState) (c : Fin 4) (hy : y c = 0) : law k a y = 0 := by
  unfold law tensorResponse
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x = 0
  · subst x
    rw [StartingWord.wordLaw_zero a ha, mul_zero]
  · have hcol : tensorColumn (fun _ : Fin 4 => AES.wordSuperboxKernel)
        (fun x : AES.Word => fun c => outputEquiv k c x) y x = 0 := by
      unfold tensorColumn
      apply Finset.prod_eq_zero (Finset.mem_univ c)
      change AES.wordSuperboxKernel (y c) (outputEquiv k c x) = 0
      rw [hy, AES.word_superbox_pointed.zero_row,
        if_neg (outputEquiv_ne_zero k c x hx)]
    rw [hcol, zero_mul]

theorem law_zero (k : Fin 4) (a : AES.Word) (ha : a ≠ 0) : law k a 0 = 0 :=
  law_zero_of_coordinate_zero k a ha 0 0 rfl

theorem law_all_active_support (k : Fin 4) (a : AES.Word) (ha : a ≠ 0)
    (y : AES.WordState) (hy : law k a y ≠ 0) (c : Fin 4) : y c ≠ 0 := by
  intro hc
  exact hy (law_zero_of_coordinate_zero k a ha y c hc)

end AESPaper.OneSourceLaw
