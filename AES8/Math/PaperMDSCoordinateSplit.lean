/- Module role: Reusable finite-dimensional kernels, tensor energies, MDS information sets and symbolic norm bounds.
See docs/PAPER_COVERAGE.md for current-paper correspondence and open obligations. -/
import AES8.Math.PaperMDSGram

/-!
# Physical coordinate partition for information-set overlap

For two code dimensions `s,t ≤ n` with `n ≤ s+t`, the paper partitions the
middle coordinates into `A,B,E`, of sizes `n-t,s+t-n,n-s`. Both information
sets and their cardinalities are constructed here from those inequalities.
The embeddings name physical positions; MDS supplies their information-set
property in the caller. No fiber size or operator bound is assumed here.
Constructive structural proofs only; no AES estimates or attacks.
-/

noncomputable section

namespace AES8.PaperMDSCoordinateSplit

variable {M A B E : Type*} [Fintype M]

/-- A physical middle-coordinate partition with the paper's exact sizes. -/
def splitCoordinates (s t : ℕ) (hs : s ≤ Fintype.card M)
    (ht : t ≤ Fintype.card M) (hst : Fintype.card M ≤ s + t) :
    (Fin (Fintype.card M - t) ⊕
      (Fin (s + t - Fintype.card M) ⊕ Fin (Fintype.card M - s))) ≃ M :=
  Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega)

/-- The left information coordinates occupy `A` and `B`. -/
def leftInfoEmbedding (idx : A ⊕ (B ⊕ E) ≃ M) : (A ⊕ B) ↪ M where
  toFun x := idx (Sum.elim Sum.inl (fun b => Sum.inr (Sum.inl b)) x)
  inj' := by
    intro x y h
    have h' := idx.injective h
    cases x <;> cases y <;> simp_all

/-- The right information coordinates occupy `B` and `E`. -/
def rightInfoEmbedding (idx : A ⊕ (B ⊕ E) ≃ M) : (B ⊕ E) ↪ M where
  toFun x := idx (Sum.inr x)
  inj' := fun _ _ h => Sum.inr.inj (idx.injective h)

@[simp] theorem leftInfoEmbedding_inl (idx : A ⊕ (B ⊕ E) ≃ M) (a : A) :
    leftInfoEmbedding idx (Sum.inl a) = idx (Sum.inl a) := rfl

@[simp] theorem leftInfoEmbedding_inr (idx : A ⊕ (B ⊕ E) ≃ M) (b : B) :
    leftInfoEmbedding idx (Sum.inr b) = idx (Sum.inr (Sum.inl b)) := rfl

@[simp] theorem rightInfoEmbedding_inl (idx : A ⊕ (B ⊕ E) ≃ M) (b : B) :
    rightInfoEmbedding idx (Sum.inl b) = idx (Sum.inr (Sum.inl b)) := rfl

@[simp] theorem rightInfoEmbedding_inr (idx : A ⊕ (B ⊕ E) ≃ M) (e : E) :
    rightInfoEmbedding idx (Sum.inr e) = idx (Sum.inr (Sum.inr e)) := rfl

theorem leftInfo_card (s t : ℕ) (hs : s ≤ Fintype.card M)
    (ht : t ≤ Fintype.card M) (hst : Fintype.card M ≤ s + t) :
    Fintype.card (Fin (Fintype.card M - t) ⊕ Fin (s + t - Fintype.card M)) = s := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

theorem rightInfo_card (s t : ℕ) (hs : s ≤ Fintype.card M)
    (ht : t ≤ Fintype.card M) (hst : Fintype.card M ≤ s + t) :
    Fintype.card (Fin (s + t - Fintype.card M) ⊕ Fin (Fintype.card M - s)) = t := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Every middle coordinate appears in at least one information set. -/
theorem info_cover (idx : A ⊕ (B ⊕ E) ≃ M) (i : M) :
    (∃ x, leftInfoEmbedding idx x = i) ∨ (∃ y, rightInfoEmbedding idx y = i) := by
  obtain ⟨x, rfl⟩ := idx.surjective i
  rcases x with a | x
  · exact Or.inl ⟨Sum.inl a, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

/-- The left and right information sets intersect exactly in `B`. -/
theorem info_intersection (idx : A ⊕ (B ⊕ E) ≃ M) (x : A ⊕ B) (y : B ⊕ E) :
    leftInfoEmbedding idx x = rightInfoEmbedding idx y ↔
      ∃ b : B, x = Sum.inr b ∧ y = Sum.inl b := by
  constructor
  · intro h
    have h' := idx.injective h
    cases x with
    | inl a => cases h'
    | inr b =>
      have hy : y = Sum.inl b := (Sum.inr.inj h').symm
      exact ⟨b, rfl, hy⟩
  · rintro ⟨b, rfl, rfl⟩
    rfl

end AES8.PaperMDSCoordinateSplit
