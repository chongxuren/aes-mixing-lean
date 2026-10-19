import AESMixing.FieldMatrixCertificate

/-! Compact RREF reconstruction certificates. The rank is accepted only after
all three matrix identities are checked. No floating-point rank or external
linear algebra oracle is part of the theorem. -/
namespace AESMixing
open scoped BigOperators

structure RankCertificate (F : Type*) (rows cols : ℕ) where
  rank : Fin (cols+1)
  pivots : Fin rank.val → Fin cols
  reduced : Fin rank.val → Fin cols → F
  leftInverse : Fin rank.val → Fin rows → F

variable {F : Type*} [Ring F] {rows cols : ℕ}

def RankCertificate.Valid (c : RankCertificate F rows cols)
    (A : Fin rows → Fin cols → F) : Prop :=
  (∀ i j, A i j = ∑ k, A i (c.pivots k) * c.reduced k j) ∧
  (∀ i j, (∑ k, c.leftInverse i k * A k (c.pivots j)) = if i = j then 1 else 0) ∧
  (∀ i j, c.reduced i (c.pivots j) = if i = j then 1 else 0)

instance [DecidableEq F] (c : RankCertificate F rows cols)
    (A : Fin rows → Fin cols → F) : Decidable (c.Valid A) := by
  unfold RankCertificate.Valid
  infer_instance

theorem RankCertificate.kernel_card [Fintype F] [DecidableEq F] (c : RankCertificate F rows cols)
    (A : Fin rows → Fin cols → F) (h : c.Valid A) :
    Fintype.card (fieldMatrix A).ker = Fintype.card F ^ (cols-c.rank.val) := by
  classical
  have hc : c.rank.val ≤ cols := by omega
  have hR (i j : Fin c.rank.val) :
      (∑ k : Fin cols, c.reduced i k * (if k = c.pivots j then 1 else 0)) =
        if i = j then 1 else 0 := by
    simpa using h.2.2 i j
  simpa only [← Nat.card_eq_fintype_card] using
    fieldMatrix_kernel_card hc A (fun i k => A i (c.pivots k)) c.reduced
      c.leftInverse (fun k j => if k = c.pivots j then 1 else 0) h.1 h.2.1 hR

theorem byte_rank_certificate_card {rows cols : ℕ}
    (c : RankCertificate (BinaryWord 8) rows cols)
    (A : Fin rows → Fin cols → BinaryWord 8) (h : c.Valid A) :
    Nat.card (fieldMatrix A).ker = 256 ^ (cols-c.rank.val) := by
  have hh := c.kernel_card A h
  norm_num only [BinaryWord.card, Nat.reducePow] at hh
  simpa only [← Nat.card_eq_fintype_card] using hh

end AESMixing
