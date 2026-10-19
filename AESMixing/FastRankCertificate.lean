import AESMixing.RankCertificate

/-! A proved optimization of certificate checking: skip multiplication by
zero and one. Kernel evaluation remains the checker; no native evaluator or
new mathematical axiom is introduced. -/
namespace AESMixing
open scoped BigOperators

/-- Compact exact byte data; every coefficient is still checked by the
reconstruction identities. Field numerals are not used to encode bytes. -/
def certificateRow {n : ℕ} (packed : ℕ) (i : Fin n) : BinaryWord 8 :=
  ⟨BitVec.ofNat 8 (packed >>> (8*i.val))⟩

def certificateMul (x y : BinaryWord 8) : BinaryWord 8 :=
  if x = 0 then 0 else if y = 0 then 0 else if x = 1 then y else if y = 1 then x else x*y

theorem certificateMul_eq (x y : BinaryWord 8) : certificateMul x y = x*y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    by_cases hx1 : x = 1 <;> by_cases hy1 : y = 1 <;>
    simp [certificateMul,hx,hy,hx1,hy1]

def RankCertificate.FastValid {rows cols : ℕ}
    (c : RankCertificate (BinaryWord 8) rows cols)
    (A : Fin rows → Fin cols → BinaryWord 8) : Prop :=
  (∀ i j, A i j = ∑ k, certificateMul (A i (c.pivots k)) (c.reduced k j)) ∧
  (∀ i j, (∑ k, certificateMul (c.leftInverse i k) (A k (c.pivots j))) = if i = j then 1 else 0) ∧
  (∀ i j, c.reduced i (c.pivots j) = if i = j then 1 else 0)

instance {rows cols : ℕ} (c : RankCertificate (BinaryWord 8) rows cols)
    (A : Fin rows → Fin cols → BinaryWord 8) : Decidable (c.FastValid A) := by
  unfold RankCertificate.FastValid
  infer_instance

theorem RankCertificate.valid_of_fast {rows cols : ℕ}
    (c : RankCertificate (BinaryWord 8) rows cols)
    (A : Fin rows → Fin cols → BinaryWord 8) (h : c.FastValid A) : c.Valid A := by
  simpa only [RankCertificate.FastValid, RankCertificate.Valid, certificateMul_eq] using h

end AESMixing
