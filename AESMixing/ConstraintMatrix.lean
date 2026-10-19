import AESMixing.ActivityColumns
import AESMixing.FieldMatrixCertificate

/-! Explicit matrices for the five constraint atoms. Eight variables are the
two four-byte inputs. Sixteen rows impose input support conditions and the
two possible output equations at each byte position. -/
namespace AESMixing
open scoped BigOperators
open AES
variable {F : Type*} [Ring F]

def rowValue {n : ℕ} (a x : Fin n → F) : F := ∑ i, a i * x i

theorem rowValue_append {m n : ℕ} (a x : Fin m → F) (b y : Fin n → F) :
    rowValue (Fin.append a b) (Fin.append x y) = rowValue a x + rowValue b y := by
  simp [rowValue, Fin.sum_univ_add]

theorem rowValue_zero {n : ℕ} (x : Fin n → F) : rowValue 0 x = 0 := by
  simp [rowValue]

theorem rowValue_sub {n : ℕ} (a b x : Fin n → F) :
    rowValue (a-b) x = rowValue a x - rowValue b x := by
  simp [rowValue, sub_mul, Finset.sum_sub_distrib]

def atomRow {n : ℕ} (m : Fin 5) (a b : Fin n → F) : Fin n → F :=
  match m.val with
  | 0 => 0
  | 1 => a
  | 2 => b
  | 3 => a
  | _ => a-b

def atomSecondRow {n : ℕ} (m : Fin 5) (b : Fin n → F) : Fin n → F :=
  if m = 3 then b else 0

theorem atomRows_zero_iff {n : ℕ} (m : Fin 5) (a b x : Fin n → F) :
    (rowValue (atomRow m a b) x = 0 ∧ rowValue (atomSecondRow m b) x = 0) ↔
      atomCondition m (rowValue a x) (rowValue b x) := by
  fin_cases m <;>
    simp [atomRow, atomSecondRow, atomCondition, rowValue_zero, rowValue_sub, sub_eq_zero]

def supportRow (mask : Fin 16) (i : Fin 4) : Fin 4 → F :=
  if maskBit mask i then 0 else fun j => if i = j then 1 else 0

theorem supportRow_value (mask : Fin 16) (i : Fin 4) (x : Fin 4 → F) :
    rowValue (supportRow mask i) x = if maskBit mask i then 0 else x i := by
  by_cases h : maskBit mask i = true <;> simp [rowValue, supportRow, h]

theorem supportRows_zero_iff (mask : Fin 16) (x : Fin 4 → F) :
    (∀ i, rowValue (supportRow mask i) x = 0) ↔ maskProjection mask x = x := by
  constructor
  · intro h
    funext i
    by_cases hi : maskBit mask i = true
    · simp [maskProjection, hi]
    · have hx := h i
      simpa [maskProjection, supportRow_value, hi] using hx.symm
  · intro h i
    have hx := congrFun h i
    by_cases hi : maskBit mask i = true <;>
      simp_all [maskProjection, supportRow_value]

def constraintMatrix (A : Fin 4 → Fin 4 → F)
    (a b : Fin 16) (m : Fin 4 → Fin 5) : Fin 16 → Fin 8 → F :=
  Fin.append
    (Fin.append
      (fun i => Fin.append (supportRow a i) (0 : Fin 4 → F))
      (fun i => Fin.append (0 : Fin 4 → F) (supportRow b i)))
    (Fin.append
      (fun i => atomRow (m i) (Fin.append (A i) (0 : Fin 4 → F))
        (Fin.append (0 : Fin 4 → F) (A i)))
      (fun i => atomSecondRow (m i) (Fin.append (0 : Fin 4 → F) (A i))))

theorem append_zero_iff {m n : ℕ} (x : Fin m → F) (y : Fin n → F) :
    Fin.append x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · funext i
      simpa using congrFun h (Fin.castAdd n i)
    · funext i
      simpa using congrFun h (Fin.natAdd m i)
  · rintro ⟨rfl,rfl⟩
    funext i
    refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp

theorem fieldMatrix_append_rows {m n r : ℕ}
    (A : Fin m → Fin n → F) (B : Fin r → Fin n → F) (x : Fin n → F) :
    fieldMatrix (Fin.append A B) x = Fin.append (fieldMatrix A x) (fieldMatrix B x) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [fieldMatrix]

theorem constraintMatrix_zero_iff (A : Fin 4 → Fin 4 → F)
    (a b : Fin 16) (m : Fin 4 → Fin 5) (x y : Fin 4 → F) :
    fieldMatrix (constraintMatrix A a b m) (Fin.append x y) = 0 ↔
      maskProjection a x = x ∧ maskProjection b y = y ∧
        ∀ i, atomCondition (m i) (fieldMatrix A x i) (fieldMatrix A y i) := by
  unfold constraintMatrix
  rw [fieldMatrix_append_rows (m := 8) (r := 8)]
  simp only [fieldMatrix_append_rows (m := 4) (r := 4),
    append_zero_iff (m := 8) (n := 8), append_zero_iff (m := 4) (n := 4)]
  have hs (c : Fin 16) (u v : Fin 4 → F) :
      fieldMatrix (fun i => Fin.append (supportRow c i) (0 : Fin 4 → F))
        (Fin.append u v) = 0 ↔ maskProjection c u = u := by
    rw [funext_iff]
    change (∀ i, rowValue (Fin.append (supportRow c i) 0) (Fin.append u v) = 0) ↔ _
    simp only [rowValue_append, rowValue_zero, add_zero]
    exact supportRows_zero_iff c u
  have ht (c : Fin 16) (u v : Fin 4 → F) :
      fieldMatrix (fun i => Fin.append (0 : Fin 4 → F) (supportRow c i))
        (Fin.append u v) = 0 ↔ maskProjection c v = v := by
    rw [funext_iff]
    change (∀ i, rowValue (Fin.append 0 (supportRow c i)) (Fin.append u v) = 0) ↔ _
    simp only [rowValue_append, rowValue_zero, zero_add]
    exact supportRows_zero_iff c v
  have ho : (fieldMatrix (fun i => atomRow (m i) (Fin.append (A i) 0) (Fin.append 0 (A i)))
        (Fin.append x y) = 0 ∧
      fieldMatrix (fun i => atomSecondRow (m i) (Fin.append 0 (A i))) (Fin.append x y) = 0) ↔
      ∀ i, atomCondition (m i) (fieldMatrix A x i) (fieldMatrix A y i) := by
    rw [funext_iff, funext_iff, ← forall_and]
    change (∀ i, rowValue (atomRow (m i) (Fin.append (A i) 0) (Fin.append 0 (A i)))
        (Fin.append x y) = 0 ∧
      rowValue (atomSecondRow (m i) (Fin.append 0 (A i))) (Fin.append x y) = 0) ↔ _
    simp only [atomRows_zero_iff, rowValue_append, rowValue_zero, add_zero, zero_add]
    rfl
  rw [hs, ht, ho]
  exact and_assoc

end AESMixing
