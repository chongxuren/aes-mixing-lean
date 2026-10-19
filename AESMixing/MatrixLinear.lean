import AESMixing.ByteLinear

/-! Concrete byte matrices as additive maps, with basis-complete certificates. -/
namespace AESMixing.AES
open scoped BigOperators

def injectByte {n : ℕ} (j : Fin n) : BinaryWord 8 →+ (Fin n → BinaryWord 8) where
  toFun x i := if i = j then x else 0
  map_zero' := by funext i; simp
  map_add' x y := by funext i; by_cases h : i = j <;> simp [h]

theorem column_decomposition {n : ℕ} (x : Fin n → BinaryWord 8) :
    x = ∑ j, injectByte j (x j) := by
  funext i
  simp [injectByte]

theorem column_addHom_ext {n : ℕ} {A : Type*} [AddCommMonoid A]
    (f g : (Fin n → BinaryWord 8) →+ A)
    (h : ∀ j b, f (injectByte j (byteBasis b)) = g (injectByte j (byteBasis b))) : f = g := by
  have hi (j : Fin n) : f.comp (injectByte j) = g.comp (injectByte j) :=
    byte_addHom_ext _ _ (h j)
  apply DFunLike.ext
  intro x
  rw [column_decomposition x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact DFunLike.congr_fun (hi j) (x j)

def columnMatrix {m n : ℕ} (M : Fin m → Fin n → Byte) :
    (Fin n → BinaryWord 8) →+ (Fin m → BinaryWord 8) where
  toFun x i := ∑ j, scale (M i j) (x j)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [map_add, Finset.sum_add_distrib]

/-- A left-inverse identity checked on the binary basis holds for all inputs. -/
theorem matrix_left_inverse_from_basis {n : ℕ} (M R : Fin n → Fin n → Byte)
    (h : ∀ j b,
      columnMatrix R (columnMatrix M (injectByte j (byteBasis b))) = injectByte j (byteBasis b)) :
    Function.LeftInverse (columnMatrix R) (columnMatrix M) := by
  have he : (columnMatrix R).comp (columnMatrix M) = AddMonoidHom.id _ :=
    column_addHom_ext _ _ h
  intro x
  exact DFunLike.congr_fun he x

end AESMixing.AES
