import AESConcrete.WordFourierDiffusion
import AESConcrete.DegreeHilbertSchmidt

/-! Coordinate reversal commutes with every byte-degree projection.
This transports physical Fourier block bounds without treating arbitrary
unitary conjugation as entrywise or degreewise invariance. -/
noncomputable section
open scoped BigOperators
namespace AES8.PaperDegreeReverse
open AESMixing AESConcrete.WordFourierDiffusion
open AESConcrete.DegreeHilbertSchmidt
set_option autoImplicit false
set_option maxRecDepth 100000

def reverseMask : Equiv.Perm (Fin 4 → Bool) where
  toFun a i := a (byteReverse i)
  invFun a i := a (byteReverse i)
  left_inv a := by funext i; exact congrArg a (byteReverse_self i)
  right_inv a := by funext i; exact congrArg a (byteReverse_self i)

theorem degree_reverse (a : Fin 4 → Bool) :
    degreeIndex (reverseMask a) = degreeIndex a :=
  (by decide : ∀ a, degreeIndex (reverseMask a) = degreeIndex a) a

theorem projection_reverse (a : Fin 4 → Bool) (y x : AES.Word) :
    productProjection 0 (reverseMask a) (wordReverse y) (wordReverse x) =
      productProjection 0 a y x := by
  exact Equiv.prod_comp byteReverse (fun i => degreePiece 0 (a i) (y i) (x i))

theorem degreeKernel_reverse (j : Fin 5) (y x : AES.Word) :
    degreeKernel 0 j (wordReverse y) (wordReverse x) = degreeKernel 0 j y x := by
  unfold degreeKernel
  calc
    _ = ∑ a, if degreeIndex (reverseMask a) = j then
        productProjection 0 (reverseMask a) (wordReverse y) (wordReverse x) else 0 :=
      (Equiv.sum_comp reverseMask (fun a => if degreeIndex a = j then
        productProjection 0 a (wordReverse y) (wordReverse x) else 0)).symm
    _ = _ := by simp only [degree_reverse, projection_reverse]

theorem reindex_compose {V W : Type*} [Fintype V] [Fintype W]
    (e : V ≃ W) (K L : W → W → ℝ) :
    kernelCompose (reindexKernel e K) (reindexKernel e L) =
      reindexKernel e (kernelCompose K L) := by
  funext y x
  exact e.sum_comp (fun v => K (e y) v * L v (e x))

theorem block_reverse (K : AES.Word → AES.Word → ℝ) (i j : Fin 5) :
    block 0 (reindexKernel wordReverse K) i j =
      reindexKernel wordReverse (block 0 K i j) := by
  have hi : reindexKernel wordReverse (degreeKernel 0 i) = degreeKernel 0 i := by
    funext y x; exact degreeKernel_reverse i y x
  have hj : reindexKernel wordReverse (degreeKernel 0 j) = degreeKernel 0 j := by
    funext y x; exact degreeKernel_reverse j y x
  unfold block
  calc
    _ = kernelCompose (reindexKernel wordReverse (degreeKernel 0 i))
        (kernelCompose (reindexKernel wordReverse K)
          (reindexKernel wordReverse (degreeKernel 0 j))) := by rw [hi, hj]
    _ = _ := by rw [reindex_compose, reindex_compose]

end AES8.PaperDegreeReverse
