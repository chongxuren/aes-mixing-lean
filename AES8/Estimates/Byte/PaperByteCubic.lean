import AESConcrete.ByteLineBounds
import AES8.Estimates.Byte.PaperByteGramPrinted
import AES8.Estimates.Byte.PaperByteCubePrinted
import AES8.Estimates.Byte.PaperByteMixedPrinted

/-!
# The paper's exact cubic byte resources

Frozen paper f902bb94, localres:cubic and localres:cubic-constants.
This leaf owns the literal byte constants and their strict rational rounding.
The contracted three-mark line/plane geometry is a separate join.
Each byte orientation is fixed within its Gram; different tensor legs may
choose different orientations. Constructive bounds only; no attacks.
-/

noncomputable section
open scoped BigOperators

namespace AES8.PaperByteCubic
open AESMixing
open AESConcrete.ByteGramCore (Byte)
open AESConcrete.ByteGramDiagonal (residualGram)
open AESConcrete.ByteOrientations (Orientation channel)

def S3 : ℝ := (255 : ℝ) *
  (16766^3 + 70*191^3 + 112*64^3 + 72*319^3) / 4177920^3
def gF : ℝ := 13276 / (4*4177920)
def T2 : ℝ := 571447 / 2^27
def a0 : ℝ := 1081 / 1000
def b0 : ℝ := 111 / 500

theorem gram_absolute_cube (o : Orientation) :
    (∑ a, ∑ b, |residualGram (channel o) a b|^3) ≤ S3 :=
  AES8.PaperByteCubePrinted.actual_gram_absolute_cube_le o

theorem gram_mixed_entry (o : Orientation) (a b : Byte) :
    |kernelCompose (residualGram (channel o)) byteFourierMatrix a b| ≤ gF :=
  AES8.PaperByteMixedPrinted.actual_gram_mixed_bound o a b

-- Route dependency: this bound uses the paper's symbolic H <= 70 chain.
-- Exact finite multiplicities remain separate exported predecessor facts.
theorem gram_square_moment (o : Orientation) :
    (∑ a, ∑ b, residualGram (channel o) a b^2) ≤ T2 :=
  AES8.PaperByteGramPrinted.actual_gram_square_moment_le o

theorem a3_eq : AESConcrete.ByteLineBounds.a3 = 65536*S3 := rfl

theorem b3_eq : AESConcrete.ByteLineBounds.b3 = 65536*gF*T2 := by
  unfold AESConcrete.ByteLineBounds.b3 AESConcrete.ByteLineBounds.mixedCubeBound gF T2
  ring

-- Editorial: retain the paper's1.081/.222 endpoints; the historical
-- exported1.1/.223 relaxations do not establish these named inequalities.
theorem scaled_cube_lt : 65536*S3 < a0 := by
  norm_num [S3, a0]

theorem scaled_mixed_lt : 65536*gF*T2 < b0 := by
  norm_num [gF, T2, b0]

theorem a3_lt : AESConcrete.ByteLineBounds.a3 < a0 := by
  rw [a3_eq]
  exact scaled_cube_lt

theorem b3_lt : AESConcrete.ByteLineBounds.b3 < b0 := by
  rw [b3_eq]
  exact scaled_mixed_lt

end AES8.PaperByteCubic
