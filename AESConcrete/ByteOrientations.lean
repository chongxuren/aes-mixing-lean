import AESMixing.ByteResources

/-! The four concrete byte channels and their already proved resources.
This module defines no Gram estimates or word-level correspondence. -/

noncomputable section
namespace AESConcrete.ByteOrientations
open AESMixing

abbrev Byte := BinaryWord 8

inductive Orientation
  | ordinary
  | transposed
  | fourier
  | fourierTransposed

def channel : Orientation → Byte → Byte → ℝ
  | .ordinary => aesByteChannel
  | .transposed => fun b a => aesByteChannel a b
  | .fourier => aesSquaredWalshChannel
  | .fourierTransposed => fun b a => aesSquaredWalshChannel a b

theorem channel_resources (orientation : Orientation) : ByteResources (channel orientation) := by
  cases orientation
  · exact aes_byte_resources
  · exact aes_byte_transpose_resources
  · exact aes_fourier_byte_resources
  · exact aes_fourier_byte_transpose_resources

end AESConcrete.ByteOrientations
