import AES8.Math.PaperSymbolicSlopes
import AES8.Model.Byte.PaperAESAlgebraic

/-! Concrete AES specialization of the field-generic symbolic certificate. -/
noncomputable section
namespace AES8.PaperSymbolicSlopes

theorem aes_symbolic_slopes : Certificate PaperAESAlgebraic.generator :=
  symbolic_slopes _ PaperAESAlgebraic.generator_degree_gt_six

end AES8.PaperSymbolicSlopes
