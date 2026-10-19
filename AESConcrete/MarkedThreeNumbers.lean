import AESConcrete.ByteLineBounds
import AESConcrete.LineOverlap
import AESConcrete.MixedCodeBounds
import AESConcrete.ContainmentCodeBounds

/-!
# Exact signed three-mark scalar ceiling

The six overlap cases contribute with the actual inverse-frame signs.
This scalar evaluation does not establish their applicability to any
physical marked block; the actual mixed geometry is proved separately.
Constructive mathematics only; no attacks or manuscript changes.
-/

noncomputable section
namespace AESConcrete.MarkedThreeNumbers

def groupedBound : ℝ := 20*(256/255)^5 *
  (ByteLineBounds.a3 + 6*(1/16)^2*LineOverlap.eta1 +
    3*(1/16)^4*LineOverlap.eta2 -
    3*(1/16)*(ContainmentCodeBounds.z3-ContainmentCodeBounds.h3) +
    6*(1/16)^3*MixedCodeBounds.f3 + (1/16)^5*ByteLineBounds.b3)

theorem groupedBound_lt_twenty_two : groupedBound < 22 := by
  norm_num [groupedBound, ByteLineBounds.a3, ByteLineBounds.cubeBound,
    ByteGramResources.cubeNumerator, ByteLineBounds.b3, ByteLineBounds.mixedCubeBound,
    LineOverlap.eta1, LineOverlap.eta2, LineOverlap.delta, LineOverlap.offdiag,
    ContainmentCodeBounds.z3, ContainmentCodeBounds.h3, MixedCodeBounds.f3]

end AESConcrete.MarkedThreeNumbers
