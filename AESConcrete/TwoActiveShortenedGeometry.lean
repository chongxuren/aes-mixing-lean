import AESConcrete.TwoActiveGeometry

/-!
# Actual one-output-zero lines inside the two-active source plane

Each line is identified with the actual shortened physical graph, with two
original inactive input zeros and one imposed output zero. Its residual input
and every remaining output coordinate are bijective parameters. These exact
geometry interfaces supply no amplitude or energy inequality and no new cap.

Future draft only; no compilation or acceptance is asserted. Constructive
mathematics only; no attacks or application execution. Independent retained
uniform keys, whitening, omitted final MixColumns, ordered-distinct reference
and fixed 10/14/16 remain unchanged. Existing sources and records are frozen.
-/

noncomputable section

namespace AESConcrete.TwoActiveShortenedGeometry
open AESMixing
open AESMixing.AES (maskBit maskSize)
open AESConcrete.ResidualIncidenceCoefficient (SelectedSupport)
open AESConcrete.TwoActiveSource
open AESConcrete.TwoActiveGeometry
open AESConcrete.ShortenedLineResponse (singletonMask singletonMask_bit singletonMask_size)

section Generic
variable {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]

/-- An actual output-zero restriction of the original two-coordinate source. -/
abbrev zeroLine (L : (Fin 4 → V) →+ (Fin 4 → V)) (p : SelectedSupport 1 2) (i : Fin 4) :=
  {uv : V × V // L (source p uv.1 uv.2) i = 0}

/-- Exact physical graph, with no code indicator or source cardinality factor. -/
def zeroLineEquiv (L : (Fin 4 → V) →+ (Fin 4 → V)) (p : SelectedSupport 1 2) (i : Fin 4) :
    zeroLine L p i ≃ ShortenedGraph L (singletonMask i) p.val.val.2 where
  toFun uv := ⟨source p uv.val.1 uv.val.2, by
    constructor
    · intro j hj
      have he : j = i := (singletonMask_bit i j).mp hj
      simpa only [he] using uv.property
    · exact source_onPlane p uv.val.1 uv.val.2⟩
  invFun x := ⟨(x.val (residualLabel p), x.val (uniformLabel p)), by
    change L (source p (x.val (residualLabel p)) (x.val (uniformLabel p))) i = 0
    rw [source_reconstruct p x.val x.property.2]
    exact x.property.1 i ((singletonMask_bit i i).mpr rfl)⟩
  left_inv uv := by
    apply Subtype.ext
    exact Prod.ext (source_residual p uv.val.1 uv.val.2) (source_uniform p uv.val.1 uv.val.2)
  right_inv x := by
    apply Subtype.ext
    exact source_reconstruct p x.val x.property.2

theorem zeroLine_shortening (p : SelectedSupport 1 2) (i : Fin 4) :
    maskSize (singletonMask i) + maskSize p.val.val.2 = 3 := by
  rw [singletonMask_size]
  have hp := p.property
  omega

/-- The original signed residual value is an exact line parameter. -/
theorem zeroLine_residual_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (i : Fin 4) :
    Function.Bijective (fun uv : zeroLine L p i => uv.val.1) := by
  have hb := (ShortenedLineResponse.input_coordinate_bijective L hL
    (singletonMask i) p.val.val.2 (zeroLine_shortening p i)
    (residualLabel p) (residualLabel_not_inactive p)).comp (zeroLineEquiv L p i).bijective
  change Function.Bijective
    (fun uv : zeroLine L p i => source p uv.val.1 uv.val.2 (residualLabel p)) at hb
  simpa only [source_residual] using hb

/-- Each physical output other than the imposed zero is an exact line parameter. -/
theorem zeroLine_output_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (i k : Fin 4) (hk : k ≠ i) :
    Function.Bijective (fun uv : zeroLine L p i => L (source p uv.val.1 uv.val.2) k) := by
  have hbit : maskBit (singletonMask i) k ≠ true := by
    intro hbit
    exact hk ((singletonMask_bit i k).mp hbit)
  exact (ShortenedLineResponse.output_coordinate_bijective L hL
    (singletonMask i) p.val.val.2 (zeroLine_shortening p i) k hbit).comp
      (zeroLineEquiv L p i).bijective

omit [DecidableEq V] in
/-- The `v=0` source axis also has every physical output as a bijective parameter. -/
theorem residual_axis_coordinate_bijective
    (L : (Fin 4 → V) →+ (Fin 4 → V)) (hL : ZeroMDS L)
    (p : SelectedSupport 1 2) (i : Fin 4) :
    Function.Bijective (fun u : V => L (source p u 0) i) := by
  have he : (fun u : V => L (source p u 0) i) =
      singletonCoordinateEquiv L hL (residualLabel p) i := by
    funext u
    rw [singletonCoordinateEquiv_apply, source_residual_axis]
  rw [he]
  exact (singletonCoordinateEquiv L hL (residualLabel p) i).bijective

end Generic

theorem word_zeroLine_residual_bijective (p : SelectedSupport 1 2) (i : Fin 4) :
    Function.Bijective (fun uv : zeroLine WordCrossZero.wordMixAddEquiv.toAddMonoidHom p i =>
      uv.val.1) :=
  zeroLine_residual_bijective WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS p i

theorem word_zeroLine_output_bijective (p : SelectedSupport 1 2) (i k : Fin 4) (hk : k ≠ i) :
    Function.Bijective (fun uv : zeroLine WordCrossZero.wordMixAddEquiv.toAddMonoidHom p i =>
      WordCrossZero.wordMixAddEquiv (source p uv.val.1 uv.val.2) k) :=
  zeroLine_output_bijective WordCrossZero.wordMixAddEquiv.toAddMonoidHom
    WordCrossZero.wordMixAddEquiv_zeroMDS p i k hk

end AESConcrete.TwoActiveShortenedGeometry
