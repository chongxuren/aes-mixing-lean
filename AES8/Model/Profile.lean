import AES8.Math.Imports

/-! The common fourteen-coordinate profile type and scalar multiplication.
This interface contains no numerical profile, comparison matrix or AES bound.
Historical/Data supplies the old constants; Model/SupportProfile constructs
actual support profiles. Declaration names are retained for compatibility. -/
noncomputable section
namespace AES8
abbrev Profile := Fin 14 → ℝ
def scale (a : ℝ) (x : Profile) : Profile := fun i => a * x i
end AES8
