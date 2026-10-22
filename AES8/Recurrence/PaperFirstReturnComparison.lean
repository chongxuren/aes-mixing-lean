import AES8.Reductions.Source.PaperOneSourceReturn
import AES8.Recurrence.PaperComparisonMaps

/-! Exact finite comparisons for the frozen paper's first-return estimates.
These check the graph-defined coefficients, not empirical operators or samples.
Physical source lengths and the finite sharp-entry resource remain separate. -/
namespace AES8.PaperFirstReturnComparison
open PaperComparison
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def oneSource (a : Fin 14) : ℚ :=
  let (i,t) := typeOf a
  64 / (125 * scales a) *
    (PaperOneSourceReturn.coefficient i t 0 * (1000001/1000000) +
      PaperOneSourceReturn.coefficient i t 1 * (183/500))

theorem one_source_le (a : Fin 14) : oneSource a ≤ firstReturn a := by
  fin_cases a <;> decide +kernel

/-- The positive source vector .01*1 + .13*e2 + 48*e6 + 71*e9. -/
def severalSource : QProfile :=
  ![1/100,14/100,1/100,1/100,1/100,4801/100,1/100,
    1/100,7101/100,1/100,1/100,1/100,1/100,1/100]

def severalImageUpper : QProfile :=
  ![3/1000,21/1000,1085/1000,1085/1000,15/1000,419/1000,
    2590/1000,26707/1000,294/1000,223/1000,628/1000,429/1000,31/1000,1166/1000]

theorem several_image_le (a : Fin 14) :
    mv returnMatrix severalSource a ≤ severalImageUpper a := by
  fin_cases a <;> decide +kernel

theorem several_upper_le (a : Fin 14) : severalImageUpper a ≤ firstReturn a := by
  fin_cases a <;> decide +kernel

theorem several_source_le (a : Fin 14) :
    mv returnMatrix severalSource a ≤ firstReturn a :=
  (several_image_le a).trans (several_upper_le a)

end AES8.PaperFirstReturnComparison
