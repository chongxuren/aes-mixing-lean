import AES8.Recurrence.PaperComparisonMaps

/-!
# Fifty-six fixed rational profile-image comparisons

The statements check the common graph-defined maps on exactly the frozen
startup and alternating profiles. `decide +kernel` uses kernel reduction;
no native computation axiom, numerical search or AES norm hypothesis is used.
-/
namespace AES8.PaperComparison
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

 theorem step_00 : stepMatrix 0 0 =
    37778931862957161709568/340282366920938463463374607431768211455 := by decide +kernel
 theorem return_00 : returnMatrix 0 0 =
    14837361170942393319424/73359409684188986467870553125 := by decide +kernel

 theorem startup_even_test (i : Fin 14) :
    startup2 i ≤ ratioPermille i / 1000 * evenEnvelope i := by
  fin_cases i <;> decide +kernel

 theorem startup_odd_test (i : Fin 14) :
    startup3 i ≤ ratioPermille i / 1000 * oddEnvelope i := by
  fin_cases i <;> decide +kernel

 theorem invariant_even_test (i : Fin 14) :
    invariantEven i ≤ ratioPermille i / 1000 * evenEnvelope i := by
  fin_cases i <;> decide +kernel

 theorem invariant_odd_test (i : Fin 14) :
    invariantOdd i ≤ ratioPermille i / 1000 * oddEnvelope i := by
  fin_cases i <;> decide +kernel

end AES8.PaperComparison
