import AESMixing.GramCases
namespace AESMixing.GramCertificates.I_15_15_s0
-- Generated witness data; checked below by the Lean kernel.
def certificates : Fin 25 → RankCertificate (BinaryWord 8) 16 8 :=
![{ rank := ⟨0, by decide⟩, pivots := ![], reduced := ![], leftInverse := ![] },
{ rank := ⟨1, by decide⟩, pivots := ![0], reduced := ![certificateRow 2352307457], leftInverse := ![certificateRow 4224304392879487320064] },
{ rank := ⟨1, by decide⟩, pivots := ![4], reduced := ![certificateRow 10103083597951926272], leftInverse := ![certificateRow 4224304392879487320064] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 2352307457, certificateRow 10103083597951926272], leftInverse := ![certificateRow 4224304392879487320064, certificateRow 18143249215766533308921564626944] },
{ rank := ⟨1, by decide⟩, pivots := ![0], reduced := ![certificateRow 10103083600304233729], leftInverse := ![certificateRow 4224304392879487320064] },
{ rank := ⟨1, by decide⟩, pivots := ![0], reduced := ![certificateRow 648017665], leftInverse := ![certificateRow 373066952146701971881984] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 3513253889, certificateRow 16843008], leftInverse := ![certificateRow 878397059301901428850688, certificateRow 9500073197960419082240] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 648017665, certificateRow 10103083597951926272], leftInverse := ![certificateRow 373066952146701971881984, certificateRow 4224304392879487320064] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 3513253889, certificateRow 16843008, certificateRow 10103083597951926272], leftInverse := ![certificateRow 878397059301901428850688, certificateRow 9500073197960419082240, certificateRow 18143249215766533308921564626944] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 1304379355105329153, certificateRow 1952060926651859200], leftInverse := ![certificateRow 878397059301901428850688, certificateRow 9500073197960419082240] },
{ rank := ⟨1, by decide⟩, pivots := ![4], reduced := ![certificateRow 2783214678405283840], leftInverse := ![certificateRow 373066952146701971881984] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 2352307457, certificateRow 2783214678405283840], leftInverse := ![certificateRow 4224304392879487320064, certificateRow 373066952146701971881984] },
{ rank := ⟨2, by decide⟩, pivots := ![4, 5], reduced := ![certificateRow 15089310555799814144, certificateRow 72340168526266368], leftInverse := ![certificateRow 878397059301901428850688, certificateRow 9500073197960419082240] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 4, 5], reduced := ![certificateRow 2352307457, certificateRow 15089310555799814144, certificateRow 72340168526266368], leftInverse := ![certificateRow 4224304392879487320064, certificateRow 158457203388694488941097648128, certificateRow 237684496987525978519922278400] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 12297828651817590017, certificateRow 2783214678405283840], leftInverse := ![certificateRow 377291256539581459202048, certificateRow 373066952146701971881984] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 648017665, certificateRow 2783214678405283840], leftInverse := ![certificateRow 373066952146701971881984, certificateRow 1602310358688481963491832851595264] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 3513253889, certificateRow 16843008, certificateRow 2783214678405283840], leftInverse := ![certificateRow 878397059301901428850688, certificateRow 9500073197960419082240, certificateRow 1602310358688481963491832851595264] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 4, 5], reduced := ![certificateRow 648017665, certificateRow 15089310555799814144, certificateRow 72340168526266368], leftInverse := ![certificateRow 373066952146701971881984, certificateRow 3772528186279247592342336158302208, certificateRow 40564819207358681080115631226880] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 4, 5], reduced := ![certificateRow 3513253889, certificateRow 16843008, certificateRow 15089310555799814144, certificateRow 72340168526266368], leftInverse := ![certificateRow 878397059301901428850688, certificateRow 9500073197960419082240, certificateRow 3772686642604239227529375827099648, certificateRow 40802503694846133860675134423040] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 17868021629501046785, certificateRow 72340168543109376, certificateRow 2783214678405283840], leftInverse := ![certificateRow 4969190353773056313168977993924608, certificateRow 40564819216803414045854921654272, certificateRow 1602310358688481963491832851595264] },
{ rank := ⟨1, by decide⟩, pivots := ![0], reduced := ![certificateRow 2783214679053301505], leftInverse := ![certificateRow 373066952146701971881984] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 14083343302064078849, certificateRow 1879720758125592832], leftInverse := ![certificateRow 878397059301901428850688, certificateRow 9500073197960419082240] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 12297828650113300225, certificateRow 10103083597951926272], leftInverse := ![certificateRow 377291256539581459202048, certificateRow 4224304392879487320064] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 6727635676456026113, certificateRow 72340168543109376, certificateRow 10103083597951926272], leftInverse := ![certificateRow 18301706419192121286010081378304, certificateRow 237684497042866210741050933248, certificateRow 18143249215766533308921564626944] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 15089310559313068033, certificateRow 72340168543109376], leftInverse := ![certificateRow 878397059301901428850688, certificateRow 9500073197960419082240] }]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem checked (t : Fin 25) : (certificates t).Valid (gramCaseMatrix true 15 15 (gramSubModeIndex 0 t)) := by
  fin_cases t <;> apply RankCertificate.valid_of_fast <;> decide
def ranks (t : Fin 25) : ℕ := (certificates t).rank.val
theorem counts (t : Fin 25) : gramCaseCount true 15 15 (gramSubModeIndex 0 t) = 256^(8-ranks t) :=
  gramCaseCount_from_certificate _ _ _ _ (certificates t) (checked t)
#print axioms counts
end AESMixing.GramCertificates.I_15_15_s0
