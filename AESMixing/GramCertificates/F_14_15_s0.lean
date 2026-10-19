import AESMixing.GramCases
namespace AESMixing.GramCertificates.F_14_15_s0
-- Generated witness data; checked below by the Lean kernel.
def certificates : Fin 25 → RankCertificate (BinaryWord 8) 16 8 :=
![{ rank := ⟨1, by decide⟩, pivots := ![0], reduced := ![certificateRow 1], leftInverse := ![certificateRow 1] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 1, certificateRow 4143317248], leftInverse := ![certificateRow 1, certificateRow 4537899042132549697783] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 1, certificateRow 10199962666986897408], leftInverse := ![certificateRow 1, certificateRow 2600990914393046777856] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 1, certificateRow 4143317248, certificateRow 10199962666986897408], leftInverse := ![certificateRow 1, certificateRow 4537899042132549697783, certificateRow 11171170914511271600689696997376] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 1, certificateRow 17795413142112960768], leftInverse := ![certificateRow 1, certificateRow 4537899042132549697783] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 1, certificateRow 2374762752], leftInverse := ![certificateRow 1, certificateRow 665853674084619975131277] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 2], reduced := ![certificateRow 1, certificateRow 3103785216, certificateRow 3506503680], leftInverse := ![certificateRow 1, certificateRow 988893056303421643030529, certificateRow 494538761872079369273345] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 1, certificateRow 2374762752, certificateRow 10199962666986897408], leftInverse := ![certificateRow 1, certificateRow 665853674084619975131277, certificateRow 2600990914393046777856] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 2, 4], reduced := ![certificateRow 1, certificateRow 3103785216, certificateRow 3506503680, certificateRow 10199962666986897408], leftInverse := ![certificateRow 1, certificateRow 988893056303421643030529, certificateRow 494538761872079369273345, certificateRow 11171170914511271600689696997376] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 2], reduced := ![certificateRow 1, certificateRow 7523466384118907136, certificateRow 13382956920604786688], leftInverse := ![certificateRow 1, certificateRow 988893056303421643030529, certificateRow 494538761872079369273345] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 1, certificateRow 72904222286282752], leftInverse := ![certificateRow 1, certificateRow 4722366482869645213696] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 1, certificateRow 4143317248, certificateRow 72904222286282752], leftInverse := ![certificateRow 1, certificateRow 4537899042132549697783, certificateRow 4722366482869645213696] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 4, 5], reduced := ![certificateRow 1, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 1, certificateRow 494538761872079369273344, certificateRow 877493168842289660821504] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 4, 5], reduced := ![certificateRow 1, certificateRow 4143317248, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 1, certificateRow 4537899042132549697783, certificateRow 14657210556265016673248733036544, certificateRow 16558686839119045887935050153984] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 1, certificateRow 141005773335822592, certificateRow 72904222286282752], leftInverse := ![certificateRow 1, certificateRow 1170962420310934917480695, certificateRow 4722366482869645213696] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 1, certificateRow 2374762752, certificateRow 72904222286282752], leftInverse := ![certificateRow 1, certificateRow 665853674084619975131277, certificateRow 20282409603651670423947251286016] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 2, 4], reduced := ![certificateRow 1, certificateRow 3103785216, certificateRow 3506503680, certificateRow 72904222286282752], leftInverse := ![certificateRow 1, certificateRow 988893056303421643030529, certificateRow 494538761872079369273345, certificateRow 20282409603651670423947251286016] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 4, 5], reduced := ![certificateRow 1, certificateRow 2374762752, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 1, certificateRow 665853674084619975131277, certificateRow 2109370598783186371744150400794624, certificateRow 3752245776679414397941646784200704] },
{ rank := ⟨5, by decide⟩, pivots := ![0, 1, 2, 4, 5], reduced := ![certificateRow 1, certificateRow 3103785216, certificateRow 3506503680, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 1, certificateRow 988893056303421643030529, certificateRow 494538761872079369273345, certificateRow 2124027808844912626545319764557824, certificateRow 3768804462641040274987292173533184] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 2, 4], reduced := ![certificateRow 1, certificateRow 13259445029547540736, certificateRow 14988544712372191232, certificateRow 72904222286282752], leftInverse := ![certificateRow 1, certificateRow 4218741198548440504484449910521857, certificateRow 2129653008877964156386540754305025, certificateRow 20282409603651670423947251286016] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 1, certificateRow 10199528963564110080], leftInverse := ![certificateRow 1, certificateRow 665853674084619975131277] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 2], reduced := ![certificateRow 1, certificateRow 15089514861907935488, certificateRow 7546010324260945920], leftInverse := ![certificateRow 1, certificateRow 988893056303421643030529, certificateRow 494538761872079369273345] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 1, certificateRow 5064094373701746944, certificateRow 10199962666986897408], leftInverse := ![certificateRow 1, certificateRow 669598363131583014109325, certificateRow 2600990914393046777856] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 2, 4], reduced := ![certificateRow 1, certificateRow 3786837895931756800, certificateRow 6668859083363254272, certificateRow 10199962666986897408], leftInverse := ![certificateRow 1, certificateRow 18143250204659589612343207657473, certificateRow 4119864945280507426943654690817, certificateRow 11171170914511271600689696997376] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 2], reduced := ![certificateRow 1, certificateRow 13330656003927048448, certificateRow 15060318636705120256], leftInverse := ![certificateRow 1, certificateRow 988893056303421643030529, certificateRow 494538761872079369273345] }]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem checked (t : Fin 25) : (certificates t).Valid (gramCaseMatrix false 14 15 (gramSubModeIndex 0 t)) := by
  fin_cases t <;> apply RankCertificate.valid_of_fast <;> decide
def ranks (t : Fin 25) : ℕ := (certificates t).rank.val
theorem counts (t : Fin 25) : gramCaseCount false 14 15 (gramSubModeIndex 0 t) = 256^(8-ranks t) :=
  gramCaseCount_from_certificate _ _ _ _ (certificates t) (checked t)
#print axioms counts
end AESMixing.GramCertificates.F_14_15_s0
