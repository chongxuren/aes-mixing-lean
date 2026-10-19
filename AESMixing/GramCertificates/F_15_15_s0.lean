import AESMixing.GramCases
namespace AESMixing.GramCertificates.F_15_15_s0
-- Generated witness data; checked below by the Lean kernel.
def certificates : Fin 25 → RankCertificate (BinaryWord 8) 16 8 :=
![{ rank := ⟨0, by decide⟩, pivots := ![], reduced := ![], leftInverse := ![] },
{ rank := ⟨1, by decide⟩, pivots := ![0], reduced := ![certificateRow 2374863873], leftInverse := ![certificateRow 2600990914393046777856] },
{ rank := ⟨1, by decide⟩, pivots := ![4], reduced := ![certificateRow 10199962666986897408], leftInverse := ![certificateRow 2600990914393046777856] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 2374863873, certificateRow 10199962666986897408], leftInverse := ![certificateRow 2600990914393046777856, certificateRow 11171170914511271600689696997376] },
{ rank := ⟨1, by decide⟩, pivots := ![0], reduced := ![certificateRow 10199962669361761281], leftInverse := ![certificateRow 2600990914393046777856] },
{ rank := ⟨1, by decide⟩, pivots := ![0], reduced := ![certificateRow 16974337], leftInverse := ![certificateRow 4722366482869645213696] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 3506503681, certificateRow 1744896256], leftInverse := ![certificateRow 494538761872079369273344, certificateRow 877493168842289660821504] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 16974337, certificateRow 10199962666986897408], leftInverse := ![certificateRow 4722366482869645213696, certificateRow 2600990914393046777856] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 3506503681, certificateRow 1744896256, certificateRow 10199962666986897408], leftInverse := ![certificateRow 494538761872079369273344, certificateRow 877493168842289660821504, certificateRow 11171170914511271600689696997376] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 13382956920604786689, certificateRow 15118980569582600448], leftInverse := ![certificateRow 494538761872079369273344, certificateRow 877493168842289660821504] },
{ rank := ⟨1, by decide⟩, pivots := ![4], reduced := ![certificateRow 72904222286282752], leftInverse := ![certificateRow 4722366482869645213696] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 2374863873, certificateRow 72904222286282752], leftInverse := ![certificateRow 2600990914393046777856, certificateRow 4722366482869645213696] },
{ rank := ⟨2, by decide⟩, pivots := ![4, 5], reduced := ![certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 494538761872079369273344, certificateRow 877493168842289660821504] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 4, 5], reduced := ![certificateRow 2374863873, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 2600990914393046777856, certificateRow 14657210556265016673248733036544, certificateRow 16558686839119045887935050153984] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 10128188745028832257, certificateRow 72904222286282752], leftInverse := ![certificateRow 7323357397262691991552, certificateRow 4722366482869645213696] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 16974337, certificateRow 72904222286282752], leftInverse := ![certificateRow 4722366482869645213696, certificateRow 20282409603651670423947251286016] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 3506503681, certificateRow 1744896256, certificateRow 72904222286282752], leftInverse := ![certificateRow 494538761872079369273344, certificateRow 877493168842289660821504, certificateRow 20282409603651670423947251286016] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 4, 5], reduced := ![certificateRow 16974337, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 4722366482869645213696, certificateRow 2109370598783186371744150400794624, certificateRow 3752245776679414397941646784200704] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 4, 5], reduced := ![certificateRow 3506503681, certificateRow 1744896256, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 494538761872079369273344, certificateRow 877493168842289660821504, certificateRow 2124027808844912626545319764557824, certificateRow 3768804462641040274987292173533184] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 14988544712372191233, certificateRow 7494272356177740032, certificateRow 72904222286282752], leftInverse := ![certificateRow 2129653008877964156386540754305024, certificateRow 3752245777553052197272531148734464, certificateRow 20282409603651670423947251286016] },
{ rank := ⟨1, by decide⟩, pivots := ![0], reduced := ![certificateRow 72904222303257089], leftInverse := ![certificateRow 4722366482869645213696] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 7546010324260945921, certificateRow 13389317937207247104], leftInverse := ![certificateRow 494538761872079369273344, certificateRow 877493168842289660821504] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 4], reduced := ![certificateRow 10128188742670942721, certificateRow 10199962666986897408], leftInverse := ![certificateRow 7323357397262691991552, certificateRow 2600990914393046777856] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 6668859083363254273, certificateRow 7494272356177740032, certificateRow 10199962666986897408], leftInverse := ![certificateRow 4119864945280507426943654690816, certificateRow 16558686842974415399340346441728, certificateRow 11171170914511271600689696997376] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 15060318636705120257, certificateRow 7494272356177740032], leftInverse := ![certificateRow 494538761872079369273344, certificateRow 877493168842289660821504] }]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem checked (t : Fin 25) : (certificates t).Valid (gramCaseMatrix false 15 15 (gramSubModeIndex 0 t)) := by
  fin_cases t <;> apply RankCertificate.valid_of_fast <;> decide
def ranks (t : Fin 25) : ℕ := (certificates t).rank.val
theorem counts (t : Fin 25) : gramCaseCount false 15 15 (gramSubModeIndex 0 t) = 256^(8-ranks t) :=
  gramCaseCount_from_certificate _ _ _ _ (certificates t) (checked t)
#print axioms counts
end AESMixing.GramCertificates.F_15_15_s0
