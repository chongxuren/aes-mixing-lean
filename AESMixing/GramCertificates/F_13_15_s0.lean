import AESMixing.GramCases
namespace AESMixing.GramCertificates.F_13_15_s0
-- Generated witness data; checked below by the Lean kernel.
def certificates : Fin 25 → RankCertificate (BinaryWord 8) 16 8 :=
![{ rank := ⟨1, by decide⟩, pivots := ![1], reduced := ![certificateRow 256], leftInverse := ![certificateRow 256] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 2374828033, certificateRow 256], leftInverse := ![certificateRow 2600990914393046813696, certificateRow 256] },
{ rank := ⟨2, by decide⟩, pivots := ![1, 4], reduced := ![certificateRow 256, certificateRow 10199962666986897408], leftInverse := ![certificateRow 256, certificateRow 2600990914393046777856] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 2374828033, certificateRow 256, certificateRow 10199962666986897408], leftInverse := ![certificateRow 2600990914393046813696, certificateRow 256, certificateRow 11171170914511271600689696997376] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 10199962669361725441, certificateRow 256], leftInverse := ![certificateRow 2600990914393046813696, certificateRow 256] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 16973825, certificateRow 256], leftInverse := ![certificateRow 4722366482869645214208, certificateRow 256] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 2], reduced := ![certificateRow 3103784961, certificateRow 256, certificateRow 1744896000], leftInverse := ![certificateRow 988893056303421643030784, certificateRow 256, certificateRow 877493168842289660821760] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 16973825, certificateRow 256, certificateRow 10199962666986897408], leftInverse := ![certificateRow 4722366482869645214208, certificateRow 256, certificateRow 2600990914393046777856] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 2, 4], reduced := ![certificateRow 3103784961, certificateRow 256, certificateRow 1744896000, certificateRow 10199962666986897408], leftInverse := ![certificateRow 988893056303421643030784, certificateRow 256, certificateRow 877493168842289660821760, certificateRow 11171170914511271600689696997376] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 2], reduced := ![certificateRow 7523466384118906881, certificateRow 256, certificateRow 15118980569582600192], leftInverse := ![certificateRow 988893056303421643030784, certificateRow 256, certificateRow 877493168842289660821760] },
{ rank := ⟨2, by decide⟩, pivots := ![1, 4], reduced := ![certificateRow 256, certificateRow 72904222286282752], leftInverse := ![certificateRow 256, certificateRow 4722366482869645213696] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 2374828033, certificateRow 256, certificateRow 72904222286282752], leftInverse := ![certificateRow 2600990914393046813696, certificateRow 256, certificateRow 4722366482869645213696] },
{ rank := ⟨3, by decide⟩, pivots := ![1, 4, 5], reduced := ![certificateRow 256, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 256, certificateRow 494538761872079369273344, certificateRow 877493168842289660821504] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 4, 5], reduced := ![certificateRow 2374828033, certificateRow 256, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 2600990914393046813696, certificateRow 256, certificateRow 14657210556265016673248733036544, certificateRow 16558686839119045887935050153984] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 10128188745028796417, certificateRow 256, certificateRow 72904222286282752], leftInverse := ![certificateRow 7323357397262692027392, certificateRow 256, certificateRow 4722366482869645213696] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 16973825, certificateRow 256, certificateRow 72904222286282752], leftInverse := ![certificateRow 4722366482869645214208, certificateRow 256, certificateRow 20282409603651670423947251286016] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 2, 4], reduced := ![certificateRow 3103784961, certificateRow 256, certificateRow 1744896000, certificateRow 72904222286282752], leftInverse := ![certificateRow 988893056303421643030784, certificateRow 256, certificateRow 877493168842289660821760, certificateRow 20282409603651670423947251286016] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 4, 5], reduced := ![certificateRow 16973825, certificateRow 256, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 4722366482869645214208, certificateRow 256, certificateRow 2109370598783186371744150400794624, certificateRow 3752245776679414397941646784200704] },
{ rank := ⟨5, by decide⟩, pivots := ![0, 1, 2, 4, 5], reduced := ![certificateRow 3103784961, certificateRow 256, certificateRow 1744896000, certificateRow 15060318633198616576, certificateRow 7494272354432843776], leftInverse := ![certificateRow 988893056303421643030784, certificateRow 256, certificateRow 877493168842289660821760, certificateRow 2124027808844912626545319764557824, certificateRow 3768804462641040274987292173533184] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 2, 4], reduced := ![certificateRow 13259445029547540481, certificateRow 256, certificateRow 7494272356177739776, certificateRow 72904222286282752], leftInverse := ![certificateRow 4218741198548440504484449910522112, certificateRow 256, certificateRow 3752245777553052197272531148734720, certificateRow 20282409603651670423947251286016] },
{ rank := ⟨2, by decide⟩, pivots := ![0, 1], reduced := ![certificateRow 72904222303256577, certificateRow 256], leftInverse := ![certificateRow 4722366482869645214208, certificateRow 256] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 2], reduced := ![certificateRow 15089514861907935233, certificateRow 256, certificateRow 13389317937207246848], leftInverse := ![certificateRow 988893056303421643030784, certificateRow 256, certificateRow 877493168842289660821760] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 4], reduced := ![certificateRow 10128188742670942209, certificateRow 256, certificateRow 10199962666986897408], leftInverse := ![certificateRow 7323357397262691992064, certificateRow 256, certificateRow 2600990914393046777856] },
{ rank := ⟨4, by decide⟩, pivots := ![0, 1, 2, 4], reduced := ![certificateRow 3786837895931756545, certificateRow 256, certificateRow 7494272356177739776, certificateRow 10199962666986897408], leftInverse := ![certificateRow 18143250204659589612343207657728, certificateRow 256, certificateRow 16558686842974415399340346441984, certificateRow 11171170914511271600689696997376] },
{ rank := ⟨3, by decide⟩, pivots := ![0, 1, 2], reduced := ![certificateRow 13330656003927048193, certificateRow 256, certificateRow 7494272356177739776], leftInverse := ![certificateRow 988893056303421643030784, certificateRow 256, certificateRow 877493168842289660821760] }]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem checked (t : Fin 25) : (certificates t).Valid (gramCaseMatrix false 13 15 (gramSubModeIndex 0 t)) := by
  fin_cases t <;> apply RankCertificate.valid_of_fast <;> decide
def ranks (t : Fin 25) : ℕ := (certificates t).rank.val
theorem counts (t : Fin 25) : gramCaseCount false 13 15 (gramSubModeIndex 0 t) = 256^(8-ranks t) :=
  gramCaseCount_from_certificate _ _ _ _ (certificates t) (checked t)
#print axioms counts
end AESMixing.GramCertificates.F_13_15_s0
