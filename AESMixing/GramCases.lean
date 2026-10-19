import AESMixing.ConstraintCount
import AESMixing.FastRankCertificate

/-! A fixed, exhaustive index for the Gram constraint certificates.
The Boolean orientation selects actual forward or inverse MixColumns.
The 625 modes are all four-tuples over the five constraint atoms. -/
namespace AESMixing

def gramMixing (inverse : Bool) : Fin 4 → Fin 4 → BinaryWord 8 :=
  if inverse then fun i j => ⟨AES.minorInverse 15 15 i j⟩
  else fun i j => ⟨AES.mixEntry i j⟩

def gramModes (i : Fin 625) : Fin 4 → Fin 5 := finFunctionFinEquiv.symm i

theorem gramModes_exhaustive (m : Fin 4 → Fin 5) : ∃ i : Fin 625, gramModes i = m :=
  ⟨finFunctionFinEquiv m, finFunctionFinEquiv.symm_apply_apply m⟩

def gramModeIndex (block : Fin 5) (i : Fin 125) : Fin 625 :=
  ⟨125*block.val+i.val, by omega⟩

def gramBlock (i : Fin 625) : Fin 5 := ⟨i.val/125, by omega⟩
def gramWithinBlock (i : Fin 625) : Fin 125 := ⟨i.val%125, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
theorem gramBlock_index : ∀ b : Fin 5, ∀ t : Fin 125,
    gramBlock (gramModeIndex b t) = b := by decide

set_option maxRecDepth 100000 in
theorem gramWithinBlock_index : ∀ b : Fin 5, ∀ t : Fin 125,
    gramWithinBlock (gramModeIndex b t) = t := by decide

set_option maxRecDepth 100000 in
theorem gramModeIndex_split : ∀ i : Fin 625,
    gramModeIndex (gramBlock i) (gramWithinBlock i) = i := by decide

def gramSubModeIndex (block i : Fin 25) : Fin 625 :=
  ⟨25*block.val+i.val, by omega⟩

def gramSubBlock (i : Fin 625) : Fin 25 := ⟨i.val/25, by omega⟩
def gramSubWithin (i : Fin 625) : Fin 25 := ⟨i.val%25, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
theorem gramSubBlock_index : ∀ b t : Fin 25, gramSubBlock (gramSubModeIndex b t) = b := by decide

set_option maxRecDepth 100000 in
theorem gramSubWithin_index : ∀ b t : Fin 25, gramSubWithin (gramSubModeIndex b t) = t := by decide

set_option maxRecDepth 100000 in
theorem gramSubModeIndex_split : ∀ i : Fin 625,
    gramSubModeIndex (gramSubBlock i) (gramSubWithin i) = i := by decide

theorem gramModeIndex_exhaustive (i : Fin 625) :
    ∃ b : Fin 5, ∃ t : Fin 125, gramModeIndex b t = i := by
  refine ⟨⟨i.val/125, by omega⟩, ⟨i.val%125, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  simp only [gramModeIndex]
  omega

def gramCaseMatrix (inverse : Bool) (a b : Fin 16) (i : Fin 625) :
    Fin 16 → Fin 8 → BinaryWord 8 := constraintMatrix (gramMixing inverse) a b (gramModes i)

noncomputable def gramCaseCount (inverse : Bool) (a b : Fin 16) (i : Fin 625) : ℕ :=
  Nat.card (fieldMatrix (gramCaseMatrix inverse a b i)).ker

theorem gramCaseCount_from_certificate (inverse : Bool) (a b : Fin 16) (i : Fin 625)
    (c : RankCertificate (BinaryWord 8) 16 8) (h : c.Valid (gramCaseMatrix inverse a b i)) :
    gramCaseCount inverse a b i = 256^(8-c.rank.val) :=
  byte_rank_certificate_card c _ h

end AESMixing
