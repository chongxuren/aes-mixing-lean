"""Emit the fixed pilot-row and complete-inventory Lean assembly modules.

Each callback receives a project-relative POSIX path and UTF-8 bytes. The
generated text preserves the checked certificate's module names and contents.
"""

PREFIX = "AES8/Estimates/Word/"
OPTIONS = (
    "set_option Elab.async false\n"
    "set_option maxRecDepth 65536\n"
    "set_option maxHeartbeats 80000000\n"
)


def emit_pilot_wrappers(write_callback):
    """Emit the 18 assembly modules for the historically named alpha-13 row."""
    base = "PaperSharpEntriesRow13"
    interface = base + "Interface"
    raw = (
        "import AES8.Estimates.Word.PaperSharpEntriesPairCoverage\n"
        f"namespace AES8.{interface}\n"
        "@[irreducible] def Cell (b : Fin 255) : Prop := "
        "AES8.PaperSharpEntriesPairCoverage.PairCells (12 : Fin 255) b\n"
        f"end AES8.{interface}\n"
    )
    write_callback(PREFIX + interface + ".lean", raw.encode("utf8"))
    for block in range(16):
        first = block * 16
        name = base + f"Block{block:02d}"
        raw = "".join(
            f"import AES8.Estimates.Word.PaperSharpEntriesPairB{b + 1}\n"
            for b in range(first, min(first + 16, 255))
        )
        raw += "import AES8.Estimates.Word.PaperSharpEntriesCoefficientCertificate\n"
        raw += f"import AES8.Estimates.Word.{interface}\nnamespace AES8.{name}\n"
        raw += f"open AES8.{interface} AES8.PaperSharpEntriesCoefficientCertificate\n"
        raw += OPTIONS
        raw += (
            f"theorem cells (b : Fin 16) (hb : {first}+b.val < 255) : "
            f"Cell ⟨{first}+b.val,hb⟩ := by\n  fin_cases b\n"
        )
        for b in range(first, min(first + 16, 255)):
            caps = f"(AES8.PaperSharpEntriesPairB{b + 1}.caps coefficient_spec)"
            raw += (
                f"  · exact (show Cell ({b} : Fin 255) from by\n"
                "      unfold Cell\n"
                f"      exact ⟨{caps}.1, {caps}.2.1, {caps}.2.2⟩)\n"
            )
        if block == 15:
            raw += "  · norm_num at hb\n"
        raw += f"end AES8.{name}\n"
        write_callback(PREFIX + name + ".lean", raw.encode("utf8"))
    raw = "".join(
        f"import AES8.Estimates.Word.{base}Block{block:02d}\n"
        for block in range(16)
    )
    raw += f"namespace AES8.{base}\n"
    raw += f"open AES8.PaperSharpEntriesPairCoverage AES8.{interface}\n" + OPTIONS
    raw += """theorem row_cells : RowCells (12 : Fin 255) := by
  intro b
  have blocks (a t : Fin 16) (hb : a.val*16+t.val < 255) :
      Cell ⟨a.val*16+t.val,hb⟩ := by
    fin_cases a
"""
    raw += "".join(
        f"    · exact AES8.{base}Block{block:02d}.cells t hb\n"
        for block in range(16)
    )
    raw += """  let a : Fin 16 := ⟨b.val / 16, by omega⟩
  let t : Fin 16 := ⟨b.val % 16, by omega⟩
  have hb : a.val*16+t.val < 255 := by dsimp [a,t]; omega
  have hi : (⟨a.val*16+t.val,hb⟩ : Fin 255) = b := by
    apply Fin.ext
    dsimp [a,t]
    omega
  have result := blocks a t hb
  rw [hi] at result
  unfold Cell at result
  exact result

#print axioms row_cells
end AES8.PaperSharpEntriesRow13
"""
    write_callback(PREFIX + base + ".lean", raw.encode("utf8"))


def emit_complete(write_callback):
    """Emit the 18 modules combining all 255 rows into the full inventory."""
    base = "PaperSharpEntriesComplete"
    interface = base + "Interface"
    raw = (
        "import AES8.Estimates.Word.PaperSharpEntriesPairCoverage\n"
        f"namespace AES8.{interface}\n"
        "@[irreducible] def Row (a : Fin 255) : Prop := "
        "AES8.PaperSharpEntriesPairCoverage.RowCells a\n"
        f"end AES8.{interface}\n"
    )
    write_callback(PREFIX + interface + ".lean", raw.encode("utf8"))

    def row(alpha):
        return "PaperSharpEntriesRow13" if alpha == 13 else f"PaperSharpEntriesRowA{alpha:03d}"

    for block in range(16):
        first = block * 16
        name = base + f"Block{block:02d}"
        raw = "".join(
            f"import AES8.Estimates.Word.{row(a + 1)}\n"
            for a in range(first, min(first + 16, 255))
        )
        raw += f"import AES8.Estimates.Word.{interface}\nnamespace AES8.{name}\n"
        raw += f"open AES8.{interface}\n" + OPTIONS
        raw += (
            f"theorem rows (a : Fin 16) (ha : {first}+a.val < 255) : "
            f"Row ⟨{first}+a.val,ha⟩ := by\n  fin_cases a\n"
        )
        for a in range(first, min(first + 16, 255)):
            raw += (
                f"  · exact (show Row ({a} : Fin 255) from by\n"
                "      unfold Row\n"
                f"      exact AES8.{row(a + 1)}.row_cells)\n"
            )
        if block == 15:
            raw += "  · norm_num at ha\n"
        raw += f"end AES8.{name}\n"
        write_callback(PREFIX + name + ".lean", raw.encode("utf8"))
    raw = "".join(
        f"import AES8.Estimates.Word.{base}Block{block:02d}\n"
        for block in range(16)
    )
    raw += f"namespace AES8.{base}\n"
    raw += (
        "open AES8.PaperSharpEntriesPairCoverage "
        f"AES8.PaperSharpEntriesInventoryAssembly AES8.{interface}\n"
    ) + OPTIONS
    raw += """theorem all_rows : ∀ a : Fin 255, RowCells a := by
  intro a
  have blocks (b t : Fin 16) (ha : b.val*16+t.val < 255) :
      Row ⟨b.val*16+t.val,ha⟩ := by
    fin_cases b
"""
    raw += "".join(
        f"    · exact AES8.{base}Block{block:02d}.rows t ha\n"
        for block in range(16)
    )
    raw += """  let b : Fin 16 := ⟨a.val / 16, by omega⟩
  let t : Fin 16 := ⟨a.val % 16, by omega⟩
  have ha : b.val*16+t.val < 255 := by dsimp [b,t]; omega
  have hi : (⟨b.val*16+t.val,ha⟩ : Fin 255) = a := by
    apply Fin.ext
    dsimp [b,t]
    omega
  have result := blocks b t ha
  rw [hi] at result
  unfold Row at result
  exact result

theorem complete_inventory : CompleteInventory := complete_inventory_of_rows all_rows
theorem ordinary_raw_bound : AES8.PaperSharpEntriesFinite.OrdinaryRawBound :=
  (required_raw_bounds_of_rows all_rows).1
theorem fourier_raw_bound : AES8.PaperSharpEntriesFinite.FourierRawBound AES8.PaperSharpEntriesFinite.fourierMapHom :=
  (required_raw_bounds_of_rows all_rows).2
#print axioms complete_inventory
#print axioms ordinary_raw_bound
#print axioms fourier_raw_bound
end AES8.PaperSharpEntriesComplete
"""
    write_callback(PREFIX + base + ".lean", raw.encode("utf8"))
