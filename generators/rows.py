#!/usr/bin/env python3
"""Render fixed-row Lean certificates from integer transform transcripts.

``emit_row(alpha, data_path, write)`` emits one ordinary row (alpha != 13).
``emit_pairs(13, data_path, write, legacy_names=True)`` emits the pilot pairs;
their historical row wrappers are supplied by the assembly generator.
The callback receives a project-relative POSIX path and UTF-8 source bytes.
Only checking the resulting Lean declarations certifies the arithmetic.
"""

import argparse
import json
from pathlib import Path
import sys


PREFIX = "AES8/Estimates/Word/"
CASES = ((0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3))
OPTIONS = (
    "set_option Elab.async false\n"
    "set_option maxRecDepth 65536\n"
    "set_option maxHeartbeats 80000000\n"
)


def _check_alpha(alpha):
    if type(alpha) is not int or not 1 <= alpha <= 255:
        raise ValueError("alpha must be an integer from 1 to 255")


def _packed(values):
    offset = max(0, -min(values))
    width = max(1, (max(values) + offset).bit_length())
    word = sum((value + offset) << (width * i)
               for i, value in enumerate(values))
    return "packedVector %d %d %d" % (word, width, offset)


def _read_case(stream, alpha, beta, family, power):
    line = stream.readline()
    if not line:
        raise ValueError("missing transform case for (%d, %d, %d, %d)" %
                         (alpha, beta, family, power))
    case = json.loads(line)
    expected = {"alpha": alpha, "beta": beta,
                "family": family, "power": power}
    for key, value in expected.items():
        if type(case.get(key)) is not int or case[key] != value:
            raise ValueError("unexpected transform case: " + key)
    stages = case.get("stages")
    if not isinstance(stages, list) or len(stages) != 9:
        raise ValueError("a transform case must contain nine stages")
    for stage in stages:
        if not isinstance(stage, list) or len(stage) != 256:
            raise ValueError("a transform stage must contain 256 integers")
        if any(type(v) is not int or abs(v) > (1 << 54) for v in stage):
            raise ValueError("transform value exceeds the integer range guard")
    return stages


def emit_pairs(alpha, data_path, write, legacy_names=False):
    """Emit 255 pair modules; retain only one beta's six cases in memory."""
    _check_alpha(alpha)
    if legacy_names and alpha != 13:
        raise ValueError("legacy pair names belong to the alpha=13 pilot row")
    # Python 3.11 limits decimal conversion by default. These locally generated,
    # fixed-size packed vectors intentionally exceed that generic input limit.
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    template = Path(__file__).with_name("pair_template.lean.in").read_text(
        encoding="utf-8")
    slots = ["@@STAGE_%02d@@" % i for i in range(54)]
    if any(template.count(slot) != 1 for slot in slots):
        raise ValueError("pair template must contain exactly 54 stage slots")
    with Path(data_path).open("r", encoding="utf-8") as stream:
        for beta in range(1, 256):
            if legacy_names:
                name = "PaperSharpEntriesPairB%d" % beta
            else:
                name = "PaperSharpEntriesPairA%03dB%03d" % (alpha, beta)
            raw = (template.replace("@@NAME@@", name)
                   .replace("@@ALPHA@@", str(alpha))
                   .replace("@@BETA@@", str(beta)))
            index = 0
            for family, power in CASES:
                stages = _read_case(stream, alpha, beta, family, power)
                for stage in stages:
                    raw = raw.replace(slots[index], _packed(stage))
                    index += 1
            if index != 54 or "@@" in raw:
                raise ValueError("unfilled pair template slot")
            write(PREFIX + name + ".lean", raw.encode("utf-8"))
        if stream.read().strip():
            raise ValueError("unexpected data after the 1,530 transform cases")
    return 255


def _row_support(alpha):
    """Return the historical 18 ordinary-row aggregation modules verbatim."""
    row = "PaperSharpEntriesRowA%03d" % alpha
    interface = row + "Interface"
    sources = {}
    sources[PREFIX + interface + ".lean"] = (
        "import AES8.Estimates.Word.PaperSharpEntriesPairCoverage\n"
        "namespace AES8." + interface + "\n"
        "@[irreducible] def Cell (b : Fin 255) : Prop := "
        "AES8.PaperSharpEntriesPairCoverage.PairCells (" + str(alpha - 1) +
        " : Fin 255) b\nend AES8." + interface + "\n"
    ).encode("utf-8")
    for block in range(16):
        first = block * 16
        name = row + "Block%02d" % block
        raw = "".join(
            "import AES8.Estimates.Word.PaperSharpEntriesPairA%03dB%03d\n" %
            (alpha, n + 1) for n in range(first, min(first + 16, 255)))
        raw += ("import AES8.Estimates.Word.PaperSharpEntriesCoefficientCertificate\n"
                "import AES8.Estimates.Word." + interface + "\n")
        raw += ("namespace AES8." + name + "\nopen AES8." + interface +
                " AES8.PaperSharpEntriesCoefficientCertificate\n" + OPTIONS)
        raw += ("theorem cells (b : Fin 16) (hb : " + str(first) +
                "+b.val < 255) : Cell ⟨" + str(first) +
                "+b.val,hb⟩ := by\n  fin_cases b\n")
        for n in range(first, min(first + 16, 255)):
            cap = ("(AES8.PaperSharpEntriesPairA%03dB%03d.caps coefficient_spec)" %
                   (alpha, n + 1))
            raw += ("  · exact (show Cell (" + str(n) +
                    " : Fin 255) from by\n      unfold Cell\n      exact ⟨" +
                    cap + ".1, " + cap + ".2.1, " + cap + ".2.2⟩)\n")
        if block == 15:
            raw += "  · norm_num at hb\n"
        sources[PREFIX + name + ".lean"] = (
            raw + "end AES8." + name + "\n").encode("utf-8")
    raw = "".join("import AES8.Estimates.Word." + row + "Block%02d\n" % a
                  for a in range(16))
    raw += ("namespace AES8." + row +
            "\nopen AES8.PaperSharpEntriesPairCoverage AES8." + interface +
            "\n" + OPTIONS)
    raw += ("theorem row_cells : RowCells (" + str(alpha - 1) +
            " : Fin 255) := by\n  intro b\n"
            "  have blocks (a t : Fin 16) (hb : a.val*16+t.val < 255) :\n"
            "      Cell ⟨a.val*16+t.val,hb⟩ := by\n    fin_cases a\n")
    raw += "".join("    · exact AES8." + row + "Block%02d.cells t hb\n" % a
                   for a in range(16))
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
"""
    sources[PREFIX + row + ".lean"] = (
        raw + "end AES8." + row + "\n").encode("utf-8")
    return sources


def emit_row(alpha, data_path, write):
    """Emit the 273 modules for one of the 254 ordinary rows."""
    _check_alpha(alpha)
    if alpha == 13:
        raise ValueError("use legacy emit_pairs and the pilot row wrappers for alpha=13")
    count = emit_pairs(alpha, data_path, write)
    sources = _row_support(alpha)
    for path in sorted(sources):
        write(path, sources[path])
    return count + len(sources)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--alpha", required=True, type=int)
    parser.add_argument("--data", required=True, type=Path,
                        help="JSONL emitted by generate_transforms")
    parser.add_argument("--output", required=True, type=Path,
                        help="Lean project root receiving generated files")
    parser.add_argument("--legacy-pairs", action="store_true",
                        help="emit only the 255 alpha=13 pilot pair modules")
    args = parser.parse_args()

    def write(path, data):
        target = args.output / path
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            if target.read_bytes() != data:
                raise ValueError("refusing to overwrite differing source: " + path)
        else:
            target.write_bytes(data)

    if args.legacy_pairs:
        count = emit_pairs(args.alpha, args.data, write, legacy_names=True)
    else:
        count = emit_row(args.alpha, args.data, write)
    print("Wrote %d Lean modules for alpha=%d" % (count, args.alpha))


if __name__ == "__main__":
    main()
