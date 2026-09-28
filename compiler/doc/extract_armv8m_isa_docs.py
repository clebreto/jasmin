#!/usr/bin/env python3
"""Extract machine-readable ISA documentation for the Jasmin Armv8-M backend.

Parses the Armv8-M Architecture Reference Manual (DDI0553B.r) PDF and produces
a JSON file describing every base (non floating-point, non vector) instruction
of chapter C2.4 "Alphabetical list of instructions":

  - the section id, title and page range,
  - the descriptive summary paragraph(s),
  - for every encoding (T1, T2, ...): the architecture requirement stated by
    the manual ("Armv8-M Main Extension only", "Armv8.1-M ...", ...), the
    assembler syntax templates of each variant, and the "Decode" pseudocode
    (which carries the UNDEFINED / UNPREDICTABLE conditions),
  - the "Operation" pseudocode,
  - the "Data Independent Timing behavior" statement, when there is one,

plus the shared pseudocode functions of chapter E2 that the operations of the
instructions modeled by Jasmin depend on.

It then relates the mnemonics of the Jasmin model to these entries and prints
a coverage table: for each mnemonic, the entries, the extension requirements,
and whether the manual lists the instruction as data independent timing.

Usage:
    python3 extract_armv8m_isa_docs.py [--markdown] [PDF_PATH] [OUT_JSON]

With --markdown, the coverage table is printed as a Markdown table: the one of
docs/source/compiler/advanced/armv8m.md.

The JSON file holds excerpts of the manual: it is not tracked.

Defaults:
    PDF_PATH: DDI0553B_r_armv8m_arm.pdf at the root of the repository
    OUT_JSON: armv8m_isa_docs.json next to this script

Requires PyMuPDF (``pip install pymupdf``; imported as ``fitz``).

The extractor is deterministic: running it again on the same PDF reproduces
the same JSON. It relies on the PDF table of contents for the boundaries of
the entries and on font and position metadata to classify lines:

    NimbusSanL-Bold 11.4        section heading
    NimbusRomNo9L-Medi 12       part heading (T1, Decode ..., Operation ...)
    NimbusRomNo9L-Medi 10       variant heading, "Applies when", DIT items
    NimbusRomNo9L-ReguItal 10   architecture requirement of an encoding
    NimbusRomNo9L-Regu 10       body text
    NimbusMonL-* 10             assembler syntax
    NimbusMonL-* 8              pseudocode (line numbers are Regu 8)
    LiberationSans              encoding diagrams (ignored)

Indentation of the pseudocode is reconstructed from the horizontal position of
the glyphs (the advance of the 8 pt monospaced font is 4.782 pt).
"""

import hashlib
import json
import os
import re
import sys

import fitz  # PyMuPDF

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT_PDF = os.path.normpath(
    os.path.join(HERE, "..", "..", "DDI0553B_r_armv8m_arm.pdf"))
DEFAULT_OUT = os.path.join(HERE, "armv8m_isa_docs.json")
PDF_EDITION = "DDI0553B.r"

# ---------------------------------------------------------------------------
# Jasmin mnemonic -> titles of the C2.4 entries that describe it.
#
# The first block lists the mnemonics of the Armv7-M model
# (proofs/compiler/arm_instr_decl.v), all of which exist in Armv8-M. The
# flag-setting shifts (ASRS, LSLS, ...) have their own entries in this manual:
# they are the [set_flags] variants of the Jasmin mnemonics.
# ---------------------------------------------------------------------------
MNEMONIC_FORMS = {
    "ADD": ["ADD (immediate)", "ADD (register)", "ADD (SP plus immediate)",
            "ADD (SP plus register)"],
    "ADC": ["ADC (immediate)", "ADC (register)"],
    "MUL": ["MUL"],
    "MLA": ["MLA"],
    "MLS": ["MLS"],
    "SDIV": ["SDIV"],
    "SUB": ["SUB (immediate)", "SUB (register)", "SUB (SP minus immediate)",
            "SUB (SP minus register)"],
    "SBC": ["SBC (immediate)", "SBC (register)"],
    "RSB": ["RSB (immediate)", "RSB (register)"],
    "UDIV": ["UDIV"],
    "UMULL": ["UMULL"],
    "UMAAL": ["UMAAL"],
    "UMLAL": ["UMLAL"],
    "SMULL": ["SMULL"],
    "SMLAL": ["SMLAL"],
    "SMMUL": ["SMMUL, SMMULR"],
    "SMMULR": ["SMMUL, SMMULR"],
    "SMUL_hw": ["SMULBB, SMULBT, SMULTB, SMULTT"],
    "SMLA_hw": ["SMLABB, SMLABT, SMLATB, SMLATT"],
    "SMULW_hw": ["SMULWB, SMULWT"],
    "AND": ["AND (immediate)", "AND (register)"],
    "BFC": ["BFC"],
    "BFI": ["BFI"],
    "BIC": ["BIC (immediate)", "BIC (register)"],
    "EOR": ["EOR (immediate)", "EOR (register)"],
    "MVN": ["MVN (immediate)", "MVN (register)"],
    "ORR": ["ORR (immediate)", "ORR (register)"],
    "ASR": ["ASR (immediate)", "ASR (register)", "ASRS (immediate)",
            "ASRS (register)"],
    "LSL": ["LSL (immediate)", "LSL (register)", "LSLS (immediate)",
            "LSLS (register)"],
    "LSR": ["LSR (immediate)", "LSR (register)", "LSRS (immediate)",
            "LSRS (register)"],
    "ROR": ["ROR (immediate)", "ROR (register)", "RORS (immediate)",
            "RORS (register)"],
    "REV": ["REV"],
    "REV16": ["REV16"],
    "REVSH": ["REVSH"],
    "ADR": ["ADR"],
    "MOV": ["MOV (immediate)", "MOV (register)",
            "MOV, MOVS (register-shifted register)"],
    "MOVT": ["MOVT"],
    "UBFX": ["UBFX"],
    "UXTB": ["UXTB"],
    "UXTH": ["UXTH"],
    "SBFX": ["SBFX"],
    "SXTB": ["SXTB"],
    "SXTH": ["SXTH"],
    "CLZ": ["CLZ"],
    "CMP": ["CMP (immediate)", "CMP (register)"],
    "TST": ["TST (immediate)", "TST (register)"],
    "CMN": ["CMN (immediate)", "CMN (register)"],
    "LDR": ["LDR (immediate)", "LDR (register)", "LDR (literal)"],
    "LDRB": ["LDRB (immediate)", "LDRB (register)"],
    "LDRH": ["LDRH (immediate)", "LDRH (register)"],
    "LDRSB": ["LDRSB (immediate)", "LDRSB (register)"],
    "LDRSH": ["LDRSH (immediate)", "LDRSH (register)"],
    "STR": ["STR (immediate)", "STR (register)"],
    "STRB": ["STRB (immediate)", "STRB (register)"],
    "STRH": ["STRH (immediate)", "STRH (register)"],
    # Instructions emitted by the assembly printer, outside of the model.
    "B": ["B"],
    "BL": ["BL"],
    "BX": ["BX, BXNS"],
    "IT": ["IT"],
    "PUSH": ["PUSH (multiple registers)", "PUSH (single register)"],
    "POP": ["POP (multiple registers)", "POP (single register)"],
}

# Shared pseudocode functions to extract from chapter E2.
SHARED_HELPERS = [
    "AddWithCarry",
    "Shift", "Shift_C", "LSL", "LSL_C", "LSR", "LSR_C", "ASR", "ASR_C",
    "ROR", "ROR_C", "RRX", "RRX_C",
    "DecodeImmShift", "DecodeRegShift",
    "T32ExpandImm", "T32ExpandImm_C",
    "ConditionPassed", "ConditionHolds", "CurrentCond",
    "SignExtend", "ZeroExtend", "IsZero", "IsZeroBit",
    "CountLeadingZeroBits", "HighestSetBit", "BitCount", "Align",
    "SignedSatQ", "UnsignedSatQ", "SignedSat", "UnsignedSat",
    "R", "SP", "_SP", "RSPCheck", "LookUpSP", "LookUpSP_with_security_mode",
    "MemU", "MemA",
    "InITBlock", "LastInITBlock",
    "HaveMainExt", "HaveDSPExt", "HasArchVersion",
]

# ---------------------------------------------------------------------------
# Geometry and fonts.
# ---------------------------------------------------------------------------
Y_TOP = 95.0       # below the running header
Y_BOTTOM = 775.0   # above the running footer
CODE_X0 = 110.7    # left margin of the pseudocode
CODE_ADV = 4.782   # advance of the 8 pt monospaced font
SYNTAX_ADV = 5.978  # advance of the 10 pt monospaced font

LIGATURES = {"ﬁ": "fi", "ﬂ": "fl", "ﬀ": "ff", "ﬃ": "ffi",
             "ﬄ": "ffl", "’": "'", "‘": "'", "“": '"',
             "”": '"', "–": "-", "—": "-", "•": "*",
             " ": " "}


def clean(s):
    for k, v in LIGATURES.items():
        s = s.replace(k, v)
    return s


class Span:
    __slots__ = ("page", "x", "y", "x1", "font", "size", "text")

    def __init__(self, page, x, y, x1, font, size, text):
        self.page, self.x, self.y, self.x1 = page, x, y, x1
        self.font, self.size, self.text = font, size, text

    @property
    def mono(self):
        return self.font.startswith("NimbusMonL")

    @property
    def kind(self):
        f, s = self.font, self.size
        if f.startswith("LiberationSans"):
            return "diagram"
        if f.startswith("NimbusSanL-Bold") and s > 11:
            return "section"
        if f.startswith("NimbusMonL"):
            return "code" if s < 9 else "syntax"
        if f.startswith("NimbusRomNo9L-Medi"):
            return "part" if s > 11 else "sub"
        if f.startswith("NimbusRomNo9L-ReguItal"):
            return "ital"
        if f.startswith("NimbusRomNo9L-Regu"):
            if s < 9 and self.x < CODE_X0 - 2.0 and self.text.strip().isdigit():
                return "lineno"
            return "text"
        return "other"


def page_spans(doc, pno):
    """Spans of page [pno] (0-based), without header, footer and diagrams."""
    out = []
    for block in doc[pno].get_text("dict")["blocks"]:
        if block["type"] != 0:
            continue
        for line in block["lines"]:
            for sp in line["spans"]:
                text = clean(sp["text"])
                if not text.strip():
                    continue
                x0, y0, x1, _ = sp["bbox"]
                if y0 < Y_TOP or y0 > Y_BOTTOM:
                    continue
                # Re-anchor on the first non-blank glyph.
                lead = len(text) - len(text.lstrip(" "))
                if lead:
                    adv = (x1 - x0) / max(len(text), 1)
                    x0 += lead * adv
                    text = text.lstrip(" ")
                out.append(Span(pno + 1, x0, y0, x1, sp["font"], sp["size"],
                                text.rstrip()))
    return out


def group_rows(spans):
    """Group spans in rows (same page, same baseline), sorted."""
    spans = sorted(spans, key=lambda s: (s.page, s.y, s.x))
    rows = []
    for s in spans:
        if rows and rows[-1][0].page == s.page and abs(rows[-1][0].y - s.y) < 3.0:
            rows[-1].append(s)
        else:
            rows.append([s])
    for r in rows:
        r.sort(key=lambda s: s.x)
    return rows


def row_kind(row):
    kinds = [s.kind for s in row]
    for k in ("section", "part", "code", "syntax"):
        if k in kinds:
            return k
    for k in ("sub", "ital", "text"):
        if kinds[0] == k:
            return k
    return kinds[0]


def render_mono(row, x0, adv):
    """Render a row of monospaced spans, rebuilding the spacing."""
    line = ""
    for s in row:
        if not s.mono:
            continue
        col = int(round((s.x - x0) / adv))
        if col > len(line):
            line += " " * (col - len(line))
        elif line and not line.endswith(" ") and col >= len(line):
            pass
        elif line and col < len(line) and not line.endswith(" "):
            line += " "
        line += s.text
    return line.rstrip()


def render_text(row):
    parts = []
    last = None
    for s in row:
        if s.kind in ("lineno", "diagram"):
            continue
        if last is not None and s.x - last > 1.0:
            parts.append(" ")
        parts.append(s.text)
        last = s.x1
    return re.sub(r"\s+", " ", "".join(parts)).strip()


def paragraphs(rows):
    """Join rows of body text in paragraphs (split on vertical gaps)."""
    paras, cur, last = [], [], None
    for r in rows:
        t = render_text(r)
        if not t:
            continue
        y, page = r[0].y, r[0].page
        bullet = t.startswith("* ") or t.startswith("- ")
        if cur and (last is None or page != last[1] or y - last[0] > 15.0
                    or bullet):
            if not (page != last[1] and not bullet and not cur[-1].endswith(".")):
                paras.append(" ".join(cur))
                cur = []
        cur.append(t)
        last = (y, page)
    if cur:
        paras.append(" ".join(cur))
    return paras


ENC_RE = re.compile(r"^[TA]\d+$")
# A condition of an "Applies when" clause, or the continuation of one.
COND_RE = re.compile(r"^(!?\(?[A-Za-z_][A-Za-z0-9_:]*\s*(==|!=)|&&|\|\||[01x]+\b)")


def parse_entry(doc, title, sec_id, p_start, p_end, next_id):
    """Parse the C2.4 entry [sec_id title] lying in pages p_start..p_end
    (1-based, inclusive)."""
    spans = []
    for pno in range(p_start - 1, p_end):
        spans.extend(page_spans(doc, pno))
    rows = group_rows(spans)

    # Keep the rows between our section heading and the next one.
    begin, end = None, len(rows)
    for i, r in enumerate(rows):
        if row_kind(r) == "section":
            head = r[0].text.strip()
            if head == sec_id:
                begin = i + 1
            elif begin is not None and head.startswith("C2."):
                end = i
                break
    if begin is None:
        raise RuntimeError("heading of %s %s not found (pages %d-%d)"
                           % (sec_id, title, p_start, p_end))
    rows = rows[begin:end]

    entry = {
        "id": sec_id,
        "title": title,
        "page": p_start,
        "page_end": rows[-1][0].page if rows else p_start,
        "summary": "",
        "encodings": [],
        "operation_asl": "",
        "dit": None,
        "notes": [],
    }

    state = "summary"
    summary_rows, dit_rows, note_rows = [], [], []
    enc, variant = None, None
    op_lines, part_name = [], None

    def new_encoding(name):
        nonlocal enc, variant
        enc = {"name": name, "requires": "", "variants": [], "decode_asl": ""}
        variant = None
        entry["encodings"].append(enc)

    def new_variant(name):
        nonlocal variant
        variant = {"name": name, "applies_when": "", "syntax": [],
                   "equivalent_to": []}
        enc["variants"].append(variant)

    decode_lines = []

    def flush_decode():
        nonlocal decode_lines
        if enc is not None and decode_lines:
            enc["decode_asl"] = "\n".join(decode_lines)
        decode_lines = []

    equivalent = False
    applies = False
    for r in rows:
        k = row_kind(r)
        text = render_text(r)
        if any(sp.kind == "sub" and sp.text.startswith("Applies when")
               for sp in r):
            k = "sub"
        if applies:
            # Continuation of a wrapped condition.
            if k == "syntax" and COND_RE.match(text):
                variant["applies_when"] = \
                    (variant["applies_when"] + " " + text.strip(" .")).strip()
                continue
            applies = False
        if k == "part":
            flush_decode()
            part_name = text
            equivalent = False
            if ENC_RE.match(text):
                new_encoding(text)
                state = "encoding"
            elif text.startswith("Decode for"):
                state = "decode"
            elif text.startswith("Assembler symbols"):
                state = "symbols"
            elif text.startswith("Operation"):
                state = "operation"
            elif text.startswith("Restricted behavior"):
                state = "restricted"
            else:
                state = "other"
                note_rows.append(r)
            continue

        if state == "summary":
            if k in ("text", "ital", "sub"):
                summary_rows.append(r)
        elif state == "encoding":
            if k == "ital" and not enc["requires"] and not enc["variants"]:
                enc["requires"] = text
            elif k == "sub":
                if text.startswith("Applies when"):
                    if variant is None:
                        new_variant("")
                    variant["applies_when"] = text[len("Applies when"):].strip(" .")
                    applies = True
                elif text.startswith("is equivalent to"):
                    equivalent = True
                elif text.startswith("and is"):
                    if variant is not None:
                        variant["preferred"] = text
                    equivalent = False
                else:
                    new_variant(text)
                    equivalent = False
            elif k == "syntax":
                if variant is None:
                    continue
                line = render_mono(r, CODE_X0, SYNTAX_ADV)
                target = "equivalent_to" if equivalent else "syntax"
                if line.lstrip().startswith("//") and variant[target]:
                    variant[target][-1] += "  " + line.strip()
                else:
                    variant[target].append(line.strip())
        elif state == "decode":
            if k == "code":
                decode_lines.append(render_mono(r, CODE_X0, CODE_ADV))
        elif state == "operation":
            if k == "code":
                op_lines.append(render_mono(r, CODE_X0, CODE_ADV))
        elif state == "restricted":
            if k == "sub" and text.startswith("Data Independent Timing"):
                state = "dit"
                dit_rows.append(r)
            else:
                note_rows.append(r)
        elif state == "dit":
            if k == "sub" and not text.startswith("-") and \
                    not text.startswith("*") and dit_rows and \
                    r[0].x < 120.0 and not text.startswith("Data Independent"):
                state = "restricted"
                note_rows.append(r)
            else:
                dit_rows.append(r)
        elif state == "other":
            note_rows.append(r)
    flush_decode()

    entry["summary"] = "\n\n".join(paragraphs(summary_rows))
    entry["operation_asl"] = "\n".join(op_lines)
    for e in entry["encodings"]:
        for v in e["variants"]:
            if not v["equivalent_to"]:
                del v["equivalent_to"]
            if not v["applies_when"]:
                del v["applies_when"]
    if dit_rows:
        lines = [render_text(r) for r in dit_rows]
        lines = [l for l in lines if l]
        body = " ".join(lines[1:])
        entry["dit"] = {
            "title": lines[0],
            "text": "\n".join(lines[1:]),
            # Whether the statement also covers the flags.
            "flags": bool(re.search(r"values of the N, Z, C, V flags", body)),
        }
    notes = paragraphs(note_rows)
    if notes:
        entry["notes"] = notes
    else:
        del entry["notes"]
    return entry


def parse_helper(doc, name, sec_id, p_start, p_end):
    spans = []
    for pno in range(p_start - 1, p_end):
        spans.extend(page_spans(doc, pno))
    rows = group_rows(spans)
    begin, end = None, len(rows)
    for i, r in enumerate(rows):
        if row_kind(r) == "section":
            head = r[0].text.strip()
            if head == sec_id:
                begin = i + 1
            elif begin is not None:
                end = i
                break
    if begin is None:
        return None
    lines = [render_mono(r, CODE_X0, CODE_ADV) for r in rows[begin:end]
             if row_kind(r) == "code"]
    return {"id": sec_id, "page": rows[begin][0].page if begin < len(rows)
            else p_start, "asl": "\n".join(lines)}


def find_heading_page(doc, sec_id, guess, lo, hi):
    """Page (1-based) holding the heading [sec_id]; the table of contents of
    this PDF has a few wrong targets."""
    order = [guess] + [p for d in range(1, hi - lo + 1)
                       for p in (guess - d, guess + d)]
    for p in order:
        if p < lo or p > hi:
            continue
        for s in page_spans(doc, p - 1):
            if s.kind == "section" and s.text.strip() == sec_id:
                return p
    return None


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def is_vector_entry(title):
    """Floating-point and vector (MVE) instructions start with V."""
    return title.startswith("V") or title.startswith("FLDM") or \
        title.startswith("FSTM")


def extension(entries):
    """Extension that the entries need. The model relies on the 32-bit
    encodings, of the Main extension."""
    reqs = {enc["requires"] for e in entries for enc in e["encodings"]}
    return "DSP" if any("DSP" in r for r in reqs) else "Main"


def markdown(instructions, mnemonics):
    print("| Mnemonic | Entries of the manual | Extension | Data "
          "independent timing |")
    print("|---|---|---|---|")
    for mn, titles in mnemonics.items():
        entries = [instructions[t] for t in titles]
        ids = ", ".join("%s %s" % (e["id"], t)
                        for e, t in zip(entries, titles))
        with_dit = [t for e, t in zip(entries, titles) if e["dit"] is not None]
        if len(with_dit) == len(titles):
            dit = "yes"
        elif not with_dit:
            dit = "no"
        else:
            dit = "yes, except " + ", ".join(
                t for t in titles if t not in with_dit)
        print("| `%s` | %s | %s | %s |" % (mn, ids, extension(entries), dit))


def main(argv):
    md = "--markdown" in argv
    argv = [a for a in argv if a != "--markdown"]
    pdf = argv[1] if len(argv) > 1 else DEFAULT_PDF
    out = argv[2] if len(argv) > 2 else DEFAULT_OUT
    doc = fitz.open(pdf)
    toc = doc.get_toc()

    # ---- C2.4 entries ----------------------------------------------------
    c24 = []
    for i, (lvl, t, p) in enumerate(toc):
        m = re.match(r"^(C2\.4\.\d+)\s+(.*\S)\s*$", t)
        if m:
            c24.append((m.group(1), m.group(2), p))
    chapter_end = next(p for (lvl, t, p) in toc if t.startswith("D "))
    instructions = {}
    for j, (sec_id, title, p) in enumerate(c24):
        if is_vector_entry(title):
            continue
        p_next = c24[j + 1][2] if j + 1 < len(c24) else chapter_end
        next_id = c24[j + 1][0] if j + 1 < len(c24) else None
        entry = parse_entry(doc, title, sec_id, p, p_next, next_id)
        if title in instructions:
            raise RuntimeError("duplicate title " + title)
        instructions[title] = entry

    # ---- shared pseudocode -----------------------------------------------
    e2 = []
    for (lvl, t, p) in toc:
        m = re.match(r"^(E2\.1\.\d+)\s+(\S+)\s*$", t)
        if m:
            e2.append((m.group(1), m.group(2), p))
    e2_lo = min(p for (_, _, p) in e2 if p > 1900)
    e2_hi = next(p for (lvl, t, p) in toc if t.startswith("F "))
    helpers = {}
    by_name = {n: (s, p) for (s, n, p) in e2}
    for name in SHARED_HELPERS:
        if name not in by_name:
            raise RuntimeError("no pseudocode section for " + name)
        sec_id, guess = by_name[name]
        if not (e2_lo <= guess <= e2_hi):
            # Wrong target in the table of contents: use the neighbours.
            idx = [s for (s, _, _) in e2].index(sec_id)
            guess = e2[idx - 1][2]
        p = find_heading_page(doc, sec_id, guess, e2_lo, e2_hi)
        if p is None:
            raise RuntimeError("heading of %s %s not found" % (sec_id, name))
        h = parse_helper(doc, name, sec_id, p, min(p + 3, e2_hi))
        if h is None or not h["asl"]:
            raise RuntimeError("empty pseudocode for " + name)
        helpers[name] = h

    # ---- mnemonics of the Jasmin model -----------------------------------
    mnemonics = {}
    for mn, titles in MNEMONIC_FORMS.items():
        for t in titles:
            if t not in instructions:
                raise RuntimeError("%s: no entry titled %r" % (mn, t))
        mnemonics[mn] = titles

    result = {
        "pdf": {
            "file": os.path.basename(pdf),
            "edition": PDF_EDITION,
            "sha256": sha256(pdf),
        },
        "instructions": instructions,
        "mnemonics": mnemonics,
        "shared_pseudocode": helpers,
    }
    with open(out, "w") as f:
        json.dump(result, f, indent=2, ensure_ascii=False, sort_keys=False)
        f.write("\n")

    # ---- validation and report -------------------------------------------
    with open(out) as f:
        check = json.load(f)
    assert check == result

    problems = []
    for t, e in instructions.items():
        if not e["summary"]:
            problems.append("%s %s: no summary" % (e["id"], t))
        if not e["encodings"]:
            problems.append("%s %s: no encoding" % (e["id"], t))
        # The manual gives no requirement for the aliases: they have the
        # requirement of the instruction they stand for.
        alias = "This is an alias of" in e["summary"]
        for enc in e["encodings"]:
            if not enc["requires"] and not alias:
                problems.append("%s %s %s: no architecture requirement"
                                % (e["id"], t, enc["name"]))
            if not any(v["syntax"] for v in enc["variants"]):
                problems.append("%s %s %s: no syntax"
                                % (e["id"], t, enc["name"]))

    def requires(e):
        return sorted({enc["requires"] for enc in e["encodings"]})

    def dit(e):
        return "-" if e["dit"] is None else "DIT"

    if md:
        markdown(instructions, mnemonics)
        return 0

    print("%-10s %-44s %-9s %-13s %s" % ("mnemonic", "entry", "id", "timing",
                                          "requires"))
    for mn, titles in mnemonics.items():
        for t in titles:
            e = instructions[t]
            print("%-10s %-44s %-9s %-13s %s"
                  % (mn, t, e["id"], dit(e), "; ".join(requires(e))))
            if not e["operation_asl"] and "pseudo-instruction" not in e["summary"] \
                    and "alias" not in e["summary"]:
                problems.append("%s %s: no operation pseudocode" % (e["id"], t))

    print()
    print("%d entries, %d mnemonics, %d shared pseudocode functions"
          % (len(instructions), len(mnemonics), len(helpers)))
    n_dit = sum(1 for e in instructions.values() if e["dit"] is not None)
    print("%d entries carry a Data Independent Timing statement" % n_dit)
    if problems:
        print()
        print("Problems:")
        for p in problems:
            print("  " + p)
    print("wrote " + out)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
