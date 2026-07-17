#!/usr/bin/env python3
"""Extract machine-readable ISA documentation for the Jasmin AArch64 backend.

Parses the ARM Architecture Reference Manual (DDI0487 M.a, A-profile) PDF and
produces a JSON file describing, for every A64 base-instruction mnemonic used
by the Jasmin ARMv8-A (AArch64) backend:

  - the corresponding C6.2 "Alphabetical list of A64 base instructions"
    entry/entries (section id, title, page),
  - the descriptive summary paragraph(s),
  - the assembler syntax templates,
  - the "Operation" ASL pseudocode section,

plus a set of shared ASL helper functions extracted once from chapter J1
("A-profile Architecture Pseudocode").

Usage:
    python3 extract_armv8a_isa_docs.py [PDF_PATH] [OUT_JSON]

Defaults:
    PDF_PATH: /Users/clebreto/dev/splits/DDI0487_M.a.a_a-profile_architecture_reference_manual.pdf
    OUT_JSON: armv8a_isa_docs.json next to this script

Requires PyMuPDF (``pip install pymupdf``; imported as ``fitz``).

The extractor is deterministic: re-running it on the same PDF reproduces the
same JSON. It relies on the PDF table of contents for C6.2 entry boundaries
and on font/position metadata (Courier = code, Arial-Bold = headings,
Times = body text) to classify lines; indentation of pseudocode is
reconstructed from horizontal glyph positions (Courier advance = 0.6 em).

At the end the script asserts that every target Jasmin mnemonic has at least
one form entry, prints a coverage table, and validates the emitted JSON.
"""

import hashlib
import json
import os
import re
import sys

import fitz  # PyMuPDF

DEFAULT_PDF = "/Users/clebreto/dev/splits/DDI0487_M.a.a_a-profile_architecture_reference_manual.pdf"
PDF_EDITION = "DDI0487 M.a"

# ---------------------------------------------------------------------------
# Jasmin mnemonic -> ARM ARM C6.2 entry titles (exact TOC titles).
# ---------------------------------------------------------------------------
MNEMONIC_FORMS = {
    "ADD": ["ADD (immediate)", "ADD (shifted register)", "ADD (extended register)"],
    "ADDS": ["ADDS (immediate)", "ADDS (shifted register)"],
    "ADC": ["ADC"],
    "ADCS": ["ADCS"],
    "SUB": ["SUB (immediate)", "SUB (shifted register)", "SUB (extended register)"],
    "SUBS": ["SUBS (immediate)", "SUBS (shifted register)"],
    "SBC": ["SBC"],
    "SBCS": ["SBCS"],
    "MUL": ["MUL"],
    "MADD": ["MADD"],
    "MSUB": ["MSUB"],
    "NEG": ["NEG (shifted register)", "SUB (shifted register)"],
    "SDIV": ["SDIV"],
    "UDIV": ["UDIV"],
    "UMULL": ["UMULL"],
    "SMULL": ["SMULL"],
    "UMADDL": ["UMADDL"],
    "SMADDL": ["SMADDL"],
    "UMULH": ["UMULH"],
    "SMULH": ["SMULH"],
    "AND": ["AND (immediate)", "AND (shifted register)"],
    "ANDS": ["ANDS (immediate)", "ANDS (shifted register)"],
    "BIC": ["BIC (shifted register)"],
    "BICS": ["BICS (shifted register)"],
    "ORR": ["ORR (immediate)", "ORR (shifted register)"],
    "EOR": ["EOR (immediate)", "EOR (shifted register)"],
    "MVN": ["MVN"],
    "ASR": ["ASR (register)", "ASR (immediate)"],
    "ASRV": ["ASRV"],
    "LSL": ["LSL (register)", "LSL (immediate)"],
    "LSLV": ["LSLV"],
    "LSR": ["LSR (register)", "LSR (immediate)"],
    "LSRV": ["LSRV"],
    "ROR": ["ROR (immediate)", "ROR (register)"],
    "RORV": ["RORV"],
    "BFXIL": ["BFXIL", "BFM"],
    "SBFX": ["SBFX", "SBFM"],
    "UBFX": ["UBFX", "UBFM"],
    "BFC": ["BFC", "BFM"],
    "BFI": ["BFI", "BFM"],
    "EXTR": ["EXTR"],
    "MOV": ["MOV (register)", "MOV (to/from SP)"],
    "MOVN": ["MOVN"],
    "MOVZ": ["MOVZ"],
    "MOVK": ["MOVK"],
    "ADR": ["ADR"],
    "CMP": ["CMP (immediate)", "CMP (shifted register)"],
    "CMN": ["CMN (immediate)", "CMN (shifted register)"],
    "TST": ["TST (immediate)", "TST (shifted register)"],
    "LDR": ["LDR (immediate)", "LDR (register)"],
    "LDRB": ["LDRB (immediate)", "LDRB (register)"],
    "LDRH": ["LDRH (immediate)", "LDRH (register)"],
    "LDRSB": ["LDRSB (immediate)", "LDRSB (register)"],
    "LDRSH": ["LDRSH (immediate)", "LDRSH (register)"],
    "LDRSW": ["LDRSW (immediate)", "LDRSW (register)"],
    "STR": ["STR (immediate)", "STR (register)"],
    "STRB": ["STRB (immediate)", "STRB (register)"],
    "STRH": ["STRH (immediate)", "STRH (register)"],
    "SXTB": ["SXTB"],
    "SXTH": ["SXTH"],
    "SXTW": ["SXTW"],
    "UXTB": ["UXTB"],
    "UXTH": ["UXTH"],
    "UXTW": ["MOV (register)"],
    "RBIT": ["RBIT"],
    "REV": ["REV"],
    "REV16": ["REV16"],
    "REV32": ["REV32"],
    "CLZ": ["CLZ"],
    "CLS": ["CLS"],
    "CSEL": ["CSEL"],
    "CSINC": ["CSINC"],
    "CSINV": ["CSINV"],
    "CSNEG": ["CSNEG"],
    "CSET": ["CSET"],
    "CSETM": ["CSETM"],
}

# Notes attached to every form of the given Jasmin mnemonic.
MNEMONIC_NOTES = {
    "NEG": "NEG is an alias of SUB (shifted register) with Rn = ZR; the SUB "
           "entry carries the operational pseudocode.",
    "MUL": "MUL is an alias of MADD with Ra = ZR (see the MADD entry for the "
           "operational pseudocode).",
    "UMULL": "UMULL is an alias of UMADDL with Ra = XZR.",
    "SMULL": "SMULL is an alias of SMADDL with Ra = XZR.",
    "UXTW": "The ARM ARM defines no UXTW entry: UXTW #0 is equivalent to a "
            "32-bit register MOV (alias of ORR (shifted register)), whose "
            "32-bit result is zero-extended to 64 bits; the MOV (register) "
            "entry is recorded here in its place.",
}

# Shared ASL helper functions to extract from chapter J1.
SHARED_HELPERS = [
    "DecodeShift", "ShiftReg", "DecodeBitMasks", "ExtendReg",
    "DecodeRegExtend", "SignExtend", "ZeroExtend", "Zeros", "Ones",
    "ConditionHolds",
]

# ---------------------------------------------------------------------------
# Low-level text extraction helpers
# ---------------------------------------------------------------------------

FOOTER_RE = re.compile(r"^[A-Z]\d?\d?-\d+$")  # e.g. "C6-1796", "J1-15899"

HEADER_FOOTER_TEXTS = {
    "ARM DDI 0487", "M.a.a", "Non-Confidential",
    "A64 Base Instruction Descriptions",
    "C6.2 Alphabetical list of A64 base instructions",
    "A-profile Architecture Pseudocode",
}


def page_lines(page):
    """Return a list of merged, classified line dicts for a page.

    Fragments sharing (approximately) the same baseline y are merged left to
    right, so e.g. a mnemonic and its operand template, or a section number
    and its title, become a single logical line.
    """
    d = page.get_text("dict")
    frags = []
    for blk in d.get("blocks", []):
        for line in blk.get("lines", []):
            text = "".join(s["text"] for s in line.get("spans", []))
            if not text.strip():
                continue
            spans = [s for s in line["spans"] if s["text"].strip()]
            frags.append({
                "y": line["bbox"][1],
                "x0": line["bbox"][0],
                "text": text.strip(),
                "fonts": [(s["font"], s["size"]) for s in spans],
            })
    frags.sort(key=lambda f: (round(f["y"], 1), f["x0"]))
    merged = []
    for f in frags:
        if merged and abs(f["y"] - merged[-1]["y"]) <= 2.0:
            merged[-1]["text"] += " " + f["text"]
            merged[-1]["fonts"] += f["fonts"]
        else:
            merged.append(dict(f))
    out = []
    for m in merged:
        # Skip running headers and footers.
        if m["y"] < 40 or m["y"] > 755:
            continue
        t = m["text"]
        if t in HEADER_FOOTER_TEXTS or t.startswith("Copyright ©") or FOOTER_RE.match(t):
            continue
        fonts = m["fonts"]
        m["is_code"] = bool(fonts) and all(f.startswith("CourierNew") for f, _ in fonts)
        m["is_heading"] = any(f == "Arial-BoldMT" and s >= 8.2 for f, s in fonts)
        m["size"] = fonts[0][1] if fonts else 0.0
        m["page"] = page.number + 1  # 1-based PDF page number
        out.append(m)
    return out


def normalize_ws(s):
    return re.sub(r"[ \t]+", " ", s).strip()


def reconstruct_code(lines):
    """Rebuild indented pseudocode from Courier lines using x positions.

    Courier is monospaced with an advance width of 0.6 em, so the indentation
    in characters is (x0 - base_x0) / (0.6 * fontsize).
    """
    code_lines = [l for l in lines if l["is_code"]]
    if not code_lines:
        return "\n".join(normalize_ws(l["text"]) for l in lines)
    base_x0 = min(l["x0"] for l in code_lines)
    out = []
    for l in lines:
        if l["is_code"] and l["size"] > 0:
            n = int(round((l["x0"] - base_x0) / (0.6 * l["size"])))
            out.append(" " * max(0, n) + normalize_ws(l["text"]))
        else:
            out.append(normalize_ws(l["text"]))
    return "\n".join(out)


# ---------------------------------------------------------------------------
# C6.2 instruction entry extraction
# ---------------------------------------------------------------------------

TEMPLATE_RE = re.compile(r"^([A-Z][A-Z0-9]{0,9})\s+([<\[#].*)$")


def extract_entry(doc, sid, title, page_start, page_end):
    """Extract one C6.2 entry spanning PDF pages [page_start, page_end] (1-based)."""
    lines = []
    for pno in range(page_start - 1, page_end):
        lines.extend(page_lines(doc[pno]))

    # Locate the entry title heading ("C6.2.5 ADD (immediate)").
    start_idx = 0
    for i, l in enumerate(lines):
        if l["is_heading"] and l["text"].startswith(sid + " "):
            start_idx = i + 1
            break
    lines = lines[start_idx:]
    # Safety: cut at any *other* C6.2.N heading (entries normally start on a
    # fresh page, so this is a no-op in practice).
    for i, l in enumerate(lines):
        if l["is_heading"] and re.match(r"^C6\.2\.\d+ ", l["text"]):
            lines = lines[:i]
            break

    # --- summary: body-text lines up to the first heading or code line -----
    summary_parts = []
    prev = None
    for l in lines:
        if l["is_heading"] or l["is_code"]:
            break
        txt = normalize_ws(l["text"])
        new_para = (prev is None or l["page"] != prev["page"]
                    or (l["y"] - prev["y"]) > 14.0)
        if new_para or not summary_parts:
            summary_parts.append(txt)
        else:
            summary_parts[-1] += " " + txt
        prev = l
    summary = "\n\n".join(summary_parts)

    # --- syntax: assembler templates before the "Assembler Symbols" section -
    syn_end = len(lines)
    for i, l in enumerate(lines):
        if l["is_heading"] and l["text"].lower().startswith("assembler symbol"):
            syn_end = i
            break
    syntax = []
    pending_equiv = False
    for l in lines[:syn_end]:
        txt = normalize_ws(l["text"])
        if not l["is_code"]:
            if txt.startswith("is equivalent to"):
                pending_equiv = True
            continue
        m = TEMPLATE_RE.match(txt)
        if m:
            if pending_equiv and syntax:
                syntax[-1] += "  ==  " + txt
            else:
                syntax.append(txt)
            pending_equiv = False
    # Deduplicate while preserving order.
    seen = set()
    syntax = [s for s in syntax if not (s in seen or seen.add(s))]

    # --- Operation section --------------------------------------------------
    operation = None
    op_start = None
    for i, l in enumerate(lines):
        if l["is_heading"] and l["text"] == "Operation":
            op_start = i + 1
            break
    if op_start is not None:
        op_lines = []
        for l in lines[op_start:]:
            if l["is_heading"]:
                break
            op_lines.append(l)
        operation = reconstruct_code(op_lines)

    return {
        "c62_id": sid,
        "title": title,
        "page": page_start,
        "page_end": page_end,
        "summary": summary,
        "syntax": syntax,
        "operation_asl": operation,
    }


# ---------------------------------------------------------------------------
# Chapter J1 shared pseudocode extraction
# ---------------------------------------------------------------------------

def extract_shared_pseudocode(doc, toc):
    """Locate and extract the SHARED_HELPERS functions from chapter J1."""
    lvl1 = [(t, p) for lvl, t, p in toc if lvl == 1]
    j1_start = j1_end = None
    for i, (t, p) in enumerate(lvl1):
        if t.startswith("J1 "):
            j1_start = p
            j1_end = lvl1[i + 1][1] if i + 1 < len(lvl1) else doc.page_count
            break
    result = {}
    if j1_start is None:
        for name in SHARED_HELPERS:
            result[name] = "NOTE: chapter J1 not found in the PDF table of contents."
        return result

    banners = {name: "// %s()" % name for name in SHARED_HELPERS}
    hit_page = {}
    for pno in range(j1_start - 1, j1_end - 1):
        txt = doc[pno].get_text()
        for name, banner in banners.items():
            if name not in hit_page and banner in txt:
                hit_page[name] = pno

    for name in SHARED_HELPERS:
        if name not in hit_page:
            result[name] = ("NOTE: could not locate the '// %s()' definition "
                            "banner in chapter J1 of this PDF." % name)
            continue
        pno = hit_page[name]
        lines = []
        for p in range(pno, min(pno + 3, j1_end - 1)):
            lines.extend(page_lines(doc[p]))
        start = None
        for i, l in enumerate(lines):
            if l["is_code"] and normalize_ws(l["text"]) == banners[name]:
                start = i
                break
        if start is None:
            result[name] = ("NOTE: found the '// %s()' banner on page %d but "
                            "could not re-locate it during structured "
                            "extraction." % (name, pno + 1))
            continue
        body = []
        for l in lines[start:]:
            if l["is_heading"]:  # next J1.x.y.z section heading
                break
            body.append(l)
        result[name] = reconstruct_code(body)
    return result


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def sha256_of(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    pdf_path = sys.argv[1] if len(sys.argv) > 1 else DEFAULT_PDF
    out_path = (sys.argv[2] if len(sys.argv) > 2 else
                os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "armv8a_isa_docs.json"))

    doc = fitz.open(pdf_path)
    toc = doc.get_toc()

    # C6.2.x entry name -> (section id, start page, end page), all 1-based.
    c62 = [(t, p) for lvl, t, p in toc if lvl == 3 and re.match(r"^C6\.2\.\d+ ", t)]
    entry_ranges = {}
    for i, (t, p) in enumerate(c62):
        sid, name = t.split(" ", 1)
        end = c62[i + 1][1] - 1 if i + 1 < len(c62) else p
        entry_ranges[name] = (sid, p, max(p, end))
    print("C6.2 entries found in TOC: %d" % len(entry_ranges))

    # Extract each distinct form once.
    needed_titles = sorted({t for forms in MNEMONIC_FORMS.values() for t in forms})
    forms_cache = {}
    for title in needed_titles:
        if title not in entry_ranges:
            print("WARNING: no C6.2 TOC entry for %r" % title)
            continue
        sid, ps, pe = entry_ranges[title]
        forms_cache[title] = extract_entry(doc, sid, title, ps, pe)

    mnemonics = {}
    for mnem, titles in MNEMONIC_FORMS.items():
        entries = []
        for title in titles:
            if title not in forms_cache:
                continue
            e = dict(forms_cache[title])
            note = MNEMONIC_NOTES.get(mnem)
            if note:
                e["note"] = note
            entries.append(e)
        mnemonics[mnem] = entries

    shared = extract_shared_pseudocode(doc, toc)

    data = {
        "pdf": {
            "file": os.path.basename(pdf_path),
            "edition": PDF_EDITION,
            "sha256": sha256_of(pdf_path),
        },
        "mnemonics": mnemonics,
        "shared_pseudocode": shared,
    }

    os.makedirs(os.path.dirname(out_path), exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(data, f, indent=2, ensure_ascii=False)
        f.write("\n")

    # --- validation and coverage report -------------------------------------
    with open(out_path) as f:
        reparsed = json.load(f)
    assert set(reparsed["mnemonics"]) == set(MNEMONIC_FORMS)

    print("\nCoverage table (Jasmin mnemonic -> extracted forms):")
    total_forms = 0
    degraded = []
    for mnem in sorted(MNEMONIC_FORMS):
        entries = reparsed["mnemonics"][mnem]
        assert entries, "mnemonic %s has no form entries!" % mnem
        total_forms += len(entries)
        details = []
        for e in entries:
            flags = []
            if not e.get("summary"):
                flags.append("no-summary")
            if not e.get("syntax"):
                flags.append("no-syntax")
            if not e.get("operation_asl"):
                flags.append("no-operation")
            if flags:
                degraded.append("%s / %s: %s" % (mnem, e["title"], ",".join(flags)))
            details.append("%s %s%s" % (e["c62_id"], e["title"],
                                        " [" + ",".join(flags) + "]" if flags else ""))
        print("  %-8s -> %s" % (mnem, "; ".join(details)))

    helper_notes = [n for n, v in reparsed["shared_pseudocode"].items()
                    if v.startswith("NOTE:")]
    print("\nMnemonics covered: %d/%d" % (len(reparsed["mnemonics"]), len(MNEMONIC_FORMS)))
    print("Total form entries: %d (distinct C6.2 entries extracted: %d)"
          % (total_forms, len(forms_cache)))
    print("Shared pseudocode helpers: %d extracted, %d notes-only (%s)"
          % (len(reparsed["shared_pseudocode"]) - len(helper_notes),
             len(helper_notes), ", ".join(helper_notes) or "none"))
    if degraded:
        print("Degraded extractions:")
        for d in degraded:
            print("  " + d)
    else:
        print("Degraded extractions: none")
    print("\nWrote %s" % out_path)


if __name__ == "__main__":
    main()
