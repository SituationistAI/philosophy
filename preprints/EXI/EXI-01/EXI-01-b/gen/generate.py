#!/usr/bin/env python3
"""Generator for EXI-01-b, "Commentary on On the Meaning of Life", Volume I.

Reads the source files of the EXI manuscripts (content/preprints/EXI/*/*/main.tex
and their main.aux files) and writes the apparatus of Volume I:

  lemmacheck   verifies that every lemma quoted in the commentary chapters
               (\\lem{n}{...} in ../ch*.tex) and every entry of lemmata.py
               occurs verbatim in EXI-01-a, and that the numbers agree;
  text.tex     the text of EXI-01-a divided into numbered lemmata;
  index.tex    Appendix A.1: every word type of EXI-01-a, with its lemmata and
               its occurrences in each EXI manuscript;
  families.tex Appendix A.2: occurrences of fifteen term families, by manuscript;
  kwic.tex     Appendix A.3: keyword-in-context concordance of the content
               words of EXI-01-a in the other EXI manuscripts;
  xref.tex     Appendix B: every numbered statement of every EXI manuscript
               (from its .aux file), its concept classes and the lemmata of
               EXI-01-a it bears on by the rule stated below;
  xrefsum.tex  Appendix B summary tables;
  testimonia.tex Appendix C: every sentence of the EXI manuscripts that cites EXI-01;
  stats.tex    macros with the summary counts used in the prose.

Python 3 standard library only.  Deterministic output.
"""
import glob
import os
import re
import sys
from collections import Counter, OrderedDict, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
MSDIR = os.path.dirname(HERE)                      # .../EXI-01/EXI-01-b
EXI = os.path.dirname(os.path.dirname(MSDIR))       # .../preprints/EXI
SELF = "EXI-01-b"
PRINCIPAL = "EXI-01-a"

sys.path.insert(0, HERE)
from lemmata import LEMMATA, STATEMENTS  # noqa: E402

# ---------------------------------------------------------------- utilities

def esc(s):
    """Escape plain text for LaTeX."""
    rep = {"\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
           "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
           "^": r"\textasciicircum{}"}
    return "".join(rep.get(c, c) for c in s)


def mskey(ms):
    fam, sub = ms[:6], ms[7:]
    return (int(fam[4:]), sub)


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def strip_comments(src):
    return re.sub(r"(?<!\\)%.*", "", src)


def body_of(src):
    src = strip_comments(src)
    m = re.search(r"\\begin\{document\}(.*?)\\end\{document\}", src, re.S)
    b = m.group(1) if m else src
    b = re.sub(r"\\begin\{thebibliography\}.*?\\end\{thebibliography\}", " ", b, flags=re.S)
    b = re.sub(r"\\begin\{lstlisting\}.*?\\end\{lstlisting\}", " ", b, flags=re.S)
    return b


CITE_RE = re.compile(r"\\cite(?:t|p|alp|author|year)?\*?(?:\[[^\]]*\])*\{[^}]*\}")


def bibnames(src):
    """Map citation keys to (author, year) from the \\bibitem[Author(Year)]{key} lines."""
    out = {}
    for a, y, k in re.findall(r"\\bibitem\[([^\]]*?)\((\d{4}[a-z]?)\)\]\{([^}]*)\}", src):
        out[k] = (a.replace("\\&", "and").replace("{", "").replace("}", "").strip(), y)
    return out


def cite_text(m, names):
    cmd, keys = m.group(1), m.group(2)
    parts = []
    for k in [x.strip() for x in keys.split(",")]:
        a, y = names.get(k, (k, ""))
        parts.append((a, y))
    if cmd == "t":
        return "; ".join(f"{a} ({y})" for a, y in parts)
    if cmd == "author":
        return "; ".join(a for a, _ in parts)
    return "(" + "; ".join(f"{a} {y}" for a, y in parts) + ")"


def detex(s, keep_cites=False, refs=None, names=None):
    """Plain text of a TeX fragment: commands removed, arguments of text
    commands kept, math removed.  If refs (label -> number) and names
    (citation key -> author, year) are given, cross-references and citations
    are resolved; otherwise they are removed."""
    if refs is not None:
        s = re.sub(r"\\ref\{([^}]*)\}", lambda m: refs.get(m.group(1), "?"), s)
    if names is not None:
        s = re.sub(r"\\cite(t|p|alp|author)?\*?(?:\[[^\]]*\])*\{([^}]*)\}",
                   lambda m: cite_text(m, names), s)
    if not keep_cites:
        s = CITE_RE.sub(" ", s)
    s = re.sub(r"\$[^$]*\$", " ", s)
    s = re.sub(r"\\(label|ref|eqref|input|vspace|hspace|usepackage|bibitem)\*?(\[[^\]]*\])?\{[^}]*\}", " ", s)
    s = re.sub(r"\\(begin|end)\{[^}]*\}(\[[^\]]*\])?", " ", s)
    s = re.sub(r"\\(section|subsection|paragraph)\*?(\[[^\]]*\])?\{([^}]*)\}", r" \3. ", s)
    s = re.sub(r"\\S\b", " ", s)
    s = s.replace("~", " ").replace("\\\\", " ")
    s = re.sub(r"\\[a-zA-Z]+\*?", " ", s)
    s = re.sub(r"[{}]", "", s)
    s = s.replace("``", '"').replace("''", '"').replace("---", " - ").replace("--", "-")
    s = re.sub(r"\s+", " ", s)
    return s.strip()


def norm_quote(s):
    """Normalization used to compare lemma quotations with the source."""
    s = re.sub(r"\\citep\{([^}]*)\}", r"[cite:\1]", s)
    s = re.sub(r"\\emph\{([^{}]*(\$[^$]*\$)?[^{}]*)\}", r"\1", s)
    s = s.replace("$", "").replace("~", " ")
    s = re.sub(r"\\hfill.*", "", s)
    s = re.sub(r"\s+", " ", s)
    return s.strip()


WORD_RE = re.compile(r"[A-Z]{3}-\d{2}(?:-[a-z])?\b|[A-Za-z]+(?:['\u2019][A-Za-z]+)*(?:-[A-Za-z]+)*")


def lower(w):
    return w if re.match(r"[A-Z]{3}-\d", w) else w.lower()


def words(text):
    return [lower(w) for w in WORD_RE.findall(text)]


STOP = set("""a an the of to in on at by for with from and or nor not no is are be
been being was were it its it's this that these those which what whether who whom
whose there their them they she her he his him we our us one as if than then so
such any every some all each does do did has have had can could would should may
might must will shall into about only also but either neither""".split())

# Words of EXI-01-a that name its own statements or the commentary; they are
# indexed in A.1 but have no lines in the concordance A.3.
STRUCTURAL = {"definition", "assumption", "theorem", "commentary", "EXI-01-b"}

# ---------------------------------------------------------------- the corpus

def manuscripts():
    out = OrderedDict()
    for path in sorted(glob.glob(os.path.join(EXI, "EXI-*", "EXI-*-?", "main.tex")),
                       key=lambda p: mskey(os.path.basename(os.path.dirname(p)))):
        ms = os.path.basename(os.path.dirname(path))
        if ms == SELF:
            continue
        out[ms] = path
    return out


def sections(src):
    """Split a body into (section number, text) chunks; section 0 is the
    material before the first numbered section (abstract and front)."""
    b = body_of(src)
    b = re.sub(r"\\begin\{abstract\}", r"\\section*{Abstract}", b)
    parts = re.split(r"(\\section\*?\{[^}]*\}|\\appendix)", b)
    out, num, appendix, star = [], 0, False, False
    current = "0"
    buf = parts[0]
    out.append((current, buf))
    i = 1
    while i < len(parts):
        tok = parts[i]
        if tok == "\\appendix":
            appendix, num = True, 0
        elif tok.startswith("\\section*"):
            current = "Abs" if "Abstract" in tok else current
        else:
            num += 1
            current = chr(64 + num) if appendix else str(num)
        nxt = parts[i + 1] if i + 1 < len(parts) else ""
        out.append((current, nxt))
        i += 2
    return out


SENT_RE = re.compile(r"(?<=[.!?])\s+(?=[A-Z(])")


def sentences(text):
    return [s for s in SENT_RE.split(text) if s.strip()]


# ---------------------------------------------------------------- lemmata

def principal_text():
    src = strip_comments(read(os.path.join(EXI, "EXI-01", PRINCIPAL, "main.tex")))
    m = re.search(r"\\maketitle(.*?)\\begin\{thebibliography\}", src, re.S)
    body = m.group(1)
    title = re.search(r"\\title\{([^}]*)\}", src).group(1)
    return title, body


def check_lemmata():
    title, body = principal_text()
    nb = norm_quote(body)
    lem = OrderedDict(LEMMATA)
    problems = []
    for n, q in LEMMATA:
        qq = norm_quote(q)
        if n == "1":
            if qq != title:
                problems.append(f"lemma 1 does not match the title: {qq!r}")
        elif qq not in nb:
            problems.append(f"lemma {n} not found in {PRINCIPAL}: {qq!r}")
        if "." in n:
            parent = n.split(".")[0]
            if norm_quote(q).rstrip(".") not in norm_quote(lem[parent]):
                problems.append(f"phrase lemma {n} not inside sentence lemma {parent}")
    # sentence lemmata in order and exhaustive of the sentences of the text
    sent = [n for n, _ in LEMMATA if "." not in n and n != "1"]
    pos = [nb.find(norm_quote(lem[n])) for n in sent]
    if pos != sorted(pos):
        problems.append("sentence lemmata out of order")
    # quotations in the commentary chapters
    used = Counter()
    for ch in sorted(glob.glob(os.path.join(MSDIR, "ch*.tex"))):
        txt = read(ch)
        for n, q in re.findall(r"\\lem\{([0-9.]+)\}\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}", txt):
            used[n] += 1
            if n not in lem:
                problems.append(f"{os.path.basename(ch)}: unknown lemma number {n}")
            elif norm_quote(q) != norm_quote(lem[n]):
                problems.append(f"{os.path.basename(ch)}: lemma {n} misquoted: {q!r}")
    missing = [n for n in lem if used[n] == 0]
    # every Lean listing in the chapter on the module must occur in the module
    lean = read(os.path.join(os.path.dirname(os.path.dirname(EXI)), "lean", "Philosophy", "EXI", "EXI_01.lean"))
    nlean = re.sub(r"\s+", " ", lean)
    for ch in sorted(glob.glob(os.path.join(MSDIR, "ch*.tex"))):
        for blk in re.findall(r"\\begin\{lstlisting\}\n(.*?)\\end\{lstlisting\}", read(ch), re.S):
            if "depends on axioms" in blk:
                continue                      # checker output, not module text
            if re.sub(r"\s+", " ", blk).strip() not in nlean:
                problems.append(f"{os.path.basename(ch)}: Lean listing not in module: {blk[:60]!r}")
    return problems, used, missing


def write_text():
    """The text of EXI-01-a divided into numbered lemmata."""
    lem = OrderedDict(LEMMATA)
    L = [r"\begin{longtable}{@{}p{0.13\textwidth}p{0.07\textwidth}p{0.74\textwidth}@{}}",
         r"\toprule Statement & Lemma & Text \\ \midrule \endhead",
         r"\bottomrule \endfoot"]
    for name, nums in STATEMENTS:
        first = True
        for n in nums:
            L.append(f"{name if first else ''} & [{n}] & {lem[n]} \\\\[2pt]")
            first = False
    L.append(r"\end{longtable}")
    return "\n".join(L)


# ---------------------------------------------------------------- concordance

def principal_words():
    """Word tokens of EXI-01-a by sentence lemma (citations removed)."""
    occ = OrderedDict()
    for n, q in LEMMATA:
        if "." in n:
            continue
        for w in words(detex(q)):
            occ.setdefault(w, []).append(n)
    return occ


FAMILIES = [
    ("mean", r"mean(?:ing|ingful|ingfully|ingfulness|ingless|ingly|ings|s)?"),
    ("life", r"life|lives|lived|living"),
    ("engag", r"engag\w*"),
    ("activ", r"active|actively|activity|activities"),
    ("project", r"projects?"),
    ("worth", r"worth(?:while|y|iness)?"),
    ("objectiv", r"objective(?:ly|ity)?"),
    ("valu", r"valu\w*"),
    ("attitud", r"attitudes?"),
    ("agent", r"agents?|agency"),
    ("availab", r"availab\w*"),
    ("degree", r"degrees?|extent"),
    ("matter", r"matters?|mattered|mattering"),
    ("absurd", r"absurd\w*"),
    ("sceptic", r"s[ck]eptic\w*"),
]


def corpus():
    """For every manuscript: list of (section, sentence, words)."""
    out = OrderedDict()
    for ms, path in manuscripts().items():
        src = read(path)
        rows = []
        if ms == PRINCIPAL:
            _, body = principal_text()
            for n, q in LEMMATA:
                if "." not in n and n != "1":
                    t = detex(q)
                    rows.append(("[" + n + "]", t, words(t)))
        else:
            refs = {l[0]: l[1] for l in aux_labels(os.path.join(os.path.dirname(path), "main.aux"))}
            names = bibnames(src)
            for sec, chunk in sections(src):
                t = detex(chunk, refs=refs, names=names)
                for s in sentences(t):
                    rows.append((sec, s, words(s)))
        out[ms] = rows
    return out


def compact_counts(c, order):
    return "; ".join(f"{ms[4:]}\\,({c[ms]})" for ms in order if c.get(ms))


def write_index(corp, pw):
    order = list(corp.keys())
    others = [m for m in order if m != PRINCIPAL]
    count = {w: Counter() for w in pw}
    for ms, rows in corp.items():
        for _, _, ws in rows:
            for w in ws:
                if w in count:
                    count[w][ms] += 1
    L = [r"\begin{longtable}{@{}>{\raggedright}p{0.13\textwidth}>{\raggedright}p{0.1\textwidth}r r>{\raggedright\arraybackslash}p{0.55\textwidth}@{}}",
         r"\toprule Word & Lemmata & Occ. & Mss & Occurrences in the other EXI manuscripts \\ \midrule \endhead",
         r"\bottomrule \endfoot"]
    stats = {"types": 0, "content": 0, "hapax": []}
    for w in sorted(pw):
        lemref = ", ".join(f"{n}" + (f"\\,(\\(\\times\\){k})" if k > 1 else "")
                           for n, k in Counter(pw[w]).items())
        c = count[w]
        tot = sum(c[m] for m in others)
        nms = sum(1 for m in others if c[m])
        stats["types"] += 1
        if w in STOP:
            dist = r"\emph{function word: totals only}"
        else:
            stats["content"] += 1
            dist = compact_counts(c, others) or "---"
            if tot == 0:
                stats["hapax"].append(w)
        L.append(f"\\textbf{{{esc(w)}}} & {lemref} & {tot} & {nms} & {dist} \\\\")
    L.append(r"\end{longtable}")
    return "\n".join(L), stats, count


def write_families(corp):
    """Two tables (families 1-8 and 9-15) of term-family counts by manuscript."""
    order = list(corp.keys())
    cols = [f for f, _ in FAMILIES]
    regs = {f: re.compile(r"^(?:" + r + r")$") for f, r in FAMILIES}
    table = {ms: Counter() for ms in order}
    nwords = {}
    for ms, rows in corp.items():
        n = 0
        for _, _, ws in rows:
            n += len(ws)
            for w in ws:
                for f in cols:
                    if regs[f].match(w):
                        table[ms][f] += 1
        nwords[ms] = n
    tot = Counter()
    for ms in order:
        if ms != PRINCIPAL:
            tot.update(table[ms])
    out = []
    for part in (cols[:8], cols[8:]):
        head = " & ".join(r"\textit{" + f + "-}" for f in part)
        L = [r"\begin{longtable}{@{}l r" + " r" * len(part) + r"@{}}",
             r"\toprule Ms & Words & " + head + r" \\ \midrule \endhead",
             r"\bottomrule \endfoot"]
        for ms in order:
            cells = " & ".join(str(table[ms][f]) if table[ms][f] else "." for f in part)
            L.append(f"{ms} & {nwords[ms]} & {cells} \\\\")
        L.append(r"\midrule")
        L.append("Others & " + str(sum(v for m, v in nwords.items() if m != PRINCIPAL)) + " & " +
                 " & ".join(str(tot[f]) for f in part) + r" \\")
        L.append(r"\end{longtable}")
        out.append("\n".join(L))
    return out, table, nwords, tot


def write_kwic(corp, pw, width=40):
    content = sorted(w for w in pw if w not in STOP and w not in STRUCTURAL)
    entries = defaultdict(list)
    for ms, rows in corp.items():
        if ms == PRINCIPAL:
            continue
        for sec, s, _ in rows:
            for m in WORD_RE.finditer(s):
                w = lower(m.group(0))
                if w in pw and w not in STOP and w not in STRUCTURAL:
                    left = s[:m.start()]
                    right = s[m.end():]
                    left = ("..." + left[-width:]) if len(left) > width else left
                    right = (right[:width] + "...") if len(right) > width else right
                    entries[w].append((ms, sec, left, m.group(0), right))
    L = []
    total = 0
    for w in content:
        es = entries.get(w, [])
        total += len(es)
        L.append(r"\kwichead{" + esc(w) + "}{" + str(len(es)) + "}")
        if not es:
            L.append(r"\kwicnone")
            continue
        L.append(r"\begin{longtable}{@{}>{\raggedright}p{0.07\textwidth}>{\raggedleft}p{0.41\textwidth}@{\,}>{\raggedright\arraybackslash}p{0.47\textwidth}@{}}")
        for ms, sec, left, key, right in es:
            L.append(f"{ms[4:]} {esc(sec)} & {esc(left)} & \\textbf{{{esc(key)}}}{esc(right)} \\\\")
        L.append(r"\end{longtable}")
    return "\n".join(L), total, {w: len(entries.get(w, [])) for w in content}


# ---------------------------------------------------------------- cross-references

KINDS = ["definition", "principle", "assumption", "lemma", "theorem", "corollary",
         "proposition", "remark", "objection"]
ENV_RE = re.compile(r"\\begin\{(" + "|".join(KINDS) + r")\}(\[[^\]]*\])?(.*?)\\end\{\1\}", re.S)

CLASSES = OrderedDict([
    ("M", ("meaning", r"\bmeaning(?:ful|less)?\b|\bmeanings\b|\bpoint\b|\bsignifican")),
    ("E", ("engagement", r"\bengag|\babsor|\bcare(?:s|d)?\b|\bcaring\b|\bgripped")),
    ("W", ("worth", r"\bworth|\bvalu|\bgood(?:s)?\b|\bbetter\b|\bbad\b")),
    ("O", ("objectivity", r"\bobjectiv|\bindependen|\bnot depend|\battitude|\bsubjectiv|\bwhether or not")),
    ("P", ("projects", r"\bprojects?\b|\bpursuits?\b|\bactivit|\bends\b|\bfinal end|\bundertak")),
    ("A", ("availability", r"\bavailab|\beveryone\b|\bevery agent|\bany agent|\buniversal|\bluck\b|\bcircumstanc|\bany reflective agent")),
    ("I", ("agency", r"\bagents?\b|\bintentional action")),
    ("D", ("degree", r"\bdegree|\bextent\b|\bmore meaningful|\bless meaningful|\badd(?:s)? to\b")),
    ("S", ("absurd", r"\babsurd|\bdetached|\bsub specie|\bnothing matters|\bcosmic|\buniverse\b|\bindifferen|\bdespair")),
    ("L", ("life", r"\blife\b|\blives\b")),
])

# Lemma groups of EXI-01-a and the rule by which a statement bears on them.
RULES = OrderedDict([
    ("[1]", ("title", lambda c: "M" in c and "L" in c)),
    ("[2]", ("Def. 1", lambda c: "M" in c and len(c & {"E", "W", "P"}) >= 1 and len(c & {"E", "W", "P", "D"}) >= 2)),
    ("[2.3]", ("degree", lambda c: "D" in c and ("M" in c or "W" in c))),
    ("[3]", ("Ass. 2", lambda c: "O" in c and ("W" in c or "P" in c))),
    ("[4]", ("Ass. 3", lambda c: ("I" in c or "A" in c) and len(c & {"E", "P"}) >= 1 and ("W" in c or "M" in c))),
    ("[5]", ("Thm. 4", lambda c: "A" in c and ("M" in c or "W" in c))),
    ("[10]", ("particular lives", lambda c: "M" in c and "L" in c and "A" not in c and "S" not in c and "E" in c)),
    ("[11]", ("absurd", lambda c: "S" in c)),
])


def statement_texts(path):
    src = body_of(read(path))
    out = {}
    for m in ENV_RE.finditer(src):
        kind, opt, inner = m.group(1), m.group(2), m.group(3)
        lab = re.search(r"\\label\{([^}]*)\}", inner)
        if not lab:
            continue
        out[lab.group(1)] = (kind, detex(inner))
    return out


def aux_labels(path):
    out = []
    if not os.path.exists(path):
        return out
    for line in read(path).splitlines():
        m = re.match(r"\\newlabel\{([^}]*)\}\{\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}\{([^}]*)\}", line)
        if m:
            out.append((m.group(1), m.group(2), m.group(3), m.group(4), m.group(5)))
    return out


def classes_of(text):
    t = text.lower()
    return set(k for k, (_, r) in CLASSES.items() if re.search(r, t))


def write_xref():
    rows = []
    seen = set()
    for ms, path in manuscripts().items():
        if ms == PRINCIPAL:
            continue
        texts = statement_texts(path)
        for lab, num, page, title, anchor in aux_labels(os.path.join(os.path.dirname(path), "main.aux")):
            if lab not in texts or (ms, lab) in seen:
                continue
            seen.add((ms, lab))
            kind, text = texts[lab]
            c = classes_of(text + " " + title)
            bears = [g for g, (_, f) in RULES.items() if f(c)]
            rows.append((ms, num, kind, title, page, c, bears, text))
    L = [r"\begin{longtable}{@{}l l l >{\raggedright}p{0.25\textwidth} r l >{\raggedright\arraybackslash}p{0.2\textwidth}@{}}",
         r"\toprule Ms & No. & Kind & Title & p. & Classes & Bears on \\ \midrule \endhead",
         r"\bottomrule \endfoot"]
    abbrev = {"definition": "Def.", "principle": "Pr.", "assumption": "Ass.", "lemma": "Lem.",
              "theorem": "Thm.", "corollary": "Cor.", "proposition": "Prop.", "remark": "Rem.",
              "objection": "Obj."}
    prev = None
    for ms, num, kind, title, page, c, bears, text in rows:
        cl = "".join(k for k in CLASSES if k in c)
        tt = esc(title) if title else r"\emph{" + esc(" ".join(text.split()[:7])) + r"\ldots}"
        msc = ms if ms != prev else ""
        prev = ms
        L.append(f"{msc} & {num} & {abbrev[kind]} & {tt} & {page} & \\texttt{{{cl}}} & {', '.join(bears) if bears else '---'} \\\\")
    L.append(r"\end{longtable}")
    return "\n".join(L), rows


def write_xrefsum(rows):
    by_lemma = Counter()
    by_ms = defaultdict(Counter)
    kinds = Counter()
    for ms, num, kind, title, page, c, bears, text in rows:
        kinds[kind] += 1
        for b in bears:
            by_lemma[b] += 1
            by_ms[ms][b] += 1
    L = [r"\begin{tabular}{@{}l l r@{}}", r"\toprule Lemma group & Content & Statements \\ \midrule"]
    for g, (name, _) in RULES.items():
        L.append(f"{{{g}}} & {name} & {by_lemma[g]} \\\\")
    L.append(r"\bottomrule \end{tabular}")
    t1 = "\n".join(L)
    groups = list(RULES.keys())
    L = [r"\begin{longtable}{@{}l r" + " r" * len(groups) + r"@{}}",
         r"\toprule Ms & Stmts & " + " & ".join(groups) + r" \\ \midrule \endhead",
         r"\bottomrule \endfoot"]
    nst = Counter(r[0] for r in rows)
    for ms in sorted(nst, key=mskey):
        L.append(f"{ms} & {nst[ms]} & " + " & ".join(str(by_ms[ms][g]) if by_ms[ms][g] else "." for g in groups) + r" \\")
    L.append(r"\end{longtable}")
    t2 = "\n".join(L)
    L = [r"\begin{tabular}{@{}l l >{\raggedright\arraybackslash}p{0.68\textwidth}@{}}",
         r"\toprule Code & Class & Expressions (case-insensitive; matched from the start of a word; \textsuperscript{w}: whole word only) \\ \midrule"]
    for k, (name, rx) in CLASSES.items():
        alts = rx.replace("(?:", "(").split("|")
        # re-join alternatives that were split inside a parenthesized group
        items, buf = [], ""
        for a in alts:
            buf = a if not buf else buf + "|" + a
            if buf.count("(") == buf.count(")"):
                items.append(buf)
                buf = ""
        shown = ", ".join(r"\texttt{" + esc(i.replace(r"\b", "")) + ("}" if not i.endswith(r"\b") else r"}\textsuperscript{w}")
                          for i in items)
        L.append(f"\\texttt{{{k}}} & {name} & {shown} \\\\")
    L.append(r"\bottomrule \end{tabular}")
    t3 = "\n".join(L)
    return t1, t2, t3, by_lemma, kinds


# ---------------------------------------------------------------- testimonia

def write_testimonia(corp):
    L = [r"\begin{longtable}{@{}l l >{\raggedright\arraybackslash}p{0.78\textwidth}@{}}",
         r"\toprule Ms & \S & Sentence \\ \midrule \endhead", r"\bottomrule \endfoot"]
    n, mss = 0, set()
    for ms, path in manuscripts().items():
        if ms.startswith("EXI-01"):
            continue
        src = read(path)
        refs = {l[0]: l[1] for l in aux_labels(os.path.join(os.path.dirname(path), "main.aux"))}
        names = bibnames(src)
        for sec, chunk in sections(src):
            t = detex(chunk, refs=refs, names=names)
            for s in sentences(t):
                if re.search(r"EXI-01\b", s):
                    n += 1
                    mss.add(ms)
                    L.append(f"{ms} & {esc(sec)} & {esc(s)} \\\\[2pt]")
    L.append(r"\end{longtable}")
    return "\n".join(L), n, len(mss)


# ---------------------------------------------------------------- main

def main():
    problems, used, missing = check_lemmata()
    with open(os.path.join(HERE, "lemmacheck.txt"), "w") as f:
        f.write(f"lemmata in lemmata.py: {len(LEMMATA)}\n")
        f.write(f"quotations in chapters: {sum(used.values())}\n")
        f.write("lemmata not quoted in chapters: " + (", ".join(missing) or "none") + "\n")
        for p in problems:
            f.write("PROBLEM: " + p + "\n")
    if problems:
        print("\n".join(problems))
        sys.exit(1)

    out = {}
    out["text.tex"] = write_text()
    corp = corpus()
    pw = principal_words()
    out["index.tex"], istats, _ = write_index(corp, pw)
    (out["families.tex"], out["families2.tex"]), ftab, nwords, ftot = write_families(corp)
    out["kwic.tex"], nkwic, kcount = write_kwic(corp, pw)
    out["xref.tex"], rows = write_xref()
    t1, t2, t3, by_lemma, kinds = write_xrefsum(rows)
    out["xrefsum.tex"], out["xrefms.tex"], out["xrefclasses.tex"] = t1, t2, t3
    out["testimonia.tex"], ntest, ntestms = write_testimonia(corp)

    nms = len(corp)
    tokens = sum(len(ws) for _, _, ws in corp[PRINCIPAL])
    others_words = sum(v for m, v in nwords.items() if m != PRINCIPAL)
    top = sorted(((v, k) for k, v in kcount.items()), reverse=True)[:5]
    macros = {
        "cnLemmata": len(LEMMATA),
        "cnSentLemmata": sum(1 for n, _ in LEMMATA if "." not in n),
        "cnPhraseLemmata": sum(1 for n, _ in LEMMATA if "." in n),
        "cnMss": nms,
        "cnOtherMss": nms - 1,
        "cnTokens": tokens,
        "cnTypes": istats["types"],
        "cnContent": istats["content"],
        "cnCorpusWords": others_words,
        "cnKwic": nkwic,
        "cnStatements": len(rows),
        "cnBearing": sum(1 for r in rows if r[6]),
        "cnNotBearing": sum(1 for r in rows if not r[6]),
        "cnTestimonia": ntest,
        "cnTestimoniaMss": ntestms,
        "cnAbsurd": by_lemma["[11]"],
        "cnAssTwo": by_lemma["[3]"],
        "cnAssThree": by_lemma["[4]"],
        "cnThmFour": by_lemma["[5]"],
        "cnDefOne": by_lemma["[2]"],
        "cnUnshared": len(istats["hapax"]),
    }
    L = [f"\\newcommand{{\\{k}}}{{{v}}}" for k, v in macros.items()]
    L.append(r"\newcommand{\cnUnsharedList}{" + ", ".join(r"\emph{" + esc(w) + "}" for w in istats["hapax"]) + "}")
    L.append(r"\newcommand{\cnTopKwic}{" + "; ".join(f"\\emph{{{esc(k)}}} ({v})" for v, k in top) + "}")
    for f, _ in FAMILIES:
        L.append(f"\\expandafter\\newcommand\\csname cnFam{f}\\endcsname{{{ftot[f]}}}")
    out["stats.tex"] = "\n".join(L)

    for name, content in out.items():
        with open(os.path.join(HERE, name), "w", encoding="utf-8") as f:
            f.write("% Generated by gen/generate.py; do not edit.\n" + content + "\n")
    print(f"ok: {len(LEMMATA)} lemmata; {nms} manuscripts; {istats['types']} word types; "
          f"{nkwic} concordance lines; {len(rows)} statements; {ntest} testimonia")


if __name__ == "__main__":
    main()
