"""Shared engine for the errata generators of REL-01-h and ETH-01-e.

Python 3, standard library only.  Everything is driven by a seeded
random.Random, so the output is deterministic.

The engine works on a *skeleton*: volumes, chapters (with page ranges),
numbered items (definitions, lemmas, ...) with the page on which each is
stated, numbered displays with their pages, the works each chapter cites,
and the vocabulary groups that describe each chapter's subject.  Every
generated corrigendum is drawn from that skeleton, so that it is locatable
(volume, chapter, page inside the chapter's range) and every cross-reference
it prints, wrong or right, names an item that exists.
"""

import random
import re

# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------

ROMAN = {1: "I", 2: "II", 3: "III", 4: "IV", 5: "V", 6: "VI", 7: "VII",
         8: "VIII", 9: "IX", 10: "X", 11: "XI", 12: "XII"}


def fmt_page(n, comma):
    if comma and n >= 1000:
        return "{:,}".format(n)
    return str(n)


def transpose_digits(n, rng, lo=1, hi=None):
    """A misprint of the page number n: two adjacent digits transposed, or
    one digit changed by one.  Never returns n."""
    s = str(n)
    cands = []
    for i in range(len(s) - 1):
        if s[i] != s[i + 1]:
            t = s[:i] + s[i + 1] + s[i] + s[i + 2:]
            if t[0] != "0":
                cands.append(int(t))
    for i in range(1, len(s)):
        for d in (-1, 1):
            c = int(s[i]) + d
            if 0 <= c <= 9:
                cands.append(int(s[:i] + str(c) + s[i + 1:]))
    if len(s) == 1:
        cands += [n + 1] + ([n - 1] if n > 1 else [])
    cands = sorted(set(c for c in cands if c != n and c > 0))
    if hi is not None:
        inb = [c for c in cands if lo <= c <= hi]
        if inb:
            cands = inb
    return rng.choice(cands)


VOWELS = "aeiou"


def misspell(word, rng):
    """A plausible compositor's misprint of a word (letters only)."""
    w = word
    n = len(w)
    cands = set()
    for i in range(1, n - 2):
        a, b = w[i], w[i + 1]
        if a != b and a.isalpha() and b.isalpha():
            cands.add(w[:i] + b + a + w[i + 2:])
    for i in range(1, n):
        if w[i] == w[i - 1] and w[i].isalpha():
            cands.add(w[:i] + w[i + 1:])
    for i in range(2, n - 1):
        if w[i] in VOWELS and w[i - 1] not in VOWELS and w[i + 1] not in VOWELS:
            cands.add(w[:i] + w[i + 1:])
    for i in range(1, n - 1):
        if (w[i] in "lmnprst" and w[i - 1] != w[i] and w[i + 1] != w[i]
                and w[i + 1] in VOWELS and w[i - 1] in VOWELS):
            cands.add(w[:i] + w[i] + w[i:])
    for a, b in (("ence", "ance"), ("ance", "ence"), ("ible", "able"),
                 ("ent", "ant"), ("ie", "ei"), ("ei", "ie"), ("tion", "sion")):
        k = w.find(a)
        if k > 0:
            cands.add(w[:k] + b + w[k + len(a):])
    cands.discard(w)
    cands = sorted(c for c in cands if c.lower() != w.lower())
    if not cands:
        return None
    return rng.choice(cands)


# ---------------------------------------------------------------------------
# formulas
# ---------------------------------------------------------------------------

SLOT_POOLS = {
    "w": ["w", "v", "u", "w'", "v'", "w_1", "w_2", "w_0"],
    "x": ["x", "y", "z"],
    "p": ["p", "q", "r"],
    "f": [r"{\phi}", r"{\psi}", r"{\chi}"],
    "i": ["i", "j", "k"],
}
SLOT_RE = re.compile(r"\[\[([a-z])([0-9]?)\]\]")


def fill_template(tpl, rng):
    used = {}
    taken = {k: set() for k in SLOT_POOLS}

    def rep(m):
        kind, idx = m.group(1), m.group(2)
        key = kind + idx
        if key not in used:
            pool = [c for c in SLOT_POOLS[kind] if c not in taken[kind]]
            c = rng.choice(pool)
            used[key] = c
            taken[kind].add(c)
        return used[key]

    out = SLOT_RE.sub(rep, tpl)
    sorts = {}
    for key, val in used.items():
        sorts.setdefault(key[0], set()).add(val)
    return out, [sorted(v) for k, v in sorted(sorts.items())]


def _replace_nth(s, pat, repl, rng):
    ms = list(re.finditer(pat, s))
    if not ms:
        return None
    m = rng.choice(ms)
    r = repl(m) if callable(repl) else repl
    return s[:m.start()] + r + s[m.end():]


def mutate_formula(f, varnames, rng):
    """One compositor's or author's slip in a formula: a single local change.
    Returns None if no mutation applies."""
    ops = []
    if r"\nec" in f or r"\pos" in f:
        ops.append(lambda s: _replace_nth(
            s, r"\\nec|\\pos",
            lambda m: r"\pos" if m.group(0) == r"\nec" else r"\nec", rng))
    if r"\forall" in f or r"\exists" in f:
        ops.append(lambda s: _replace_nth(
            s, r"\\forall|\\exists",
            lambda m: r"\exists" if m.group(0) == r"\forall" else r"\forall", rng))
    if r"\wedge" in f or r"\vee" in f:
        ops.append(lambda s: _replace_nth(
            s, r"\\wedge|\\vee",
            lambda m: r"\vee" if m.group(0) == r"\wedge" else r"\wedge", rng))
    if re.search(r"\\to(?![a-z])", f):
        ops.append(lambda s: _replace_nth(s, r"\\to(?![a-z])", r"\leftrightarrow", rng))
    if r"\leftrightarrow" in f:
        ops.append(lambda s: _replace_nth(s, r"\\leftrightarrow", r"\to", rng))
    if r"\neg" in f:
        ops.append(lambda s: _replace_nth(s, r"\\neg", "", rng))
    if r"\notin" in f or re.search(r"\\in(?![a-z])", f):
        ops.append(lambda s: _replace_nth(
            s, r"\\notin|\\in(?![a-z])",
            lambda m: r"\in" if m.group(0) == r"\notin" else r"\notin", rng))
    if r"\leq" in f or r"\geq" in f:
        ops.append(lambda s: _replace_nth(
            s, r"\\leq|\\geq",
            lambda m: r"\geq" if m.group(0) == r"\leq" else r"\leq", rng))
    if re.search(r"(?<![\\{])[<>](?!=)", f):
        ops.append(lambda s: _replace_nth(
            s, r"(?<![\\{])[<>](?!=)",
            lambda m: ">" if m.group(0) == "<" else "<", rng))
    if r"\subseteq" in f or r"\supseteq" in f:
        ops.append(lambda s: _replace_nth(
            s, r"\\subseteq|\\supseteq",
            lambda m: r"\supseteq" if m.group(0) == r"\subseteq" else r"\subseteq", rng))
    rel = r"([a-z](?:'|_[0-9])?)R([a-z](?:'|_[0-9])?)"
    if re.search(rel, f):
        ops.append(lambda s: _replace_nth(
            s, rel, lambda m: m.group(2) + "R" + m.group(1), rng))
    if "_1" in f or "_2" in f:
        ops.append(lambda s: _replace_nth(
            s, r"_[12]", lambda m: "_2" if m.group(0) == "_1" else "_1", rng))
    if "_{i}" in f or "_{j}" in f or "_{k}" in f:
        ops.append(lambda s: _replace_nth(
            s, r"_\{[ijk]\}",
            lambda m: "_{" + rng.choice([c for c in "ijk" if c != m.group(0)[2]]) + "}",
            rng))
    sorts = [[v for v in grp if re.fullmatch(r"[a-z]'?", v)] for grp in varnames]
    sorts = [g for g in sorts if len(g) >= 2]
    if sorts:
        def varswap(s):
            simple = rng.choice(sorts)
            a = rng.choice(simple)
            b = rng.choice([v for v in simple if v != a])
            pat = r"(?<![\\A-Za-z])" + re.escape(a) + r"(?![A-Za-z'])"
            return _replace_nth(s, pat, b, rng)
        ops.append(varswap)
    rng.shuffle(ops)
    for op in ops:
        g = op(f)
        if g and g != f:
            return g
    return None


# ---------------------------------------------------------------------------
# skeleton
# ---------------------------------------------------------------------------

class Item:
    __slots__ = ("kind", "num", "page", "vol", "ch", "idx")

    def __init__(self, kind, num, page, vol, ch, idx):
        self.kind, self.num, self.page = kind, num, page
        self.vol, self.ch, self.idx = vol, ch, idx

    def label(self):
        return "{}~{}".format(self.kind, self.num)


class Chapter:
    def __init__(self, vol, num, title, start, end, groups, cites, special=None):
        self.vol, self.num, self.title = vol, num, title
        self.start, self.end = start, end
        self.groups = groups
        self.cites = cites
        self.special = special          # None, 'bib', 'names', 'subjects', 'results'
        self.items = []
        self.displays = []              # (num, page)
        self.lemma_range = None

    @property
    def pages(self):
        return self.end - self.start + 1

    def proof_items(self):
        return [it for it in self.items
                if it.kind in ("Lemma", "Proposition", "Theorem", "Corollary")]


class Volume:
    def __init__(self, num, title, start, end, chapters):
        self.num, self.title, self.start, self.end = num, title, start, end
        self.chapters = chapters

    @property
    def roman(self):
        return ROMAN[self.num]


KIND_WEIGHTS = [("Definition", 22), ("Lemma", 26), ("Proposition", 24),
                ("Theorem", 10), ("Corollary", 10), ("Remark", 8)]


def weighted(rng, pairs):
    tot = sum(w for _, w in pairs)
    r = rng.uniform(0, tot)
    acc = 0
    for k, w in pairs:
        acc += w
        if r <= acc:
            return k
    return pairs[-1][0]


def _segment_pages(rng, n, lo, hi, fixed):
    """n sorted pages in [lo, hi]; positions in `fixed` (1-based) get the given
    page, and the others are sampled inside the segment between fixed ones."""
    pages = [None] * (n + 1)
    for k, pg in fixed.items():
        pages[k] = pg
    bounds = [(0, lo)] + sorted(fixed.items()) + [(n + 1, hi)]
    for (k0, p0), (k1, p1) in zip(bounds, bounds[1:]):
        seg = sorted(rng.randint(p0, p1) for _ in range(k1 - k0 - 1))
        for j, pg in enumerate(seg):
            pages[k0 + 1 + j] = pg
    return pages[1:]


def build_items(ch, rng, density, overrides):
    """Numbered items of a chapter, shared counter c.n as in the class."""
    n = max(3, int(round(ch.pages * density)))
    if overrides:
        n = max(n, max(overrides) + 2)
    pages = _segment_pages(rng, n, ch.start + 1, ch.end - 1,
                           {k: pg for k, (kind, pg) in overrides.items()})
    items = []
    for k in range(1, n + 1):
        kind = "Definition" if k == 1 else weighted(rng, KIND_WEIGHTS)
        if k in overrides:
            kind = overrides[k][0]
        items.append(Item(kind, "{}.{}".format(ch.num, k), pages[k - 1],
                          ch.vol, ch.num, k))
    ch.items = items


def build_displays(ch, rng, density, fixed):
    n = max(2, int(round(ch.pages * density)))
    if fixed:
        n = max(n, max(fixed) + 1)
    pages = _segment_pages(rng, n, ch.start + 1, ch.end - 1, fixed)
    ch.displays = [(k, pages[k - 1]) for k in range(1, n + 1)]


def build_lemma_items(ch, lo, hi):
    """Volume-wide consecutive lemma numbering (e.g. REL-01 Volume X)."""
    ch.lemma_range = (lo, hi)
    span = ch.pages - 2
    cnt = hi - lo + 1
    items = []
    for k in range(lo, hi + 1):
        page = ch.start + 1 + ((k - lo) * span) // cnt
        items.append(Item("Lemma", str(k), page, ch.vol, ch.num, k - lo + 1))
    ch.items = items


# ---------------------------------------------------------------------------
# entries
# ---------------------------------------------------------------------------

class Entry:
    __slots__ = ("page", "pos", "loc", "body", "note", "dag", "etype")

    def __init__(self, page, pos, loc, body, note="", dag=False, etype=""):
        self.page, self.pos, self.loc = page, pos, loc
        self.body, self.note, self.dag, self.etype = body, note, dag, etype


def forread(a, b, math=False):
    if math:
        return r"\textit{for} $" + a + r"$ \textit{read} $" + b + "$"
    return r"\textit{for} " + a + r" \textit{read} " + b


class Generator:
    """Generates corrigenda for one volume from the skeleton and vocabulary."""

    def __init__(self, book, seed):
        self.book = book
        self.rng = random.Random(seed)
        self.seen = set()       # global content keys (dedupe)
        self.used_loc = set()   # (page, loc)
        self.used_pos = set()   # (page, line)
        self.used_disp = set()  # (vol, ch, display)
        self.counts = {}
        self.limits = {}

    # -- location helpers --------------------------------------------------
    def P(self, n):
        return fmt_page(n, self.book.comma)

    def line_loc(self, page, lo=1, hi=40):
        rng = self.rng
        for _ in range(30):
            line = rng.randint(lo, hi)
            if (page, line) in self.used_pos:
                continue
            self.used_pos.add((page, line))
            if line > 32 and rng.random() < 0.6:
                return line, r"l.~{} from foot".format(41 - line)
            return line, r"l.~{}".format(line)
        return None, None

    def rand_page(self, ch):
        return self.rng.randint(ch.start + 1, ch.end)

    def page_ok(self, page):
        return page not in self.book.reserved_pages

    def limit(self, key, n):
        """Allow at most n uses of a key (counted on success of the caller's
        other checks only approximately: the count is taken here)."""
        c = self.limits.get(key, 0)
        if c >= n:
            return False
        self.limits[key] = c + 1
        return True

    def add(self, key):
        if key in self.seen:
            return False
        self.seen.add(key)
        return True

    # -- vocabulary access ---------------------------------------------------
    def groups(self, ch):
        return [self.book.groups[g] for g in ch.groups]

    # -- entry types ---------------------------------------------------------
    def e_typo(self, vol, ch):
        rng = self.rng
        terms = []
        for g in self.groups(ch):
            terms.extend(g.get("terms", []))
        terms.extend(self.book.groups["GEN"]["terms"])
        word = rng.choice(terms)
        wrong = misspell(word, rng)
        if not wrong or not self.limit(("typow", word), getattr(self.book, "typo_limit", 5)) or not self.add(("typo", word, wrong)):
            return None
        page = self.rand_page(ch)
        if not self.page_ok(page):
            return None
        pos, loc = self.line_loc(page)
        if pos is None:
            return None
        return Entry(page, pos, loc, forread(wrong.replace("_", r"\_"), word.replace("_", r"\_")),
                     etype="typo")

    def e_swap(self, vol, ch):
        rng = self.rng
        pool = []
        for g in self.groups(ch):
            pool.extend(g.get("swaps", []))
        if not pool:
            return None
        a, b = rng.choice(pool)
        a2, b2 = a, b
        # fill shared slots identically in wrong and right
        joint, _ = fill_template(a + "|||" + b, rng)
        a2, b2 = joint.split("|||")
        if not self.add(("swap", vol.num, a, b)) or not self.add(("swapf", a2, b2)):
            return None
        page = self.rand_page(ch)
        if not self.page_ok(page):
            return None
        pos, loc = self.line_loc(page)
        if pos is None:
            return None
        return Entry(page, pos, loc, forread(a2, b2), etype="wording")

    def e_insert(self, vol, ch):
        rng = self.rng
        pool = []
        for g in self.groups(ch):
            pool.extend(g.get("inserts", []))
        pool.extend(self.book.groups["GEN"].get("inserts", []))
        a, b = rng.choice(pool)
        joint, _ = fill_template(a + "|||" + b, rng)
        a2, b2 = joint.split("|||")
        if b2.startswith("DELETE"):
            body = r"\textit{delete} " + a2
            key = ("del", vol.num, a2, rng.randint(0, 3))
        else:
            body = r"\textit{after} " + a2 + r" \textit{insert} " + b2
            key = ("ins", vol.num, a, b)
        if not self.add(key):
            return None
        page = self.rand_page(ch)
        if not self.page_ok(page):
            return None
        pos, loc = self.line_loc(page)
        if pos is None:
            return None
        return Entry(page, pos, loc, body, etype="omission")

    def e_formula(self, vol, ch):
        rng = self.rng
        pool = []
        for g in self.groups(ch):
            pool.extend(g.get("formulas", []))
        if not pool:
            return None
        tpl = rng.choice(pool)
        if not self.limit(("ft", vol.num, ch.num, tpl), 3 if ch.pages > 60 else 2):
            return None
        right, names = fill_template(tpl, rng)
        wrong = mutate_formula(right, names, rng)
        if not wrong or not self.add(("f", wrong)):
            return None
        free = [d for d in ch.displays if (vol.num, ch.num, d[0]) not in self.used_disp
                and self.page_ok(d[1])]
        dag = False
        note = ""
        if free and rng.random() < 0.65:
            dnum, page = rng.choice(free)
            self.used_disp.add((vol.num, ch.num, dnum))
            pos = rng.randint(1, 40)
            loc = "display ({}.{})".format(ch.num, dnum)
            inproof = [it for it in ch.proof_items() if it.page <= page <= it.page + 1]
            if inproof:
                it = inproof[-1]
                loc = "proof of {}, ({}.{})".format(it.label(), ch.num, dnum)
                dag = True
            r = rng.random()
            later = [d for d in ch.displays if d[0] > dnum and d[1] - page <= 6]
            later = [d for d in later if (vol.num, ch.num, d[0]) not in self.used_disp]
            if r < 0.25 and later:
                d2 = rng.choice(later)
                self.used_disp.add((vol.num, ch.num, d2[0]))
                note = "; correctly printed in ({}.{}), p.~{}".format(ch.num, d2[0], self.P(d2[1]))
            elif r < 0.4:
                note = "; the formula is used in its correct form on p.~{}".format(
                    self.P(min(ch.end, page + rng.randint(1, 4))))
        else:
            page = self.rand_page(ch)
            if not self.page_ok(page):
                return None
            pos, loc = self.line_loc(page)
            if pos is None:
                return None
            inproof = [it for it in ch.proof_items() if it.page <= page <= it.page + 1]
            if inproof and rng.random() < 0.5:
                it = inproof[-1]
                loc = "proof of {}, {}".format(it.label(), loc)
                dag = True
        return Entry(page, pos, loc, forread(wrong, right, math=True), note, dag, "formula")

    def e_xref(self, vol, ch):
        rng = self.rng
        cands = [it for it in ch.proof_items() if it.idx >= 3]
        if not cands:
            return None
        t = rng.choice(cands)
        earlier = [it for it in ch.items if it.idx < t.idx and it.kind != "Remark"]
        if not earlier:
            return None
        right = rng.choice(earlier)
        same = [it for it in ch.items if it.kind == right.kind and it is not right
                and it is not t and abs(it.idx - right.idx) <= 5]
        if not same:
            return None
        wrong = rng.choice(same)
        if {t.num, right.num, wrong.num} & self.book.protected:
            return None
        pair = tuple(sorted((right.num, wrong.num)))
        if ("xp", vol.num, pair) in self.seen or not self.add(("x", vol.num, t.num, right.num)):
            return None
        self.seen.add(("xp", vol.num, pair))
        page = min(ch.end, t.page + rng.choice([0, 0, 1]))
        if not self.page_ok(page):
            return None
        pos, loc = self.line_loc(page, 1, 30)
        if pos is None:
            return None
        loc = "proof of {}, {}".format(t.label(), loc)
        note = ""
        if rng.random() < 0.35:
            note = "; the step uses {} (p.~{})".format(right.label(), self.P(right.page))
        return Entry(page, pos, loc, forread(wrong.label(), right.label()), note, True, "xref")

    def e_xref_out(self, vol, ch):
        """Reference to a numbered item of another volume."""
        rng = self.rng
        targets = self.book.outside_targets(vol, ch)
        if not targets:
            return None
        right, rvol, wrong_pool = rng.choice(targets)
        if right.num in self.book.protected:
            return None
        wrongs = [w for w in wrong_pool if w is not right and w.kind == right.kind
                  and abs(w.idx - right.idx) <= 6 and w.num not in self.book.protected]
        if not wrongs:
            return None
        wrong = rng.choice(wrongs)
        if not self.add(("xo", vol.num, right.vol, right.num, wrong.num)):
            return None
        page = self.rand_page(ch)
        if not self.page_ok(page):
            return None
        pos, loc = self.line_loc(page)
        if pos is None:
            return None
        sfx = " of Volume~" + ROMAN[rvol]
        note = ""
        if right.page and rng.random() < 0.4:
            note = "; the result cited is on p.~{}".format(self.P(right.page))
        dag = False
        inproof = [it for it in ch.proof_items() if it.page <= page <= it.page + 1]
        if inproof and rng.random() < 0.6:
            loc = "proof of {}, {}".format(inproof[-1].label(), loc)
            dag = True
        return Entry(page, pos, loc, forread(wrong.label() + sfx, right.label() + sfx),
                     note, dag, "xref")

    def e_topic(self, vol, ch):
        rng = self.rng
        topics = [t for t in self.book.topics if (t[1], t[2]) != (vol.num, ch.num)]
        if not topics:
            return None
        phrase, tv, tc = rng.choice(topics)
        alts = []
        if tc is None:
            alts = [(n, None) for n in self.book.all_volume_nums if abs(n - tv) in (1, 2)]
        else:
            for vn, nch in self.book.chapter_counts.items():
                if vn == tv:
                    alts += [(tv, c) for c in range(1, nch + 1) if abs(c - tc) in (1, 2)]
                elif abs(vn - tv) == 1 and tc <= nch:
                    alts.append((vn, tc))
        if not alts:
            return None
        wv, wc = rng.choice(alts)

        def lab(v, c):
            return "Volume~{}".format(ROMAN[v]) + (", Chapter~{}".format(c) if c else "")
        if not self.limit(("tp", phrase), 2) or not self.add(("t", vol.num, phrase, wv, wc)):
            return None
        page = self.rand_page(ch)
        if not self.page_ok(page):
            return None
        pos, loc = self.line_loc(page)
        if pos is None:
            return None
        return Entry(page, pos, loc, forread(lab(wv, wc), lab(tv, tc)),
                     " (" + phrase + ")", False, "xref")

    def e_pageref(self, vol, ch):
        rng = self.rng
        pool = [it for c in vol.chapters for it in c.items
                if it.page and it.page < ch.end and it.kind != "Remark"]
        if not pool:
            return None
        it = rng.choice(pool)
        if it.num in self.book.protected:
            return None
        wrongp = transpose_digits(it.page, rng, vol.start, vol.end)
        if not self.add(("pg", vol.num, it.vol, it.num)):
            return None
        page = self.rand_page(ch)
        if page <= it.page or not self.page_ok(page):
            page = rng.randint(max(ch.start + 1, it.page + 1), ch.end) if it.page + 1 <= ch.end else None
            if page is None or not self.page_ok(page):
                return None
        pos, loc = self.line_loc(page)
        if pos is None:
            return None
        return Entry(page, pos, loc, forread("p.~" + self.P(wrongp), "p.~" + self.P(it.page)),
                     " (" + it.label() + ")", False, "xref")

    def e_cite(self, vol, ch):
        rng = self.rng
        if not ch.cites:
            return None
        key = rng.choice(ch.cites)
        w = self.book.bib[key]
        if w.get("classic") or (w.get("slips") and rng.random() < 0.3):
            pool = w.get("slips", [])
            if not pool:
                return None
            a, b = rng.choice(pool)
        else:
            cite = self.book.cite_text(key)
            op = rng.random()
            if op < 0.45:
                yr = w["year"]
                cands = [yr - 1, yr + 1]
                taken = self.book.years_by_surname(w)
                cands = [c for c in cands if c not in taken]
                if not cands:
                    return None
                a = self.book.cite_text(key, year=rng.choice(cands))
                b = cite
            elif op < 0.8:
                sur = w["authors"][0][0]
                plain = sur.replace("ü", "u").replace("ö", "o").replace("á", "a").replace("ò", "o")
                if plain != sur and rng.random() < 0.6:
                    wrong_sur = plain
                else:
                    letters = re.sub(r"[^A-Za-z]", "", sur)
                    if letters != sur or len(sur) < 5:
                        return None
                    wrong_sur = misspell(sur, rng)
                    if not wrong_sur:
                        return None
                a = self.book.cite_text(key, surname=wrong_sur)
                b = cite
            else:
                others = [k for k in ch.cites if k != key and not self.book.bib[k].get("classic")]
                if not others or not w.get("topic"):
                    return None
                k2 = rng.choice(others)
                a = self.book.cite_text(k2)
                b = cite
                if not self.add(("cw", vol.num, k2, key)):
                    return None
                page = self.rand_page(ch)
                if not self.page_ok(page):
                    return None
                pos, loc = self.line_loc(page)
                if pos is None:
                    return None
                return Entry(page, pos, loc, forread(a, b), " (" + w["topic"] + ")",
                             False, "citation")
        if not self.limit(("ck", key), 3) or not self.add(("c", a, b)):
            return None
        page = self.rand_page(ch)
        if not self.page_ok(page):
            return None
        if rng.random() < 0.3:
            pos = 50 + rng.randint(1, 9)
            loc = "n.~{}".format(rng.randint(1, 24))
            if (page, loc) in self.used_loc:
                return None
            self.used_loc.add((page, loc))
        else:
            pos, loc = self.line_loc(page)
            if pos is None:
                return None
        return Entry(page, pos, loc, forread(a, b), "", False, "citation")

    # -- back matter -----------------------------------------------------------
    def e_bib(self, vol, ch):
        rng = self.rng
        key = rng.choice(self.book.bib_order)
        w = self.bib_entry(key)
        if w is None:
            return None
        page = self.book.bib_page(key, ch)
        fields = []
        if w.get("vol"):
            fields.append("vol")
        if w.get("pages"):
            fields.append("pages")
        if w.get("publisher"):
            fields.append("publisher")
        fields += ["year", "title", "initials"]
        f = rng.choice(fields)
        head = self.book.bib_head(key)
        if f == "vol":
            right = w["vol"]
            m = re.match(r"(\d+)(\((\d+)\))?$", right)
            if not m:
                return None
            v, iss = int(m.group(1)), m.group(3)
            if iss and rng.random() < 0.6:
                ni = int(iss) + rng.choice([-1, 1])
                if ni < 1:
                    ni = int(iss) + 1
                wrong = "{}({})".format(v, ni)
            else:
                wrong = "{}{}".format(transpose_digits(v, rng) if v > 9 else v + 1,
                                      "({})".format(iss) if iss else "")
        elif f == "pages":
            right = w["pages"]
            a, b = right.split("--")
            if rng.random() < 0.5:
                wrong = "{}--{}".format(a, transpose_digits(int(b), rng))
            else:
                wrong = "{}--{}".format(transpose_digits(int(a), rng), b)
            wa, wb = wrong.split("--")
            if int(wb) <= int(wa):
                return None
        elif f == "publisher":
            right = w["publisher"]
            alts = [p for p in self.book.publisher_confusions.get(right, []) if p != right]
            if not alts:
                return None
            wrong = rng.choice(alts)
        elif f == "year":
            right = str(w["year"])
            taken = self.book.years_by_surname(w)
            cands = [c for c in (w["year"] - 1, w["year"] + 1) if c not in taken]
            if not cands:
                return None
            wrong = str(rng.choice(cands))
        elif f == "title":
            words = [x for x in re.findall(r"[A-Za-z]+", w["title"]) if len(x) >= 6]
            if not words:
                return None
            right = rng.choice(words)
            wrong = misspell(right, rng)
            if not wrong:
                return None
        else:
            sur, ini = w["authors"][0]
            if not ini or len(ini) < 2:
                return None
            letters = "ABCDEFGHJKLMNPRSTW"
            first = ini[0]
            alt = rng.choice([c for c in letters if c != first])
            right = ini
            wrong = alt + ini[1:]
        if not self.add(("bib", key, f, wrong)):
            return None
        pos = self.book.bib_order.index(key)
        if (page, head) in self.used_loc:
            return None
        self.used_loc.add((page, head))
        return Entry(page, pos, head, forread(wrong, right), "", False, "bibliography")

    def e_name_index(self, vol, ch):
        rng = self.rng
        name = rng.choice(sorted(self.book.name_pages))
        chs = self.book.name_pages[name]
        if not chs:
            return None
        c = rng.choice(chs)
        right = rng.randint(c[0], c[1])
        page = self.book.index_page(ch, name)
        loc = r"s.v.\ " + name
        if (page, loc) in self.used_loc:
            return None
        if rng.random() < 0.75:
            wrong = transpose_digits(right, rng, 1, self.book.last_page)
            body = forread(self.P(wrong), self.P(right))
        else:
            body = r"\textit{add} " + self.P(right)
        if not self.add(("ni", name, right)):
            return None
        self.used_loc.add((page, loc))
        return Entry(page, self.book.index_rank(ch, name), loc, body, "", False, "index")

    def e_subject_index(self, vol, ch):
        rng = self.rng
        term = rng.choice(sorted(self.book.subject_pages))
        chs = self.book.subject_pages[term]
        c = rng.choice(chs)
        right = rng.randint(c[0], c[1])
        page = self.book.index_page(ch, term)
        loc = r"s.v.\ " + term
        if (page, loc) in self.used_loc:
            return None
        wrong = transpose_digits(right, rng, 1, self.book.last_page)
        if rng.random() < 0.8:
            body = forread(self.P(wrong), self.P(right))
        else:
            body = r"\textit{add} " + self.P(right)
        if not self.add(("si", term, right)):
            return None
        self.used_loc.add((page, loc))
        return Entry(page, self.book.index_rank(ch, term), loc, body, "", False, "index")

    def e_results_index(self, vol, ch):
        rng = self.rng
        it = rng.choice(self.book.result_items)
        if it.num in self.book.protected:
            return None
        page = self.book.results_page(ch, it)
        loc = "{} (Vol.~{})".format(it.label(), ROMAN[it.vol])
        if (page, loc) in self.used_loc:
            return None
        wrong = transpose_digits(it.page, rng, 1, self.book.last_page)
        if not self.add(("ri", it.vol, it.num)):
            return None
        self.used_loc.add((page, loc))
        return Entry(page, self.book.result_items.index(it), loc, forread(self.P(wrong), self.P(it.page)),
                     "", False, "index")

    def bib_entry(self, key):
        w = self.book.bib[key]
        if w.get("classic") or w.get("no_errata"):
            return None
        return w

    # -- per chapter -----------------------------------------------------------
    def chapter_entries(self, vol, ch, n, weights):
        out = []
        fn = {"typo": self.e_typo, "swap": self.e_swap, "insert": self.e_insert,
              "formula": self.e_formula, "xref": self.e_xref, "xref_out": self.e_xref_out,
              "topic": self.e_topic, "pageref": self.e_pageref, "cite": self.e_cite,
              "bib": self.e_bib, "names": self.e_name_index,
              "subjects": self.e_subject_index, "results": self.e_results_index}
        tries = 0
        while len(out) < n and tries < n * 60:
            tries += 1
            t = weighted(self.rng, weights)
            e = fn[t](vol, ch)
            if e is None:
                continue
            if not (ch.start <= e.page <= ch.end):
                continue
            out.append(e)
            self.counts[e.etype] = self.counts.get(e.etype, 0) + 1
        return out

    def running_head(self, vol, ch):
        rng = self.rng
        others = [c for c in vol.chapters if abs(c.num - ch.num) == 1 and not c.special]
        if not others:
            return None
        o = rng.choice(others)
        a = ch.start + 1 + ((ch.start + 1) % 2)   # first even page after the opening
        b = ch.end if ch.end % 2 == 0 else ch.end - 1
        if b <= a:
            return None
        e = Entry(a, 0, r"running heads, pp.~{}--{} (even)".format(self.P(a), self.P(b)),
                  forread(o.short, ch.short), "", False, "typo")
        self.counts["typo"] = self.counts.get("typo", 0) + 1
        return e


# ---------------------------------------------------------------------------
# LaTeX output
# ---------------------------------------------------------------------------

def latex_chapter(ch, entries, P, pointers):
    rows = []
    for e in entries:
        dag = r"\dag\," if e.dag else ""
        rows.append((e.page, e.pos, r"{}{} & {} & {}{} \\".format(
            dag, P(e.page), e.loc, e.body, e.note)))
    for (page, pos, loc, text) in pointers:
        rows.append((page, pos, r"{} & {} & {} \\".format(P(page), loc, text)))
    rows.sort(key=lambda r: (r[0], r[1]))
    head = r"\subsection*{{Chapter~{}. {} \hfill \normalfont\small pp.~{}--{}}}".format(
        ch.num, ch.title, P(ch.start), P(ch.end))
    if ch.special:
        head = r"\subsection*{{{} \hfill \normalfont\small pp.~{}--{}}}".format(
            ch.title, P(ch.start), P(ch.end))
    body = [head, r"\begin{errlist}"] + [r[2] for r in rows] + [r"\end{errlist}", ""]
    return "\n".join(body), len(rows)


# ---------------------------------------------------------------------------
# the book: skeleton plus bibliography and indices
# ---------------------------------------------------------------------------

def plain(s):
    for a, b in (("ü", "u"), ("ö", "o"), ("á", "a"), ("ò", "o"), ("é", "e"),
                 ("\\", ""), ("{", ""), ("}", ""), ("~", " ")):
        s = s.replace(a, b)
    return s.lower()


class Book:
    def __init__(self, volumes, comma, groups, bib, topics, chapter_counts,
                 publisher_confusions, ext_refs, reserved_pages, extra_name_ranges=()):
        self.volumes = volumes
        self.last_page = max(v.end for v in volumes)
        self.comma = comma
        self.groups = groups
        self.bib = bib
        self.topics = topics
        self.chapter_counts = chapter_counts
        self.all_volume_nums = sorted(chapter_counts)
        self.publisher_confusions = publisher_confusions
        self.ext_refs = ext_refs
        self.reserved_pages = set(reserved_pages)
        self.protected = set()
        self.bib_order = sorted(bib, key=lambda k: (plain(bib[k]["authors"][0][0]),
                                                    bib[k]["year"], bib[k].get("suffix", "")))
        # name index: author -> page ranges of chapters citing the author
        names = {}
        chapters = [c for v in volumes for c in v.chapters if not c.special]
        ranges = [(c.start, c.end, c.cites) for c in chapters] + list(extra_name_ranges)
        for lo, hi, cites in ranges:
            for k in cites:
                for sur, ini in bib[k]["authors"]:
                    nm = sur + (", " + ini if ini else "")
                    names.setdefault(nm, [])
                    if (lo, hi) not in names[nm]:
                        names[nm].append((lo, hi))
        self.name_pages = names
        subj = {}
        for c in chapters:
            for g in c.groups:
                for t in groups[g].get("index_terms", []):
                    subj.setdefault(t, [])
                    if (c.start, c.end) not in subj[t]:
                        subj[t].append((c.start, c.end))
        self.subject_pages = subj
        self.result_items = [it for c in chapters for it in c.items
                             if it.kind != "Remark" and it.page]
        self.result_items.sort(key=lambda it: (it.vol, it.ch, it.idx))

    def cite_text(self, key, year=None, surname=None):
        w = self.bib[key]
        s = [a[0] for a in w["authors"]]
        if surname:
            s[0] = surname
        if len(s) == 1:
            names = s[0]
        elif len(s) == 2:
            names = s[0] + " and " + s[1]
        else:
            names = s[0] + r" et~al."
        y = str(year) if year else str(w["year"]) + w.get("suffix", "")
        return "{} ({})".format(names, y)

    def years_by_surname(self, w):
        sur = w["authors"][0][0]
        return set(x["year"] for x in self.bib.values() if x["authors"][0][0] == sur)

    def bib_head(self, key):
        w = self.bib[key]
        sur, ini = w["authors"][0]
        extra = r" et~al." if len(w["authors"]) > 2 else (
            " and " + w["authors"][1][0] + ", " + w["authors"][1][1] if len(w["authors"]) == 2 else "")
        return "{}{}{} ({}{})".format(sur, ", " + ini if ini else "", extra,
                                      w["year"], w.get("suffix", ""))

    @staticmethod
    def _spread(ch, idx, n):
        span = ch.pages - 1
        return ch.start + 1 + (idx * span) // max(1, n)

    def bib_page(self, key, ch):
        return self._spread(ch, self.bib_order.index(key), len(self.bib_order))

    def index_rank(self, ch, term):
        pool = sorted(self.name_pages, key=plain) if ch.special == "names" else \
            sorted(self.subject_pages, key=plain)
        return pool.index(term)

    def index_page(self, ch, term):
        pool = sorted(self.name_pages, key=plain) if ch.special == "names" else \
            sorted(self.subject_pages, key=plain)
        return self._spread(ch, pool.index(term), len(pool))

    def results_page(self, ch, it):
        return self._spread(ch, self.result_items.index(it), len(self.result_items))

    def outside_targets(self, vol, ch):
        out = []
        for oc in self.ext_refs(vol, ch):
            for it in oc.items:
                if it.kind == "Remark":
                    continue
                out.append((it, oc.vol, oc.items))
        return out


def bib_latex(w):
    """Full reference for the bibliography of the erratum itself."""
    au = w["authors"]

    def one(a):
        return a[0] + (", " + a[1] if a[1] else "")
    if len(au) == 1:
        names = one(au[0])
    else:
        names = ", ".join(one(a) for a in au[:-1]) + " and " + one(au[-1])
    s = "{} ({}). ".format(names, w["year"])
    if w.get("journal"):
        s += "{}. \\emph{{{}}}".format(w["title"], w["journal"])
        if w.get("vol"):
            s += ", " + w["vol"]
        if w.get("pages"):
            s += ", " + w["pages"]
        s += "."
    elif w.get("inbook"):
        s += "{}. In {}, \\emph{{{}}}".format(w["title"], w["eds"], w["inbook"])
        if w.get("pages"):
            s += " (pp.~{})".format(w["pages"])
        s += ". {}.".format(w["publisher"])
    else:
        s += "\\emph{{{}}}. {}.".format(w["title"], w["publisher"])
    return s
