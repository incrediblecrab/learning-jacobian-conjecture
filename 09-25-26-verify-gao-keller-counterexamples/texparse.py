"""Extract polynomial displays from the paper's LaTeX source and parse them into any ring.

Used by implementation A (verify_exact.py) and by the Lean gate (check_lean.py); implementation B has its own, differently built translator.
"""
import re
from fractions import Fraction

_NOISE = [r"\\\\\[[0-9.]+pt\]", r"\\\\", r"&", r"\{\}", r"\\[,;!:]", r"\\q?quad",
          r"\\[bB]igg?[lr]?", r"\\left", r"\\right", r"\\displaystyle"]


def extract(tex, anchor, start, stops):
    """Return the raw LaTeX between `start` (first occurrence after `anchor`) and the nearest of `stops`."""
    base = 0
    if anchor:
        base = tex.index(anchor)
    i = tex.index(start, base) + len(start)
    j = min(tex.index(s, i) for s in stops if s in tex[i:])
    return tex[i:j]


def clean(raw):
    s = raw.replace("\\cdot", "*")
    for pat in _NOISE:
        s = re.sub(pat, " ", s)
    s = s.strip()
    while s and s[-1] in ",.":
        s = s[:-1].rstrip()
    return s


class _Parser:
    """Recursive descent over LaTeX math: sums, implicit products, ^ powers, \\frac/\\tfrac, subscripted letters."""

    def __init__(self, s, const, var):
        self.s, self.i, self.const, self.var = s, 0, const, var

    def peek(self):
        while self.i < len(self.s) and self.s[self.i].isspace():
            self.i += 1
        return self.s[self.i] if self.i < len(self.s) else ""

    def expect(self, ch):
        if self.peek() != ch:
            raise ValueError("expected %r at %d in %r" % (ch, self.i, self.s[max(0, self.i - 30):self.i + 30]))
        self.i += 1

    def arg(self):
        """A TeX macro argument: a brace group or a single character."""
        c = self.peek()
        if c == "{":
            depth, j = 0, self.i
            while True:
                if self.s[j] == "{":
                    depth += 1
                elif self.s[j] == "}":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            out, self.i = self.s[self.i + 1:j], j + 1
            return out
        self.i += 1
        return c

    def expr(self):
        val, first = None, True
        while True:
            c = self.peek()
            if c and c in "+-":
                self.i += 1
                sign = -1 if c == "-" else 1
            elif first:
                sign = 1
            else:
                break
            t = self.term()
            t = -t if sign < 0 else t
            val = t if val is None else val + t
            first = False
        return val

    def term(self):
        val = self.factor()
        while True:
            c = self.peek()
            if c == "" or c in "+-)}":
                return val
            if c == "*":
                self.i += 1
                continue
            val = val * self.factor()

    def factor(self):
        base = self.atom()
        if self.peek() == "^":
            self.i += 1
            e = int(re.sub(r"\s", "", self.arg()))
            base = base ** e
        return base

    def atom(self):
        c = self.peek()
        if c.isdigit():
            j = self.i
            while j < len(self.s) and self.s[j].isdigit():
                j += 1
            n, self.i = int(self.s[self.i:j]), j
            return self.const(Fraction(n))
        if c and c in "({":
            close = ")" if c == "(" else "}"
            self.i += 1
            v = self.expr()
            self.expect(close)
            return v
        if c == "\\":
            m = re.match(r"\\([A-Za-z]+)", self.s[self.i:])
            self.i += len(m.group(0))
            if m.group(1) in ("frac", "tfrac", "dfrac"):
                num = _Parser(self.arg(), self.const, self.var).expr()
                den = _Parser(self.arg(), Fraction, None).expr()
                return num * self.const(1 / Fraction(den))
            raise ValueError("unsupported macro \\%s" % m.group(1))
        if c.isalpha():
            name = c
            self.i += 1
            if self.peek() == "_":
                self.i += 1
                name += re.sub(r"\s", "", self.arg())
            return self.var(name)
        raise ValueError("unexpected %r at %d in %r" % (c, self.i, self.s[max(0, self.i - 30):self.i + 30]))


def parse(latex, const, var):
    p = _Parser(clean(latex), const, var)
    v = p.expr()
    if p.peek() != "":
        raise ValueError("trailing input %r" % p.s[p.i:p.i + 40])
    return v
