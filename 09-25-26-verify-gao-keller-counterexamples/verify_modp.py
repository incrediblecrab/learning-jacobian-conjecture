#!/usr/bin/env python3
"""Implementation B: an independent rebuild of Gao's six Keller maps (arXiv:2608.00222v1) over GF(p).

B shares no code with implementation A (verify_exact.py, texparse.py) and does not use sympy. Instead it has:
- its own tokenizer and precedence-climbing parser, used both for recipes.py and for the LaTeX displays;
- its own LaTeX-to-token translator;
- polynomials as dicts from packed-integer monomials to coefficients mod p, or to Fractions for exact checks over Q;
- its own derivatives, recursive Horner composition, and Leibniz determinants.

B reads the paper data from recipes.py. It also reads A's results/fingerprints.json, so that the two rebuilds are compared at the same points; run verify_exact.py first. Exit status is 1 if any check fails.
"""
import argparse
import itertools
import json
import os
import platform
import random
import re
import sys
import time
from fractions import Fraction

import recipes

HERE = os.path.dirname(os.path.abspath(__file__))
PRIME = 2**61 - 1
BITS = 16  # exponent field width of a packed monomial; every degree here is below 100
MASK = (1 << BITS) - 1


class Tally:
    def __init__(self):
        self.good = self.bad = 0

    def __call__(self, key, text, ok, extra=""):
        ok = bool(ok)
        self.good += ok
        self.bad += not ok
        print("%s  %-3s %s%s" % ("PASS" if ok else "FAIL", key, text, "  [%s]" % extra if extra else ""), flush=True)
        return ok

    def say(self, key, text):
        print("INFO  %-3s %s" % (key, text), flush=True)


# ---- packed monomials and polynomial arithmetic (P = modulus, or None for exact Fractions) -------------------
def pack(exps):
    mono = 0
    for j, ex in enumerate(exps):
        if not 0 <= ex <= MASK:
            raise OverflowError("exponent %d outside the packed field" % ex)
        mono |= ex << (BITS * j)
    return mono


def unpack(mono, n):
    return tuple((mono >> (BITS * j)) & MASK for j in range(n))


def coef(fr, P):
    fr = Fraction(fr)
    return fr.numerator * pow(fr.denominator, -1, P) % P if P else fr


def reduce_(acc, P):
    if P:
        out = {}
        for mono, cf in acc.items():
            cf %= P
            if cf:
                out[mono] = cf
        return out
    return {mono: cf for mono, cf in acc.items() if cf}


def padd(a, b, P, sign=1):
    out = dict(a)
    for mono, cf in b.items():
        out[mono] = out.get(mono, 0) + (cf if sign > 0 else -cf)
    return reduce_(out, P)


def pmul(a, b, P):
    if len(a) < len(b):
        a, b = b, a
    acc = {}
    get = acc.get
    for mb, cb in b.items():
        for ma, ca in a.items():
            mono = ma + mb
            acc[mono] = get(mono, 0) + ca * cb
    return reduce_(acc, P)


def pscale(a, s, P):
    return reduce_({mono: cf * s for mono, cf in a.items()}, P)


def ppow(a, ex, P):
    out = {0: 1 if P else Fraction(1)}
    for _ in range(ex):
        out = pmul(out, a, P)
    return out


def pderiv(a, j, P):
    sh, out = BITS * j, {}
    for mono, cf in a.items():
        ex = (mono >> sh) & MASK
        if ex:
            out[mono - (1 << sh)] = cf * ex
    return reduce_(out, P)


def pdegree(a, n):
    return max(sum(unpack(mono, n)) for mono in a) if a else -1


def peval(a, n, pt, P):
    tabs = [[1] for _ in range(n)]
    total = 0
    for mono, cf in a.items():
        term = cf
        for j in range(n):
            ex = (mono >> (BITS * j)) & MASK
            if ex:
                tab = tabs[j]
                while len(tab) <= ex:
                    tab.append(tab[-1] * pt[j] % P if P else tab[-1] * pt[j])
                term = term * tab[ex] % P if P else term * tab[ex]
        total += term
    return total % P if P else total


def used_vars(a):
    seen = 0
    for mono in a:
        seen |= mono
    return sum(1 for j in range(8) if (seen >> (BITS * j)) & MASK)


def substitute(E, nv, images, P):
    """E(images[0], ..., images[nv-1]) by nested Horner schemes, outermost variable = the image with most variables."""
    order = sorted(range(nv), key=lambda j: (-used_vars(images[j]), -len(images[j]), j))

    def go(terms, depth):
        if depth == nv:
            (_, cf), = terms
            return {0: cf}
        j = order[depth]
        groups = {}
        for mono, cf in terms:
            groups.setdefault((mono >> (BITS * j)) & MASK, []).append((mono, cf))
        acc = {}
        for power in range(max(groups), -1, -1):
            if acc:
                acc = pmul(acc, images[j], P)
            if power in groups:
                acc = padd(acc, go(groups[power], depth + 1), P)
        return acc

    return go(list(E.items()), 0) if E else {}


def leibniz(M, mul, add, sub, one, zero, is_zero):
    """det M as the signed sum over all permutations."""
    n, total = len(M), zero
    for perm in itertools.permutations(range(n)):
        factors = [M[i][perm[i]] for i in range(n)]
        if any(is_zero(f) for f in factors):
            continue
        prod = one
        for f in sorted(factors, key=lambda f: len(f) if isinstance(f, dict) else 0):
            prod = mul(prod, f)
        inversions = sum(1 for a in range(n) for b in range(a + 1, n) if perm[a] > perm[b])
        total = sub(total, prod) if inversions % 2 else add(total, prod)
    return total


def pdet(M, P):
    one = {0: 1 if P else Fraction(1)}
    return leibniz(M, lambda a, b: pmul(a, b, P), lambda a, b: padd(a, b, P), lambda a, b: padd(a, b, P, -1),
                   one, {}, lambda f: not f)


def ndet(M, P):
    return leibniz(M, lambda a, b: a * b % P, lambda a, b: (a + b) % P, lambda a, b: (a - b) % P,
                   1, 0, lambda f: f % P == 0)


# ---- one parser for recipe strings (Python syntax) and for LaTeX (after translation to the same tokens) --------
class Ring:
    def __init__(self, names, P):
        self.names, self.P = list(names), P

    def const(self, fr):
        cf = coef(fr, self.P)
        return {0: cf} if cf else {}

    def gen(self, name):
        if name not in self.names:
            raise NameError("unknown variable %r (ring has %s)" % (name, self.names))
        return {1 << (BITS * self.names.index(name)): 1 if self.P else Fraction(1)}


PY_TOKEN = re.compile(r"(\d+)|([A-Za-z_][A-Za-z0-9_]*)|(\*\*|[-+*/^()])|(\s+)")


def py_tokens(s):
    out, i = [], 0
    while i < len(s):
        mt = PY_TOKEN.match(s, i)
        if not mt:
            raise ValueError("cannot tokenize %r at %d" % (s, i))
        num, name, op, _ = mt.groups()
        if num:
            out.append(("n", int(num)))
        elif name:
            out.append(("v", name))
        elif op:
            out.append(("o", "^" if op == "**" else op))
        i = mt.end()
    return out


class Parser:
    PREC = {"+": 1, "-": 1, "*": 2, "/": 2}

    def __init__(self, toks, ring, env=None):
        self.t, self.i, self.R, self.env = toks, 0, ring, env or {}

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self):
        tok = self.peek()
        if tok is None:
            raise ValueError("unexpected end of expression")
        self.i += 1
        return tok

    def run(self):
        val = self.binary(1)
        if self.peek() is not None:
            raise ValueError("trailing tokens %r" % (self.t[self.i:self.i + 6],))
        return val

    def binary(self, level):
        lhs = self.unary()
        while True:
            tok = self.peek()
            if tok is None or tok[0] != "o" or tok[1] not in self.PREC or self.PREC[tok[1]] < level:
                return lhs
            self.i += 1
            rhs = self.binary(self.PREC[tok[1]] + 1)
            P = self.R.P
            if tok[1] == "+":
                lhs = padd(lhs, rhs, P)
            elif tok[1] == "-":
                lhs = padd(lhs, rhs, P, -1)
            elif tok[1] == "*":
                lhs = pmul(lhs, rhs, P)
            else:
                if set(rhs) != {0}:
                    raise ValueError("division by a non-constant or by zero")
                lhs = pscale(lhs, pow(rhs[0], -1, P) if P else 1 / rhs[0], P)

    def unary(self):
        tok = self.peek()
        if tok == ("o", "-"):
            self.i += 1
            return pscale(self.unary(), -1, self.R.P)
        if tok == ("o", "+"):
            self.i += 1
            return self.unary()
        base = self.atom()
        if self.peek() == ("o", "^"):
            self.i += 1
            tok = self.take()
            if tok == ("o", "("):
                tok, close = self.take(), self.take()
                if close != ("o", ")"):
                    raise ValueError("exponent must be a literal integer")
            if tok[0] != "n":
                raise ValueError("exponent must be a literal integer")
            base = ppow(base, tok[1], self.R.P)
        return base

    def atom(self):
        kind, val = self.take()
        if kind == "n":
            return self.R.const(val)
        if kind == "v":
            return self.env[val] if val in self.env else self.R.gen(val)
        if val == "(":
            inner = self.binary(1)
            if self.take() != ("o", ")"):
                raise ValueError("missing )")
            return inner
        raise ValueError("unexpected token %r" % val)


def from_recipe(s, ring, env=None):
    return Parser(py_tokens(s), ring, env).run()


def tex_group(s, i):
    """A TeX argument starting at s[i]: a brace group, or else one character."""
    while s[i].isspace():
        i += 1
    if s[i] != "{":
        return s[i], i + 1
    depth = 0
    for j in range(i, len(s)):
        depth += {"{": 1, "}": -1}.get(s[j], 0)
        if depth == 0:
            return s[i + 1:j], j + 1
    raise ValueError("unbalanced braces")


def tex_scan(s):
    out, i = [], 0
    while i < len(s):
        ch = s[i]
        if ch.isspace():
            i += 1
        elif ch.isdigit():
            j = i
            while j < len(s) and s[j].isdigit():
                j += 1
            out.append(("n", int(s[i:j])))
            i = j
        elif ch.isalpha():
            name, i = ch, i + 1
            if i < len(s) and s[i] == "_":
                sub, i = tex_group(s, i + 1)
                name += re.sub(r"[\s,]", "", sub)
            out.append(("v", name))
        elif ch == "\\":
            mt = re.match(r"\\([A-Za-z]+)", s[i:])
            if not mt:
                raise ValueError("stray backslash in %r" % s[i:i + 20])
            i += len(mt.group(0))
            if mt.group(1) in ("frac", "tfrac", "dfrac"):
                num, i = tex_group(s, i)
                den, i = tex_group(s, i)
                out += [("o", "(")] + tex_scan(num) + [("o", ")"), ("o", "/"), ("o", "(")] + tex_scan(den) + [("o", ")")]
            elif mt.group(1) == "cdot":
                out.append(("o", "*"))
            else:
                raise ValueError("unsupported LaTeX command \\%s" % mt.group(1))
        elif ch == "^":
            arg, i = tex_group(s, i + 1)
            out += [("o", "^"), ("o", "(")] + tex_scan(arg) + [("o", ")")]
        elif ch in "({":
            out.append(("o", "("))
            i += 1
        elif ch in ")}":
            out.append(("o", ")"))
            i += 1
        elif ch in "+-*":
            out.append(("o", ch))
            i += 1
        else:
            raise ValueError("unexpected character %r in LaTeX" % ch)
    return out


def tex_tokens(src):
    s = re.sub(r"\\\\(\[[^\]]*\])?", " ", src)
    s = re.sub(r"\\[,;:!]|\\q?quad|&", " ", s)
    s = re.sub(r"\\(?:[bB]igg?[lr]?|left|right)", " ", s)
    s = s.replace("{}", " ").strip().rstrip(",. \n")
    out = []
    for tok in tex_scan(s):
        # juxtaposition is multiplication: an operand followed by an operand
        if out and (out[-1][0] in "nv" or out[-1] == ("o", ")")) and (tok[0] in "nv" or tok == ("o", "(")):
            out.append(("o", "*"))
        out.append(tok)
    return out


def from_tex(src, ring):
    return Parser(tex_tokens(src), ring).run()


def tex_display(tex, anchor, start, stops):
    lo = tex.find(anchor) if anchor else 0
    at = tex.find(start, lo) if lo >= 0 else -1
    if at < 0:
        raise LookupError("display %r not found" % start)
    at += len(start)
    ends = [k for k in (tex.find(s, at) for s in stops) if k >= 0]
    if not ends:
        raise LookupError("end of display %r not found" % start)
    return tex[at:min(ends)]


# ---- the rebuild ---------------------------------------------------------------------------------------------
def rebuild(spec, P):
    """The map F from its recipe: returns (components in the paper's order, dict of intermediate objects)."""
    params, src = spec["params"], spec["source"]
    npar, n = len(params), len(src)
    r = n - 1
    c, k, d, e, m = spec["c"], spec["k"], spec["d"], spec["e"], spec["m"]
    RW = Ring(params, P)
    env = {}
    for name, s in spec.get("defs", []):
        env[name] = from_recipe(s, RW, env)
    Delta = [from_recipe(s, RW, env) for s in spec["Delta"]]
    if "X" in spec:
        X = [from_recipe(s, RW, env) for s in spec["X"]]
    else:
        G = [env[g] for g in spec["potentials"]]
        X1 = pscale(pdet([[pderiv(g, j, P) for j in range(npar)] for g in G], P), coef(Fraction(-1, c), P), P)
        X = [X1] + [padd(G[i], pmul(Delta[i + 1], X1, P), P) for i in range(len(G))]
    def lift(poly):  # w_j moves to field j+1; field 0 is gamma
        return {mono << BITS: cf for mono, cf in poly.items()}

    S = [padd(lift(X[i]), {mono + 1: cf for mono, cf in lift(Delta[i]).items()}, P) for i in range(r)]
    JS = pdet([[pderiv(Si, j, P) for j in range(npar + 1)] for Si in S], P)
    E, e_poly = [], True
    for i in range(r):
        Ei = {}
        for mono, cf in S[i].items():
            ex = unpack(mono, npar + 1)
            g = ex[0] + sum(d[j] * ex[j + 1] for j in range(npar)) - e[i]
            if g < 0:
                e_poly = False
                continue
            Ei[pack((g,) + ex[1:])] = cf
        E.append(Ei)
    vnames = ["v%d" % (j + 1) for j in range(r)]
    RV = Ring(vnames, P)
    stage = [from_recipe(spec["stage"]["gamma"], RV)] + [from_recipe(s, RV) for s in spec["stage"]["u"]]
    Lstage = pdet([[pderiv(q, j, P) for j in range(r)] for q in stage], P)
    T = [substitute(Ei, npar + 1, stage, P) for Ei in E]

    def to_source(poly, xshift):
        out = {}
        for mono, cf in poly.items():
            a = unpack(mono, r)
            xe = sum(m[j] * a[j] for j in range(r)) + xshift
            if xe < 0:
                return None
            out[pack((xe,) + a)] = cf
        return out

    comps = [to_source(stage[0], 1)] + [to_source(T[i], -e[i]) for i in range(r)]
    final = [comps[o] for o in spec["order"]] if all(q is not None for q in comps) else None
    return final, dict(X=X, S=S, JS=JS, E=E, e_poly=e_poly, stage=stage, Lstage=Lstage, comps=comps, RW=RW, n=n,
                        npar=npar, r=r)


def perm_parity(order):
    return -1 if sum(1 for a in range(len(order)) for b in range(a + 1, len(order)) if order[a] > order[b]) % 2 else 1


def check_map(key, spec, P, tally, tex, fps, npoints, cross):
    t0 = time.time()
    claims = spec["claims"]
    final, B = rebuild(spec, P)
    n, npar, r = B["n"], B["npar"], B["r"]
    tally(key, "det J_(gamma,w)(S) = %d gamma^%d as a polynomial identity mod p" % (spec["c"], spec["k"]),
          B["JS"] == {spec["k"]: coef(spec["c"], P)})
    tally(key, "sum m = sum e = sum d + k + 1", sum(spec["m"]) == sum(spec["e"]) == sum(spec["d"]) + spec["k"] + 1)
    tally(key, "E_i = S_i(gamma, gamma^d u) / gamma^e_i has no negative gamma exponent", B["e_poly"])
    if "base" in spec:
        base = [coef(Fraction(s), P) for s in spec["base"]]
        tally(key, "E_i vanish at the base point %s" % spec["base"], all(peval(Ei, npar + 1, base, P) == 0 for Ei in B["E"]))
        got = [[peval(pderiv(Ei, j, P), npar + 1, base, P) for j in range(npar + 1)] for Ei in B["E"][1:]]
        tally(key, "gradients of E_2..E_%d at the base point equal the paper's" % r,
              got == [[coef(g, P) for g in row] for row in spec["gradients"]])
    tally(key, "stage Jacobian determinant is the constant %s (polynomial identity mod p)" % claims["stage_det"],
          B["Lstage"] == {0: coef(Fraction(claims["stage_det"]), P)})
    sign = perm_parity(spec["order"])
    tally(key, "claimed det %s = sign %+d * c %d * det L %s" % (claims["det"], sign, spec["c"], claims["stage_det"]),
          Fraction(claims["det"]) == sign * spec["c"] * Fraction(claims["stage_det"]))
    if not tally(key, "every component is a polynomial (no negative power of x after the twist)", final is not None):
        return
    tally.say(key, "rebuilt mod p in %.1f s; term counts %s" % (time.time() - t0, [len(f) for f in final]))
    degs = [pdegree(f, n) for f in final]
    tally(key, "component degrees %s" % claims["degrees"], degs == claims["degrees"], "got %s" % degs)
    if "terms" in claims:
        stated = [(i, t) for i, t in enumerate(claims["terms"]) if t is not None]
        tally(key, "term counts stated by the paper (%s)" % ", ".join("component %d: %d" % (i + 1, t) for i, t in stated),
              all(len(final[i]) == t for i, t in stated))
    if "term_range" in claims:
        lo, hi = claims["term_range"]
        tally(key, "components 2..%d have between %d and %d terms" % (n, lo, hi), all(lo <= len(f) <= hi for f in final[1:]))
    RS = Ring(spec["source"], P)
    for label, anchor, start, stops in spec["printed"]:
        idx = int(re.findall(r"\d+", label)[-1])
        printed = from_tex(tex_display(tex, anchor, start, stops), RS)
        tally(key, "component %d equals the printed %s term by term mod p" % (idx, label), printed == final[idx - 1],
              "%d terms" % len(printed))
    for label, anchor, start, stops in spec.get("X_printed", []):
        idx = int(re.findall(r"\d+", label)[-1])
        tally(key, "sweep %s equals the paper's display mod p" % label,
              from_tex(tex_display(tex, anchor, start, stops), B["RW"]) == B["X"][idx - 1])
    claim = coef(Fraction(claims["det"]), P)
    J = [[pderiv(f, j, P) for j in range(n)] for f in final]
    if key in ("F", "G", "F4", "F5"):
        t1 = time.time()
        tally(key, "det J(%s) = %s as a polynomial identity mod p (Leibniz expansion)" % (key, claims["det"]),
              pdet(J, P) == {0: claim}, "%.1f s" % (time.time() - t1))
    rng = random.Random(97 * n + len(key))
    t1 = time.time()
    dets = []
    for _ in range(npoints):
        pt = [rng.randrange(1, P) for _ in range(n)]
        dets.append(ndet([[peval(q, n, pt, P) for q in row] for row in J], P))
    tally(key, "det J(%s) = %s at %d random points of GF(p)^%d" % (key, claims["det"], npoints, n), all(v == claim for v in dets),
          "%.1f s" % (time.time() - t1))
    if cross:
        fp = fps.get(key)
        if tally(key, "A's fingerprint for this map is present and uses p = 2^61 - 1", fp is not None and fp.get("prime") == P):
            same = all([peval(f, n, pt, P) for f in final] == vals for pt, vals in zip(fp["points"], fp["values"]))
            tally(key, "B's rebuild agrees with A's at A's %d fingerprint points, and term counts agree" % len(fp["points"]),
                  same and fp["terms"] == [len(f) for f in final])
    tally.say(key, "done in %.1f s" % (time.time() - t0))


def exact_points(key, tally):
    """Rational point checks over Q with B's own Fraction rebuild: the F and G collisions and G(0, 1/2, -1/4)."""
    colls = {"F": recipes.F_COLLISION, "G": recipes.G_COLLISION}
    if key in colls:
        final, _ = rebuild(recipes.MAPS[key], None)
        coll = colls[key]
        image = [Fraction(s) for s in coll["image"]]
        for pt in coll["points"]:
            val = [peval(f, 3, [Fraction(s) for s in pt], None) for f in final]
            tally(key, "over Q: %s(%s) = (%s)" % (key, ", ".join(pt), ", ".join(coll["image"])), val == image)
        distinct = {tuple(Fraction(s) for s in pt) for pt in coll["points"]}
        tally(key, "over Q: the %d points are pairwise distinct" % len(coll["points"]), len(distinct) == len(coll["points"]))
    if key == "G":
        pt = recipes.G_APPENDIX["point_over_011"]
        val = [peval(f, 3, [Fraction(s) for s in pt["point"]], None) for f in final]
        tally("G", "over Q: G(%s) = (%s)" % (", ".join(pt["point"]), ", ".join(pt["image"])),
              val == [Fraction(s) for s in pt["image"]])


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--maps", default="F,G,F4,F5,F6,F7")
    ap.add_argument("--points", type=int, default=3, help="random points of GF(p)^n for det J")
    ap.add_argument("--fingerprints", default=os.path.join(HERE, "results", "fingerprints.json"))
    ap.add_argument("--no-cross", action="store_true", help="skip the comparison with A's fingerprints")
    args = ap.parse_args()
    tally = Tally()
    load = "load average %.1f on %d CPUs" % (os.getloadavg()[0], os.cpu_count()) if hasattr(os, "getloadavg") else "load average unavailable"
    tally.say("env", "Python %s; standard library only; %s" % (platform.python_version(), load))
    tex = open(os.path.join(HERE, recipes.TEX), encoding="utf-8").read()
    fps = {}
    if not args.no_cross and os.path.exists(args.fingerprints):
        fps = json.load(open(args.fingerprints))
    for key in args.maps.split(","):
        tally.say(key, "=== %s ===" % recipes.MAPS[key]["title"])
        try:
            check_map(key, recipes.MAPS[key], PRIME, tally, tex, fps, args.points, not args.no_cross)
            exact_points(key, tally)
        except Exception as exc:  # a malformed recipe or display must fail the gate, not crash past the summary
            tally(key, "map could not be processed: %s: %s" % (type(exc).__name__, exc), False)
    print("SUMMARY (B)  %d passed, %d failed" % (tally.good, tally.bad))
    sys.exit(1 if tally.bad else 0)


if __name__ == "__main__":
    main()
