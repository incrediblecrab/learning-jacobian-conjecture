#!/usr/bin/env python3
"""Implementation A: exact rational verification of Gao's six Keller maps (arXiv:2608.00222v1) with sympy.

Every map is rebuilt from its recipe in recipes.py (sweep -> scalings -> stage -> monomials -> twist) over QQ and checked against the paper: polynomiality, degrees, term counts, the printed components parsed straight from the LaTeX source, the Jacobian determinant, and exact fiber certificates. Exit status 1 if any check fails.
"""
import argparse
import ast
import json
import os
import platform
import random
import sys
import time
from fractions import Fraction

import mpmath
import sympy
from sympy import QQ, Poly, Rational, groebner, symbols
from sympy.polys.groebnertools import is_groebner, is_reduced
from sympy.polys.orderings import lex
from sympy.polys.rings import ring

import recipes
import texparse

HERE = os.path.dirname(os.path.abspath(__file__))
P61 = 2**61 - 1


class Report:
    def __init__(self):
        self.failed = 0
        self.passed = 0
        self.notes = 0

    def check(self, key, what, ok, detail=""):
        ok = bool(ok)
        self.passed += ok
        self.failed += not ok
        print("%s  %-3s %s%s" % ("PASS" if ok else "FAIL", key, what, "  [%s]" % detail if detail else ""), flush=True)
        return ok

    def info(self, key, text):
        print("INFO  %-3s %s" % (key, text), flush=True)

    def note(self, key, text):
        """A discrepancy with the paper's wording whose true replacement is asserted by an adjacent check."""
        self.notes += 1
        print("NOTE  %-3s %s" % (key, text), flush=True)


def Q(s):
    return Fraction(s)


def ev(s, env, R):
    """Evaluate a recipe string over the sympy ring R; integer '/' is exact, names resolve through env."""
    lift = lambda a: R(QQ(a.numerator, a.denominator)) if isinstance(a, Fraction) else a

    def go(n):
        if isinstance(n, ast.Expression):
            return go(n.body)
        if isinstance(n, ast.Constant) and type(n.value) is int:
            return Fraction(n.value)
        if isinstance(n, ast.Name):
            return env[n.id]
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub):
            return -go(n.operand)
        if isinstance(n, ast.BinOp):
            a, b = go(n.left), go(n.right)
            if isinstance(n.op, ast.Pow):
                return a ** int(b)
            if isinstance(n.op, ast.Div):
                return a / b if isinstance(a, Fraction) else a * lift(1 / b)
            if isinstance(a, Fraction) and isinstance(b, Fraction):
                a2, b2 = a, b
            else:
                a2, b2 = lift(a), lift(b)
            if isinstance(n.op, ast.Add):
                return a2 + b2
            if isinstance(n.op, ast.Sub):
                return a2 - b2
            if isinstance(n.op, ast.Mult):
                return a2 * b2
        raise ValueError("unsupported syntax in %r" % s)

    return lift(go(ast.parse(s, mode="eval")))


def det_sym(M, R):
    """Laplace expansion; fine for the small symbolic matrices used here."""
    if len(M) == 1:
        return M[0][0]
    tot = R.zero
    for j, a in enumerate(M[0]):
        if a:
            minor = [row[:j] + row[j + 1:] for row in M[1:]]
            tot += (-a if j % 2 else a) * det_sym(minor, R)
    return tot


def det_frac(M):
    M = [list(r) for r in M]
    n, det = len(M), Fraction(1)
    for col in range(n):
        piv = next((r for r in range(col, n) if M[r][col] != 0), None)
        if piv is None:
            return Fraction(0)
        if piv != col:
            M[col], M[piv] = M[piv], M[col]
            det = -det
        det *= M[col][col]
        for r in range(col + 1, n):
            f = M[r][col] / M[col][col]
            if f:
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return det


def perm_sign(p):
    p, s = list(p), 1
    for i in range(len(p)):
        while p[i] != i:
            j = p[i]
            p[i], p[j] = p[j], p[i]
            s = -s
    return s


def compose(p, images, Rt):
    """p(images) for p in any sympy ring, images in ring Rt (power caching)."""
    cache = [[Rt.one] for _ in images]
    out = Rt.zero
    for mon, cf in p.terms():
        t = Rt(cf)
        for j, ej in enumerate(mon):
            if ej:
                while len(cache[j]) <= ej:
                    cache[j].append(cache[j][-1] * images[j])
                t = t * cache[j][ej]
        out += t
    return out


def compose_grouped(E, gimg, uimgs, Rt):
    """E(gamma, u) with gamma -> gimg, u -> uimgs; groups terms by u-monomial so gamma-powers enter linearly."""
    groups = {}
    for mon, cf in E.terms():
        groups.setdefault(mon[1:], []).append((mon[0], cf))
    gp, upow, out = [Rt.one], [[Rt.one] for _ in uimgs], Rt.zero
    for a, lst in groups.items():
        while len(gp) <= max(b for b, _ in lst):
            gp.append(gp[-1] * gimg)
        q = Rt.zero
        for b, cf in lst:
            q += gp[b].mul_ground(cf)
        for j, aj in enumerate(a):
            if aj:
                while len(upow[j]) <= aj:
                    upow[j].append(upow[j][-1] * uimgs[j])
                q = q * upow[j][aj]
        out += q
    return out


def to_frac(cf):
    return Fraction(int(cf.numerator), int(cf.denominator))


def eval_frac(p, pt):
    pows = [[Fraction(1)] for _ in pt]
    tot = Fraction(0)
    for mon, cf in p.terms():
        t = to_frac(cf)
        for j, ej in enumerate(mon):
            if ej:
                while len(pows[j]) <= ej:
                    pows[j].append(pows[j][-1] * pt[j])
                t *= pows[j][ej]
        tot += t
    return tot


def eval_modp(p, pt, P=P61):
    tot = 0
    for mon, cf in p.terms():
        t = int(cf.numerator) * pow(int(cf.denominator), -1, P) % P
        for j, ej in enumerate(mon):
            if ej:
                t = t * pow(pt[j], ej, P) % P
        tot = (tot + t) % P
    return tot


def eval_mp(p, pt):
    """Numeric value and the sum of absolute term values (for a relative residual)."""
    pows = [[mpmath.mpc(1)] for _ in pt]
    tot, mag = mpmath.mpc(0), mpmath.mpf(0)
    for mon, cf in p.terms():
        t = mpmath.mpf(int(cf.numerator)) / int(cf.denominator)
        for j, ej in enumerate(mon):
            if ej:
                while len(pows[j]) <= ej:
                    pows[j].append(pows[j][-1] * pt[j])
                t *= pows[j][ej]
        tot += t
        mag += abs(t)
    return tot, mag


def total_degree(p):
    return max(sum(mon) for mon in p.monoms())


def fingerprint_points(n, count=3):
    rng = random.Random(20260731 + n)
    return [[rng.randrange(1, P61) for _ in range(n)] for _ in range(count)]


# ----------------------------------------------------------------------------------------------------------------
def build(key, spec, rep, tex):
    """Rebuild one map from its recipe; return a dict of everything later checks need."""
    wn, (c, k, d, e, m) = spec["params"], (spec[x] for x in "ckdem")
    nw = len(wn)
    n = nw + 2
    Rs, *sg = ring(",".join(["g"] + wn), QQ, lex)
    gam, W = sg[0], sg[1:]
    env = dict(zip(wn, W))
    for name, s in spec.get("defs", []):
        env[name] = ev(s, env, Rs)
    Delta = [ev(s, env, Rs) for s in spec["Delta"]]
    if "potentials" in spec:
        Gs = [env[nm] for nm in spec["potentials"]]
        X1 = -det_sym([[g.diff(w) for w in W] for g in Gs], Rs) * Rs(QQ(1, c))
        X = [X1] + [Gs[i] + Delta[i + 1] * X1 for i in range(nw)]
        rep.info(key, "sweep X from potentials: X_1 = -det J(G)/c, X_(i+1) = G_(i+1) + Delta_(i+1) X_1; degrees %s"
                 % [total_degree(x) for x in X])
    else:
        X = [ev(s, env, Rs) for s in spec["X"]]
    const_s = lambda q: Rs(QQ(q.numerator, q.denominator))
    for (label, anchor, start, stops), Xi in zip(spec.get("X_printed", []), X):
        Pi = texparse.parse(texparse.extract(tex, anchor, start, stops), const_s, lambda nm: env[nm])
        rep.check(key, "sweep %s equals the paper's display" % label, Pi == Xi)

    S = [X[i] + gam * Delta[i] for i in range(n - 1)]
    dS = det_sym([[s.diff(v) for v in sg] for s in S], Rs)
    rep.check(key, "det J_(gamma,w)(S) = %d*gamma^%d, i.e. det J(F0) = %d*gamma^%d (symbolic)" % (c, k, c, k + 1),
              dS == c * gam**k, "got %s" % dS.as_expr())

    wt = lambda mon: sum(dj * aj for dj, aj in zip(d, mon[1:]))
    rep.check(key, "discrete data: wt(X_i) >= e_i, 1 + wt(Delta_i) >= e_i, sum m = sum e = sum d + k + 1",
              all(wt(mon) >= e[i] for i in range(n - 1) for mon in X[i].monoms())
              and all(1 + wt(mon) >= e[i] for i in range(n - 1) for mon in Delta[i].monoms())
              and sum(m) == sum(e) == sum(d) + k + 1, "sum m=%d, sum e=%d, sum d+k+1=%d" % (sum(m), sum(e), sum(d) + k + 1))

    Ru, *ug = ring(",".join(["g"] + ["u%d" % (j + 1) for j in range(nw)]), QQ, lex)
    E, neg = [], 0
    for i in range(n - 1):
        dd = {}
        for mon, cf in S[i].terms():
            ge = mon[0] + wt(mon) - e[i]
            neg += ge < 0
            dd[(max(ge, 0),) + mon[1:]] = cf
        E.append(Ru.from_dict(dd))
    rep.check(key, "E_i = S_i(gamma, gamma^d u)/gamma^e_i is a polynomial in (gamma, u)", neg == 0)

    if "base" in spec:
        base = [Q(s) for s in spec["base"]]
        rep.check(key, "base point %s: E_i(base) = 0 for all i" % spec["base"], all(eval_frac(Ei, base) == 0 for Ei in E))
        grads = [[int(eval_frac(Ei.diff(v), base)) for v in ug] for Ei in E[1:]]
        rep.check(key, "gradients of E_2, E_3, E_4 at the base point match the paper", grads == spec["gradients"], str(grads))

    vn = ["v%d" % (j + 1) for j in range(n - 1)]
    Rv, *vg = ring(",".join(vn), QQ, lex)
    venv = dict(zip(vn, vg))
    stage = [ev(spec["stage"]["gamma"], venv, Rv)] + [ev(s, venv, Rv) for s in spec["stage"]["u"]]
    detL = det_sym([[s.diff(v) for v in vg] for s in stage], Rv)
    claimL = Q(spec["claims"]["stage_det"])
    rep.check(key, "stage Jacobian determinant is the constant %s (symbolic)" % spec["claims"]["stage_det"],
              detL == Rv(QQ(claimL.numerator, claimL.denominator)), "got %s" % detL.as_expr())
    inv = stage_inverse(key, stage, Rv, vg, Ru, ug, rep)

    Rx, *xg = ring(",".join(spec["source"]), QQ, lex)
    t0 = time.time()
    sweep_comps = [Rx.from_dict({(sum(mj * aj for mj, aj in zip(m, mon)) + 1,) + mon: cf for mon, cf in stage[0].terms()})]
    bad = 0
    for i in range(n - 1):
        T = compose_grouped(E[i], stage[0], stage[1:], Rv)
        dd = {}
        for mon, cf in T.terms():
            xd = sum(mj * aj for mj, aj in zip(m, mon))
            if xd < e[i]:
                bad += 1
                continue
            dd[(xd - e[i],) + mon] = cf
        sweep_comps.append(Rx.from_dict(dd))
    rep.check(key, "polynomial map: x^e_i divides E_i(stage(v)) for every i (exact)", bad == 0,
              "%d monomials of low x-degree" % bad)
    comps = [sweep_comps[j] for j in spec["order"]]
    rep.info(key, "built in %.1f s; term counts %s" % (time.time() - t0, [len(p) for p in comps]))

    cl = spec["claims"]
    degs = [total_degree(p) for p in comps]
    rep.check(key, "component degrees %s" % cl["degrees"], degs == cl["degrees"], "got %s" % degs)
    if "terms" in cl:
        got = [len(p) for p in comps]
        stated = ", ".join("component %d: %d" % (i + 1, t) for i, t in enumerate(cl["terms"]) if t is not None)
        rep.check(key, "term counts stated by the paper (%s)" % stated,
                  all(t is None or t == g for t, g in zip(cl["terms"], got)), "got %s" % got)
    if "term_range" in cl:
        lo, hi = cl["term_range"]
        got = [len(p) for p in comps[1:]]
        rep.check(key, "components 2..%d have between %d and %d terms" % (n, lo, hi), all(lo <= g <= hi for g in got), "got %s" % got)

    xenv = dict(zip(spec["source"], xg))
    const_x = lambda q: Rx(QQ(q.numerator, q.denominator))
    for (label, anchor, start, stops) in spec["printed"]:
        idx = int(label.rstrip("}").split(",")[-1] if "," in label else label.split("_")[1]) - 1
        Pp = texparse.parse(texparse.extract(tex, anchor, start, stops), const_x, lambda nm: xenv[nm])
        diff = comps[idx] - Pp
        rep.check(key, "component %d equals the paper's printed %s (%d terms)" % (idx + 1, label, len(Pp)), not diff,
                   "%d differing terms" % len(diff))

    sign = perm_sign(spec["order"])
    chain = sign * c * claimL
    rep.check(key, "chain factorization x^(sum m) * detL * gamma^(sum d) * c gamma^(k+1) * (gamma x)^(-sum e) = %s"
              % cl["det"], chain == Q(cl["det"]), "sign %+d * c %d * detL %s = %s" % (sign, c, claimL, chain))
    return dict(Rs=Rs, gam=gam, W=W, X=X, Delta=Delta, S=S, E=E, Ru=Ru, ug=ug, Rv=Rv, vg=vg, stage=stage, inv=inv,
                Rx=Rx, xg=xg, comps=comps, sweep_comps=sweep_comps, n=n)


def stage_inverse(key, stage, Rv, vg, Ru, ug, rep):
    """Lemma 4.1: if every correction vector lies in span{col_j : j not in J}, the stage has a polynomial inverse. Build that inverse explicitly and verify both compositions are the identity."""
    N = len(stage)
    theta0 = [Fraction(0)] * N
    L = [[Fraction(0)] * N for _ in range(N)]
    corr = {}
    for r, s in enumerate(stage):
        for mon, cf in s.terms():
            deg = sum(mon)
            if deg == 0:
                theta0[r] = to_frac(cf)
            elif deg == 1:
                L[r][mon.index(1)] = to_frac(cf)
            else:
                corr.setdefault(mon, [Fraction(0)] * N)[r] = to_frac(cf)
    Lm = sympy.Matrix(N, N, lambda i, j: Rational(L[i][j].numerator, L[i][j].denominator))
    Li = Lm.inv()
    Jset = sorted({j for mon in corr for j, a in enumerate(mon) if a})
    rv = {mon: [Fraction(str(x)) for x in Li * sympy.Matrix([Rational(q.numerator, q.denominator) for q in vec])]
          for mon, vec in corr.items()}
    span_ok = all(r[j] == 0 for r in rv.values() for j in Jset)
    rep.check(key, "stage: correction vectors lie in the span of the columns outside J=%s (Lemma 4.1)" % [j + 1 for j in Jset], span_ok)
    shifted = [ug[r] - Ru(QQ(theta0[r].numerator, theta0[r].denominator)) for r in range(N)]
    z = []
    for i in range(N):
        acc = Ru.zero
        for j in range(N):
            q = Fraction(str(Li[i, j]))
            if q:
                acc += shifted[j] * Ru(QQ(q.numerator, q.denominator))
        z.append(acc)
    inv = []
    for j in range(N):
        p = z[j]
        if j not in Jset:
            for mon, r in rv.items():
                if r[j]:
                    t = Ru(QQ(r[j].numerator, r[j].denominator))
                    for l, a in enumerate(mon):
                        if a:
                            t = t * z[l] ** a
                    p = p - t
        inv.append(p)
    ok1 = all(compose(stage[r], inv, Ru) == ug[r] for r in range(N))
    ok2 = all(compose(inv[j], stage, Rv) == vg[j] for j in range(N))
    rep.check(key, "stage is a polynomial automorphism: explicit inverse, both compositions = identity (symbolic)", ok1 and ok2)
    return inv


# ----------------------------------------------------------------------------------------------------------------
def det_checks(key, spec, B, rep, direct, npoints):
    comps, xg = B["comps"], B["xg"]
    claim = Q(spec["claims"]["det"])
    t0 = time.time()
    Jp = [[f.diff(v) for v in xg] for f in comps]
    if direct:
        dJ = det_sym(Jp, B["Rx"])
        rep.check(key, "det J(%s) = %s by full symbolic expansion of the explicit polynomials" % (key, spec["claims"]["det"]),
                  dJ == B["Rx"](QQ(claim.numerator, claim.denominator)), "%.1f s" % (time.time() - t0))
    rng = random.Random(7 + len(key))
    t0 = time.time()
    vals = []
    for _ in range(npoints):
        pt = [Fraction(rng.randint(-10**6, 10**6), rng.randint(1, 10**3)) for _ in xg]
        vals.append(det_frac([[eval_frac(p, pt) for p in row] for row in Jp]))
    rep.check(key, "det J(%s) = %s at %d random rational points (exact arithmetic)" % (key, spec["claims"]["det"], npoints),
              all(v == claim for v in vals), "%.1f s" % (time.time() - t0))


def to_expr_poly(p, syms):
    """Sympy ring element (over gamma, w) -> sympy expression in the given symbols, gamma dropped (must be absent)."""
    return p.as_expr(*syms)


def fiber_checks(key, spec, B, rep, lift):
    """Fiber over a target with C0 != 0 <-> solutions (gamma, w) of S(gamma, w) = Y with gamma != 0, Y_i = t_i C0^e_i. Eliminate gamma via S_1 (Delta_1 is a nonzero constant), then certify the rest by an exact lex Groebner basis."""
    fib = spec["fiber"]
    nw, e, n = len(spec["params"]), spec["e"], B["n"]
    gsym = symbols("g")
    wsyms = symbols(" ".join(spec["params"]))
    wsyms = wsyms if isinstance(wsyms, tuple) else (wsyms,)
    Xe = [x.as_expr(gsym, *wsyms) for x in B["X"]]
    De = [dl.as_expr(gsym, *wsyms) for dl in B["Delta"]]
    assert De[0].is_number and De[0] != 0
    rng = random.Random(1000 + len(key))
    for tg in fib["targets"]:
        if "Y" in tg:
            C0, Y = Fraction(1), [Q(s) for s in tg["Y"]]
            ft = [C0] + Y
        else:
            if "random" in tg:
                paper_t = [Fraction(rng.randint(-40, 40) or 1, rng.randint(1, 9)) for _ in range(n)]
            else:
                paper_t = [Q(s) for s in tg["paper_target"]]
            ft = [None] * n
            for p_idx, s_idx in enumerate(spec["order"]):
                ft[s_idx] = paper_t[p_idx]
            C0 = ft[0]
            Y = [ft[i + 1] * C0 ** e[i] for i in range(n - 1)]
        Ys = [Rational(y.numerator, y.denominator) for y in Y]
        gam_w = (Ys[0] - Xe[0]) / De[0]
        P = [sympy.expand(Xe[i] + gam_w * De[i] - Ys[i]) for i in range(1, n - 1)]
        w1 = wsyms[0]
        if nw == 1:
            R, phis = Poly(P[0], w1), {}
            shape = True
        else:
            G = groebner(P, *reversed(wsyms), order="lex", domain=QQ)
            gl = list(G.exprs)
            R = Poly(gl[-1], w1)
            shape = len(gl) == nw and R.free_symbols_in_domain == set() and all(
                Poly(g, *reversed(wsyms)).monoms()[0] == tuple(1 if s == ws else 0 for s in reversed(wsyms))
                and (g - ws).free_symbols <= {w1}
                for g, ws in zip(gl[:-1], reversed(wsyms[1:])))
            phis = {ws: sympy.expand(ws - g) for g, ws in zip(gl[:-1], reversed(wsyms[1:]))}
        gam1 = Poly(sympy.expand(gam_w.subs(phis)), w1)
        Rsq = Poly(sympy.sqf_part(R.as_expr()), w1)
        h = sympy.gcd(Rsq, gam1.rem(R))
        good = Rsq.quo(h)
        count = good.degree()
        simple = sympy.gcd(good, R.diff(w1)).degree() == 0
        rep.check(key, "fiber over %s: Groebner basis in shape form, R(w1) of degree %d, %d roots with gamma != 0, all simple"
                  % (tg["name"], R.degree(), count),
                  shape and count == tg["points"] and simple, "expected %d points" % tg["points"])
        if "paper_R0" in tg:
            R0 = Poly(sympy.sympify(tg["paper_R0"], locals={"w1": w1}), w1)
            rep.check(key, "axis: R_0 equals the paper's factored form up to a constant", R.monic() == R0.monic())
        pr = paper_R(fib, w1, Ys)
        if pr is not None:
            rep.check(key, "  R(w1) equals the paper's fiber polynomial at this target, up to a constant factor",
                      R.monic() == pr.monic())
        if lift and count:
            lift_check(key, spec, B, rep, good, phis, gam_w, wsyms, C0, ft, tg["name"])


def paper_R(fib, w1, Ys):
    loc = {"w1": w1}
    loc.update({"Y%d" % (i + 1): y for i, y in enumerate(Ys)})
    if "paper_R" in fib:
        for name, s in fib.get("paper_R_defs", []):
            loc[name] = sympy.sympify(s, locals=loc)
        return Poly(sympy.expand(sympy.sympify(fib["paper_R"], locals=loc)), w1)
    if "paper_R_tex" in fib:
        label, anchor, start, stops = fib["paper_R_tex"]
        tex = open(os.path.join(HERE, recipes.TEX)).read()
        return Poly(sympy.expand(texparse.parse(texparse.extract(tex, anchor, start, stops),
                                                lambda q: Rational(q.numerator, q.denominator), lambda nm: loc[nm])), w1)
    return None


def lift_check(key, spec, B, rep, good, phis, gam_w, wsyms, C0, ft, name):
    """Numerically lift every root back to the source through the explicit stage inverse and evaluate the explicit polynomial components (mpmath, 80 digits): an independent sanity check of the bijection."""
    mpmath.mp.dps = 80
    roots = mpmath.polyroots([mpmath.mpf(int(c.p)) / int(c.q) for c in good.all_coeffs()], maxsteps=400, extraprec=400)
    worst, pts = mpmath.mpf(0), []
    d, m = spec["d"], spec["m"]
    for r in roots:
        wv = [r] + [mpmath.mpmathify(complex(0)) for _ in wsyms[1:]]
        for j, ws in enumerate(wsyms[1:], start=1):
            ph = phis[ws]
            wv[j] = sympy.lambdify(wsyms[0], ph, "mpmath")(r)
        g = sympy.lambdify(wsyms, gam_w, "mpmath")(*wv)
        x = (mpmath.mpf(C0.numerator) / C0.denominator) / g
        u = [wv[j] / g ** d[j] for j in range(len(wv))]
        sv = [g] + u
        vv = [eval_mp(p, sv)[0] for p in B["inv"]]
        src = [mpmath.mpmathify(x)] + [vv[j] / x ** m[j] for j in range(len(vv))]
        pts.append(src)
        for p_idx, s_idx in enumerate(spec["order"]):
            val, mag = eval_mp(B["comps"][p_idx], src)
            target = ft[s_idx]
            worst = max(worst, abs(val - (mpmath.mpf(target.numerator) / target.denominator)) / max(1, mag))
    distinct = all(max(abs(a - b) for a, b in zip(pts[i], pts[j])) > mpmath.mpf(10) ** -20
                   for i in range(len(pts)) for j in range(i))
    rep.check(key, "  lifted %d roots to distinct source points; max relative residual |%s(p) - target| = %s"
              % (len(pts), key, mpmath.nstr(worst, 3)), distinct and worst < mpmath.mpf(10) ** -40)


# ----------------------------------------------------------------------------------------------------------------
def collision_checks(key, coll, comps, rep):
    """Every listed rational point maps to the listed image, exactly, and the points are pairwise distinct."""
    image = [Q(s) for s in coll["image"]]
    for pt in coll["points"]:
        val = [eval_frac(p, [Q(s) for s in pt]) for p in comps]
        rep.check(key, "%s(%s) = (%s) over Q" % (key, ", ".join(pt), ", ".join(coll["image"])), val == image,
                  "got (%s)" % ", ".join(str(v) for v in val))
    pts = [tuple(Q(s) for s in pt) for pt in coll["points"]]
    rep.check(key, "these %d points are pairwise distinct, so %s is not injective" % (len(pts), key), len(set(pts)) == len(pts))


def extras_F(B, rep, tex):
    Rx, (x, y, z) = B["Rx"], B["xg"]
    f = B["comps"]
    collision_checks("F", recipes.F_COLLISION, f, rep)
    v1, v2, v3, X, Y, xs = symbols("v1 v2 v3 X Y x")
    loc = dict(v1=v1, v2=v2, v3=v3, X=X, Y=Y)
    c3, a2, Ecur = (sympy.sympify(recipes.F_THM34[s], locals=loc) for s in ("c3", "a2", "E"))
    ws = symbols("w")
    rep.check("F", "Sec. 2: disc_w(w^3 - 2w^2 + Xw - 2Y) = -4E(X,Y) (standard discriminant)",
              sympy.expand(sympy.discriminant(ws**3 - 2 * ws**2 + X * ws - 2 * Y, ws) + 4 * Ecur) == 0)
    sig = [sympy.sympify(s, locals=loc) for s in recipes.F_THM34["sigma"]]
    Rh, *hg = ring("z,y,x,v1,v2,v3", QQ, lex)
    henv = dict(zip(["z", "y", "x", "v1", "v2", "v3"], hg))
    H = [texparse.parse(texparse.extract(tex, *spec[1:]), lambda q: Rh(QQ(q.numerator, q.denominator)), lambda nm: henv[nm])
         for spec in recipes.F_GB]
    h1 = H[0].as_expr(*symbols("z y x v1 v2 v3"))
    rep.check("F", "Thm 3.4: h_1 = c_3 x^3 + (4 - 3 v2 v3) x - 2 v3 and a_2 = dc_3/dv_1",
              sympy.expand(h1 - (c3 * xs**3 + (4 - 3 * v2 * v3) * xs - 2 * v3)) == 0 and sympy.expand(sympy.diff(c3, v1) - a2) == 0)
    rep.check("F", "Thm 3.4(1): disc_x(h_1) = -c_3 a_2^2 and a_2^2 - 4(4 - 3 v2 v3)^3 = 108 v3^2 c_3",
              sympy.expand(sympy.discriminant(h1, xs) + c3 * a2**2) == 0
              and sympy.expand(a2**2 - 4 * (4 - 3 * v2 * v3)**3 - 108 * v3**2 * c3) == 0)
    rep.check("F", "Thm 3.4(2): v3^2 c_3 = E(sigma(v))", sympy.expand(v3**2 * c3 - Ecur.subs({X: sig[0], Y: sig[1]})) == 0)
    img = [z, y, x] + list(f)
    rep.check("F", "App. A.1: each h_i vanishes on the graph, h_i(x,y,z,F) = 0", all(not compose(h, img, Rx) for h in H))
    fz = [compose(p, [henv["x"], henv["y"], henv["z"]], Rh) for p in f]
    rep.check("F", "App. A.1: each f_i - v_i reduces to 0 modulo {h_1..h_6}",
              all(not (fz[i] - henv["v%d" % (i + 1)]).rem(H) for i in range(3)))
    rep.check("F", "App. A.1: {h_1..h_6} is a Groebner basis (all 15 S-polynomials reduce to 0), lex z>y>x>v1>v2>v3",
              is_groebner(H, Rh))
    lcs = [int(h.LC) for h in H]
    rep.check("F", "App. A.1: leading coefficients 27,54,6,24,4,8 and the monic basis is reduced",
              lcs == [27, 54, 6, 24, 4, 8] and is_reduced([h.monic() for h in H], Rh), str(lcs))


def extras_G(B, rep):
    w, X, Y, v1, v2, v3 = symbols("w X Y v1 v2 v3")
    loc = dict(w=w, X=X, Y=Y)
    Wq, p, Ec = (sympy.sympify(recipes.G_APPENDIX[s], locals=loc) for s in ("W", "p", "E"))
    rep.check("G", "App. A.2: Res_w(W, X - p(w)) = -E/64", sympy.expand(sympy.resultant(Wq, X - p, w) + Ec / 64) == 0)
    disc_std = sympy.cancel(sympy.expand(sympy.discriminant(Wq, w)) / Ec)
    res_wd = sympy.cancel(sympy.expand(sympy.resultant(Wq, sympy.diff(Wq, w), w)) / Ec)
    rep.check("G", "App. A.2: standard disc_w(W) = -E/16 and Res_w(W, dW/dw) = -E/64 (lc(W) = 1/4)",
              disc_std == Rational(-1, 16) and res_wd == Rational(-1, 64), "disc/E = %s, Res(W,W')/E = %s" % (disc_std, res_wd))
    rep.note("G", "App. A.2 prints disc_w(W) = -E/64. With the standard discriminant, the convention of the paper's own "
                  "disc_w(w^3-2w^2+Xw-2Y) = -4E, it is -E/16; -E/64 is Res_w(W, dW/dw), i.e. no division by lc(W) = 1/4. "
                  "The zero locus E = 0, which is what the argument uses, is unaffected.")
    nX, nY = (Rational(s) for s in recipes.G_APPENDIX["node"])
    rep.check("G", "App. A.2: at the node (X,Y) = (-4, 1/2), W = (w^2 - 4w - 2)^2 / 4",
              sympy.expand(Wq.subs({X: nX, Y: nY}) - sympy.sympify(recipes.G_APPENDIX["node_square"], locals=loc)) == 0)
    pt = recipes.G_APPENDIX["point_over_011"]
    val = [eval_frac(q, [Q(s) for s in pt["point"]]) for q in B["comps"]]
    rep.check("G", "App. A.2: G(%s) = (%s)" % (", ".join(pt["point"]), ", ".join(pt["image"])), val == [Q(s) for s in pt["image"]])
    collision_checks("G", recipes.G_COLLISION, B["comps"], rep)
    img = [Q(s) for s in recipes.G_COLLISION["image"]]
    pts = [tuple(Q(s) for s in pt) for pt in recipes.G_COLLISION["points"]]
    axis = [p for p in pts if p[0] == 0]
    off = [p for p in pts if p[0] != 0]
    rep.check("G", "Thm A.1, case v_1 = 0: the collision is the point (0, v_2/2, z*) on x = 0 and two points with gamma = 2 - 4xy - x^2 z = 0 and x^2 = 4/(v_2^2 - 24 v_3)",
              img[0] == 0 and len(axis) == 1 and axis[0][1] == img[1] / 2 and len(off) == 2
              and all(2 - 4 * a * b - a * a * c == 0 and a * a * (img[1] ** 2 - 24 * img[2]) == 4 for a, b, c in off))
    gam = (X - p) / 2
    xs, ys, zs = v1 / gam, (w - gam) / v1, gam * (6 * gam - 4 * w - gam**2) / v1**2
    sub = {X: v1 * v2, Y: v1**2 * v3}
    Wv = Poly(sympy.expand(Wq.subs(sub)), w)
    ok = True
    for q, target in zip(B["comps"], (v1, v2, v3)):
        expr = sympy.together((q.as_expr(*symbols("x y z")).subs({symbols("x"): xs, symbols("y"): ys, symbols("z"): zs}) - target).subs(sub))
        num, _ = sympy.fraction(expr)
        ok &= Poly(sympy.expand(num), w).rem(Wv).is_zero
    rep.check("G", "Thm A.1: x = v1/gamma, y = (w-gamma)/v1, z = gamma(6gamma-4w-gamma^2)/v1^2 give G = v modulo W (symbolic)", ok)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--maps", default="F,G,F4,F5,F6,F7")
    ap.add_argument("--points", type=int, default=3, help="random rational points for the exact det J evaluation")
    ap.add_argument("--no-lift", action="store_true", help="skip the numeric lifting of fibers to the source")
    ap.add_argument("--no-extras", action="store_true", help="skip Thm 3.4 / App. A checks for F and G")
    ap.add_argument("--fingerprints", default=os.path.join(HERE, "results", "fingerprints.json"))
    args = ap.parse_args()
    rep = Report()
    load = "load average %.1f on %d CPUs" % (os.getloadavg()[0], os.cpu_count()) if hasattr(os, "getloadavg") else "load average unavailable"
    rep.info("env", "Python %s, sympy %s, mpmath %s; %s" % (platform.python_version(), sympy.__version__, mpmath.__version__, load))
    texpath = os.path.join(HERE, recipes.TEX)
    tex = open(texpath).read()
    import hashlib
    sha = hashlib.sha256(open(texpath, "rb").read()).hexdigest()
    rep.check("src", "LaTeX source sha256 %s... matches recipes.TEX_SHA256" % sha[:12], sha == recipes.TEX_SHA256)
    fps = json.load(open(args.fingerprints)) if os.path.exists(args.fingerprints) else {}
    for key in args.maps.split(","):
        spec = recipes.MAPS[key]
        t0 = time.time()
        rep.info(key, "=== %s ===" % spec["title"])
        B = build(key, spec, rep, tex)
        det_checks(key, spec, B, rep, direct=key in ("F", "G", "F4", "F5"), npoints=args.points)
        fiber_checks(key, spec, B, rep, lift=not args.no_lift)
        if not args.no_extras and key == "F":
            extras_F(B, rep, tex)
        if not args.no_extras and key == "G":
            extras_G(B, rep)
        pts = fingerprint_points(B["n"])
        fps[key] = {"prime": P61, "points": pts, "values": [[eval_modp(p, pt) for p in B["comps"]] for pt in pts],
                    "terms": [len(p) for p in B["comps"]]}
        rep.info(key, "done in %.1f s" % (time.time() - t0))
    with open(args.fingerprints, "w") as fh:
        json.dump(fps, fh, indent=1, sort_keys=True)
    print("SUMMARY  %d passed, %d failed, %d notes on the paper's text" % (rep.passed, rep.failed, rep.notes))
    sys.exit(1 if rep.failed else 0)


if __name__ == "__main__":
    main()
