#!/usr/bin/env python3
"""Gate for the Lean proof in lean/KellerCE.lean: compile it, audit its axioms, and tie its statements to the paper.

Checks, each printed as PASS or FAIL:
  - `lean KellerCE.lean` exits 0 with no error and no `sorry`, using the toolchain pinned in lean/lean-toolchain;
  - leanchecker, the kernel replay shipped with the toolchain, re-checks every declaration of the compiled module in a separate process. The axiom audit alone does not see a declaration that meta code added with kernel checking switched off; the replay rejects it;
  - check_lean_probe.lean, elaborated without KellerCE and run in a separate process, loads the compiled module without its environment extensions and reports, for each of the six theorems, (a) the axioms it depends on, which must be among propext, Classical.choice and Quot.sound (so no sorryAx, no added axiom, and none of the axioms that native_decide introduces: Lean.ofReduceBool, or in Lean 4.34 an auxiliary axiom named like G_collision._native.native_decide.ax_1_1), and (b) the KellerCE constants its statement mentions, which must be exactly jacDet, F or G, and Dual with its arithmetic instances, so that a name such as Function.Injective in a statement is Lean core's and not a look-alike defined in the file. The `#print axioms` lines in KellerCE.lean are not used, because code in the file could fake its own output;
  - F and G as defined in Lean equal, as polynomials over Q, the components printed in the paper's LaTeX source;
  - the determinant constants and the collision points in the theorem statements equal those in recipes.py.
Exit status 1 if any check fails. Needs `lean` on PATH (elan), or at ~/.elan/bin/lean.
"""
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time
from fractions import Fraction

import sympy

import recipes
import texparse

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_DIR = os.path.join(HERE, "lean")
LEAN_FILE = "KellerCE.lean"
PROBE = "check_lean_probe.lean"
THEOREMS = ["F_keller", "G_keller", "F_collision", "G_collision", "F_counterexample", "G_counterexample"]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# The KellerCE constants each statement may mention: the definitions a reader has to trust, as listed in KellerCE.lean's docstring. `jacDet F` evaluates F on dual numbers, so Dual and its instances appear too; the instance names are the ones Lean 4.34 generates.
DUAL_F = ["Dual", "instAddDual", "instSubDual", "instMulDualOfAdd", "instHPowDualNatOfAddOfMulOfOfNat", "instOfNatDual"]
DUAL_G = DUAL_F + ["instNegDual", "instDivDualOfSubOfMul"]
MENTIONS = {"F_keller": ["jacDet", "F"] + DUAL_F, "G_keller": ["jacDet", "G"] + DUAL_G, "F_collision": ["F"], "G_collision": ["G"],
            "F_counterexample": ["jacDet", "F"] + DUAL_F, "G_counterexample": ["jacDet", "G"] + DUAL_G}
COLLISIONS = {"F": recipes.F_COLLISION, "G": recipes.G_COLLISION}


class Tally:
    def __init__(self):
        self.passed = self.failed = 0

    def __call__(self, label, ok, detail=""):
        self.passed += bool(ok)
        self.failed += not ok
        print("%s  L   %s%s" % ("PASS" if ok else "FAIL", label, "" if ok or not detail else "  [%s]" % detail), flush=True)
        return ok


def find_lean():
    return shutil.which("lean") or next((p for p in [os.path.expanduser("~/.elan/bin/lean")] if os.path.exists(p)), None)


def lean_components(src, name):
    """The three components of `def <name> ... := (c1, c2, c3)` in the Lean source, as sympy expressions in x, y, z."""
    m = re.search(r"^def %s \{α : Type\}[^\n]*? \(x y z : α\) : α × α × α :=\n(.*?)\n\n" % name, src, re.S | re.M)
    if not m:
        raise ValueError("definition of %s not found in the expected form" % name)
    body = m.group(1).strip()
    if not (body.startswith("(") and body.endswith(")")):
        raise ValueError("body of %s is not a parenthesized triple" % name)
    parts, depth, cur = [], 0, ""
    for ch in body[1:-1]:
        depth += (ch == "(") - (ch == ")")
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    if len(parts) != 3:
        raise ValueError("%s has %d components, expected 3" % (name, len(parts)))
    x, y, z = sympy.symbols("x y z")
    return [sympy.expand(sympy.sympify(p.replace("^", "**"), locals=dict(x=x, y=y, z=z))) for p in parts]


def paper_components(tex, key):
    x, y, z = sympy.symbols("x y z")
    env = dict(x=x, y=y, z=z)
    const = lambda q: sympy.Rational(q.numerator, q.denominator)
    return [sympy.expand(texparse.parse(texparse.extract(tex, anchor, start, stops), const, lambda nm: env[nm]))
            for (_, anchor, start, stops) in recipes.MAPS[key]["printed"]]


def lean_args(s):
    """Split `(0 : Rat) 0 (-1/4)` into three rationals."""
    toks = re.findall(r"\([^()]*\)|\S+", s)
    return [Fraction(t.strip("()").replace(": Rat", "").strip()) for t in toks]


def lean_collision(src, key):
    m = re.search(r"^theorem %s_collision :\n(.*?) := by" % key, src, re.S | re.M)
    if not m:
        raise ValueError("%s_collision not found" % key)
    rows = re.findall(r"%s (.*?) = \(([^()]*)\)" % key, m.group(1))
    return [(lean_args(args), [Fraction(c.strip()) for c in img.split(",")]) for args, img in rows]


def lean_witness(src, key):
    m = re.search(r"^theorem %s_not_injective .*?\n.*?@h \(([^()]*)\) \(([^()]*)\)" % key, src, re.S | re.M)
    if not m:
        raise ValueError("%s_not_injective witness pair not found" % key)
    return [[Fraction(c.strip()) for c in grp.split(",")] for grp in m.groups()]


def main():
    t0 = time.time()
    tally = Tally()
    src = open(os.path.join(LEAN_DIR, LEAN_FILE), encoding="utf-8").read()
    tex = open(os.path.join(HERE, recipes.TEX), encoding="utf-8").read()

    load = "load average %.1f on %d CPUs" % (os.getloadavg()[0], os.cpu_count()) if hasattr(os, "getloadavg") else "load average unavailable"
    print("INFO  L   Python %s, sympy %s (only to compare Lean's F and G with the paper); %s" % (platform.python_version(), sympy.__version__, load), flush=True)
    lean = find_lean()
    if tally("lean is available (elan)", lean is not None, "no `lean` on PATH or at ~/.elan/bin/lean"):
        toolchain = open(os.path.join(LEAN_DIR, "lean-toolchain")).read().strip()
        ver = subprocess.run([lean, "--version"], cwd=LEAN_DIR, capture_output=True, text=True, timeout=600)
        prefix = subprocess.run([lean, "--print-prefix"], cwd=LEAN_DIR, capture_output=True, text=True, timeout=600).stdout.strip()
        print("INFO  L   toolchain pinned in lean/lean-toolchain: %s; %s" % (toolchain, ver.stdout.strip()), flush=True)
        with tempfile.TemporaryDirectory(prefix="kellerce-build-") as build:
            t1 = time.time()
            proc = subprocess.run([lean, "-o", os.path.join(build, "KellerCE.olean"), LEAN_FILE], cwd=LEAN_DIR,
                                  capture_output=True, text=True, timeout=1800)
            out = proc.stdout + proc.stderr
            print("INFO  L   lean %s: exit %d in %.1f s" % (LEAN_FILE, proc.returncode, time.time() - t1), flush=True)
            errors = [ln for ln in out.splitlines() if ": error" in ln]
            tally("lean %s exits 0 with no errors" % LEAN_FILE, proc.returncode == 0 and not errors,
                  "exit %d; %s" % (proc.returncode, errors[0][:150] if errors else "no error line"))
            tally("no `sorry` anywhere in the output", "sorry" not in out)
            env = dict(os.environ, LEAN_SYSROOT=prefix, LEAN_PATH=build)
            checker = os.path.join(prefix, "bin", "leanchecker")
            if tally("leanchecker ships with the pinned toolchain", os.path.isfile(checker), "not in the toolchain's bin directory"):
                t1 = time.time()
                rep = subprocess.run([checker, "KellerCE"], cwd=build, env=env, capture_output=True, text=True, timeout=1800)
                msg = " ".join((rep.stdout + rep.stderr).split())
                print("INFO  L   leanchecker KellerCE: exit %d in %.1f s" % (rep.returncode, time.time() - t1), flush=True)
                tally("kernel replay: leanchecker, in a separate process, re-checks every declaration of KellerCE in the kernel and accepts them all",
                      rep.returncode == 0 and "problem" not in msg, msg[:200] or "no output")
            t1 = time.time()
            probe = subprocess.run([os.path.join(prefix, "bin", "lean"), "--run", os.path.join(HERE, PROBE)] + THEOREMS, cwd=build, env=env,
                                   capture_output=True, text=True, timeout=1800)
            print("INFO  L   lean --run %s: exit %d in %.1f s" % (PROBE, probe.returncode, time.time() - t1), flush=True)
            report = {(kind, thm): set(rest.split()) for kind, thm, rest in re.findall(r"^(AXIOMS|MENTIONS) (\w+):(.*)$", probe.stdout, re.M)}
            problem = " ".join((probe.stderr or probe.stdout).split())[:150] or "no output"
            for thm in THEOREMS:
                axioms = report.get(("AXIOMS", thm))
                tally("%s: axioms %s are among propext, Classical.choice, Quot.sound (read by the probe from the compiled module)"
                      % (thm, sorted(axioms) if axioms else "none"), axioms is not None and axioms <= STANDARD_AXIOMS,
                      "not reported: %s" % problem if axioms is None else "extra: %s" % sorted(axioms - STANDARD_AXIOMS))
            for thm in THEOREMS:
                mentions, want = report.get(("MENTIONS", thm)), {"KellerCE." + c for c in MENTIONS[thm]}
                tally("%s: the KellerCE constants its statement mentions are exactly %s" % (thm, ", ".join(MENTIONS[thm])), mentions == want,
                      "not reported: %s" % problem if mentions is None else "unexpected: %s; missing: %s" % (sorted(mentions - want), sorted(want - mentions)))

    for key in "FG":
        try:
            lc, pc = lean_components(src, key), paper_components(tex, key)
            same = [sympy.expand(a - b) == 0 for a, b in zip(lc, pc)]
            tally("Lean's %s equals the paper's printed %s, component by component, over Q" % (key, key), all(same),
                  "components differing: %s" % [i + 1 for i, s in enumerate(same) if not s])
        except (ValueError, sympy.SympifyError) as exc:
            tally("Lean's %s equals the paper's printed %s" % (key, key), False, str(exc))
        det = recipes.MAPS[key]["claims"]["det"]
        m = re.search(r"^theorem %s_keller .*?: jacDet %s x y z = (\S+) := by" % (key, key), src, re.M)
        tally("%s_keller states det J(%s) = %s, the paper's constant" % (key, key, det),
              bool(m) and Fraction(m.group(1)) == Fraction(det), "stated %s" % (m.group(1) if m else "nothing"))
        stmt = "(∀ x y z : Rat, jacDet %s x y z = %s) ∧ ¬ Function.Injective (fun p : Rat × Rat × Rat => %s p.1 p.2.1 p.2.2)" % (key, det, key)
        m = re.search(r"^theorem %s_counterexample :\n\s*(.*?) :=" % key, src, re.S | re.M)
        tally("%s_counterexample states: det J(%s) = %s on Q^3, and %s is not injective on Q^3" % (key, key, det, key),
              bool(m) and " ".join(m.group(1).split()) == stmt, "stated %r" % (m.group(1)[:120] if m else None))
        coll = COLLISIONS[key]
        want = [[Fraction(s) for s in pt] for pt in coll["points"]]
        image = [Fraction(s) for s in coll["image"]]
        try:
            rows = lean_collision(src, key)
            tally("%s_collision states the %d points and the image of recipes.py" % (key, len(want)),
                  [r[0] for r in rows] == want and all(r[1] == image for r in rows), "stated %s" % rows)
            tally("%s_not_injective uses the first two of those points" % key, lean_witness(src, key) == want[:2])
        except (ValueError, ZeroDivisionError) as exc:
            tally("%s_collision matches recipes.py" % key, False, str(exc))

    print("SUMMARY  %d passed, %d failed; %.0f s" % (tally.passed, tally.failed, time.time() - t0))
    sys.exit(1 if tally.failed else 0)


if __name__ == "__main__":
    main()
