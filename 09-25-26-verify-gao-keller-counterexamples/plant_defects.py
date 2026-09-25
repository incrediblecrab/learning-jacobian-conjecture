#!/usr/bin/env python3
"""Plant single defects in scratch copies of this lab and confirm that every gate reports each of them.

A gate reports a defect when it exits nonzero and prints at least one FAIL line; a crash without a FAIL line does not count. A clean control copy runs first, and all three gates must exit 0 on it with no FAIL line: A (verify_exact.py), B (verify_modp.py) and L (check_lean.py). Its fingerprint file seeds the fingerprint defect.

Each defect is an exact string edit, asserted to match exactly once, to recipes.py, the LaTeX source, the Lean file, or A's fingerprint file. Three Lean defects need two or three such edits: one also adds `import Lean`, one adds a macro that fakes the file's `#print axioms` output, and one rewrites the two proofs that its look-alike `Function.Injective` would otherwise break. A defect runs only through the gates that claim to cover it: B does not certify fibers or the appendix identities, and L covers only F and G. A LaTeX edit also rewrites TEX_SHA256 in the scratch recipes.py, so that the gate must catch the changed display itself rather than the checksum. One defect leaves the checksum stale, to test that check too. Nothing is edited in place. Exit status 1 if the control fails or any gate misses its defect.
"""
import concurrent.futures
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
FILES = ["recipes.py", "texparse.py", "verify_exact.py", "verify_modp.py", "check_lean.py", "check_lean_probe.lean", "source/Jacobian_CE.tex",
         "lean/KellerCE.lean", "lean/lean-toolchain"]
TEX = "source/Jacobian_CE.tex"
LEAN = "lean/KellerCE.lean"
SIMPS = ("add_re, add_eps, sub_re, sub_eps, neg_re, neg_eps, mul_re, mul_eps, div_re, div_eps, ofNat_re, ofNat_eps, "
         "pow_zero', pow_succ'")
F_PROOF = "  simp only [jacDet, det3, deriv, F, %s]\n  grind" % SIMPS
G_THEOREM = ("set_option linter.unusedSimpArgs false in\n/-- `G` is a Keller map over every field of characteristic zero. -/\n"
             "theorem G_keller {α : Type} [Lean.Grind.Field α] [Lean.Grind.IsCharP α 0] (x y z : α) : jacDet G x y z = 2 := by\n"
             "  simp only [jacDet, det3, deriv, G, %s]\n  grind" % SIMPS)
# Meta code that adds `bogus : False`, proved by `True.intro`, with the kernel check switched off. The file still compiles and `#print axioms` stays clean; only the kernel replay can reject it.
HACK = ("open Lean Elab Command in\nset_option debug.skipKernelTC true in\n"
        "#eval show CommandElabM Unit from liftCoreM <| addDecl <|\n"
        "  .thmDecl { name := `bogus, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro }\n\n")
# A macro that turns every `#print axioms X` in the file into a printout of the clean answer, so that the file's own output hides an added axiom. Only a report read from outside the file sees it.
FAKE_PRINT = ("macro_rules\n  | `(#print axioms $id) => `(#eval IO.println (\"'\" ++ $(Lean.quote id.getId.toString) ++ "
              "\"' depends on axioms: [propext, Classical.choice, Quot.sound]\"))\n\n")
COUNTEREXAMPLE_DOC = "/-- Alpöge's `F` is a counterexample to the Jacobian conjecture in dimension three. -/"

# (defect, file, old text, new text, gates that must fail, maps to run)
DEFECTS = [
    ("F6 stage coefficient 355 -> 356", "recipes.py", "355*v1*v2", "356*v1*v2", "AB", "F6"),
    ("F7 potential G2: w1**3 -> 2*w1**3", "recipes.py", '("G2", "w2**2 + w2 + w1*w3 + w1**3")',
     '("G2", "w2**2 + w2 + w1*w3 + 2*w1**3")', "AB", "F7"),
    ("printed F_{4,2}: 22/9 -> 23/9 in the LaTeX", TEX, "\\tfrac{22}{9}x^6yz^2t^2", "\\tfrac{23}{9}x^6yz^2t^2", "AB", "F4"),
    ("printed F_{6,1}: 355 -> 356 in the LaTeX", TEX, "355x^4yz_1", "356x^4yz_1", "AB", "F6"),
    ("printed F_{4,2} edited, checksum left stale", TEX + ":stale", "\\tfrac{22}{9}x^6yz^2t^2", "\\tfrac{23}{9}x^6yz^2t^2",
     "A", "F4"),
    ("F5 det claim 160/29 -> 161/29", "recipes.py", '"det": "160/29"', '"det": "161/29"', "AB", "F5"),
    ("F6 degree claim 44 -> 45", "recipes.py", '"degrees": [7, 38, 40, 42, 44]', '"degrees": [7, 38, 40, 42, 45]', "AB", "F6"),
    ("F6 term-count claim 904 -> 905", "recipes.py", "507, 904]", "507, 905]", "AB", "F6"),
    ("F collision image -1/4 -> -1/5", "recipes.py", '"image": ["-1/4", "0", "0"]', '"image": ["-1/5", "0", "0"]', "AB", "F"),
    ("F5 witness fiber 10 -> 9 points", "recipes.py", '"-1/3", "1"], "points": 10}', '"-1/3", "1"], "points": 9}', "A", "F5"),
    ("F7 witness fiber 12 -> 11 points", "recipes.py", '"-1", "3"], "points": 12}', '"-1", "3"], "points": 11}', "A", "F7"),
    ("G tangency quartic 2Y -> 3Y", "recipes.py", '- X*w + 2*Y"', '- X*w + 3*Y"', "A", "G"),
    ("F fiber polynomial: -2*Y2 -> -3*Y2", "recipes.py", '"paper_R": "w1**3 - 2*w1**2 + Y1*w1 - 2*Y2"',
     '"paper_R": "w1**3 - 2*w1**2 + Y1*w1 - 3*Y2"', "A", "F"),
    ("F6 axis polynomial R_0: 2*w1**3 - 1 -> + 1", "recipes.py", '"paper_R0": "w1**2*(w1 - 1)*(2*w1**3 - 1)"',
     '"paper_R0": "w1**2*(w1 - 1)*(2*w1**3 + 1)"', "A", "F6"),
    ("F6 gradient of E_2 at the base point: 2 -> 3", "recipes.py", "[[-16, -17, 3, 2],", "[[-16, -17, 3, 3],", "AB", "F6"),
    ("Thm 3.4 c_3: 16*v1 -> 17*v1", "recipes.py", "+ 16*v1 + v2**3*v3", "+ 17*v1 + v2**3*v3", "A", "F"),
    ("F empty-fiber target moved off the cusp curve", "recipes.py", '"paper_target": ["4/27", "4/3", "1"]',
     '"paper_target": ["4/27", "4/3", "2"]', "A", "F"),
    ("G empty-fiber target moved off the node", "recipes.py", '"Y": ["-4", "1/2"], "points": 0', '"Y": ["-4", "1/3"], "points": 0',
     "A", "G"),
    ("A's F4 fingerprint value +1", "fingerprints", "F4", None, "B", "F4"),
    ("G collision point 13/6 -> 13/5 in recipes.py", "recipes.py", '["-2", "5/6", "13/6"]', '["-2", "5/6", "13/5"]', "ABL", "G"),
    ("Lean: F_keller proved by sorry", LEAN, F_PROOF, "  sorry", "L", ""),
    ("Lean: axiom cheat : False proves G_keller", LEAN, G_THEOREM,
     "axiom cheat : False\n\n" + G_THEOREM.split(":= by\n")[0] + ":= by\n  exact cheat.elim", "L", ""),
    ("Lean: kernel check off, G_keller from False", LEAN,
     [("/-!\n# Two Keller maps", "import Lean\n/-!\n# Two Keller maps"),
      (G_THEOREM, HACK + G_THEOREM.split(":= by\n")[0] + ":= by\n  exact bogus.elim")], None, "L", ""),
    ("Lean: axiom cheat, #print axioms faked", LEAN,
     [(G_THEOREM, "axiom cheat : False\n\n" + G_THEOREM.split(":= by\n")[0] + ":= by\n  exact cheat.elim"),
      ("end KellerCE\n\n#print axioms", "end KellerCE\n\n" + FAKE_PRINT + "#print axioms")], None, "L", ""),
    ("Lean: Function.Injective shadowed by := False", LEAN,
     [(COUNTEREXAMPLE_DOC, "def Function.Injective {α β : Type} (_ : α → β) : Prop := False\n\n" + COUNTEREXAMPLE_DOC),
      ("⟨fun x y z => F_keller x y z, F_not_injective⟩", "⟨fun x y z => F_keller x y z, fun h => h⟩"),
      ("⟨fun x y z => G_keller x y z, G_not_injective⟩", "⟨fun x y z => G_keller x y z, fun h => h⟩")], None, "L", ""),
    ("Lean: false claim det J(F) = -3", LEAN, "jacDet F x y z = -2 := by", "jacDet F x y z = -3 := by", "L", ""),
    ("Lean: native_decide in G_collision", LEAN, "(13/6) = (0, 1, 0) := by\n  decide +kernel",
     "(13/6) = (0, 1, 0) := by\n  native_decide", "L", ""),
    ("Lean: G coefficient 43/2 -> 45/2", LEAN, "43/2*x^2*y^4", "45/2*x^2*y^4", "L", ""),
    ("Lean: det3 cofactor sign - v.1 -> + v.1", LEAN, "- v.1 * (u.2.1", "+ v.1 * (u.2.1", "L", ""),
]


def copy_lab(dst):
    for rel in FILES:
        os.makedirs(os.path.dirname(os.path.join(dst, rel)) or dst, exist_ok=True)
        shutil.copy2(os.path.join(HERE, rel), os.path.join(dst, rel))
    os.makedirs(os.path.join(dst, "results"), exist_ok=True)


def run_gate(lab, gate, maps, cross):
    if gate == "L":
        cmd = [sys.executable, "check_lean.py"]
    else:
        script = "verify_exact.py" if gate == "A" else "verify_modp.py"
        cmd = [sys.executable, script, "--maps", maps, "--fingerprints", os.path.join(lab, "results", "fingerprints.json")]
        if gate == "B" and not cross:
            cmd.append("--no-cross")
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    t0 = time.time()
    proc = subprocess.run(cmd, cwd=lab, env=env, capture_output=True, text=True, timeout=3600)
    lines = (proc.stdout + proc.stderr).splitlines()
    fails = [ln for ln in lines if ln.startswith("FAIL")]
    first = fails[0] if fails else (lines[-1] if lines else "")
    return proc.returncode, len(fails), first[:160], time.time() - t0


def plant(lab, fname, old, new, clean_fps):
    if fname == "fingerprints":
        fps = json.load(open(clean_fps))
        fps[old]["values"][0][1] = (fps[old]["values"][0][1] + 1) % fps[old]["prime"]
        json.dump(fps, open(os.path.join(lab, "results", "fingerprints.json"), "w"))
        return
    stale = fname.endswith(":stale")
    fname = fname.split(":")[0]
    path = os.path.join(lab, fname)
    text = open(path, encoding="utf-8").read()
    for o, n in (old if isinstance(old, list) else [(old, new)]):
        if text.count(o) != 1:
            raise ValueError("defect text %r occurs %d times in %s, expected exactly once" % (o, text.count(o), fname))
        text = text.replace(o, n)
    open(path, "w", encoding="utf-8").write(text)
    if fname == TEX and not stale:
        rp = os.path.join(lab, "recipes.py")
        rec = open(rp, encoding="utf-8").read()
        sha = hashlib.sha256(open(path, "rb").read()).hexdigest()
        rec, count = re.subn(r'TEX_SHA256 = "[0-9a-f]{64}"', 'TEX_SHA256 = "%s"' % sha, rec)
        assert count == 1
        open(rp, "w", encoding="utf-8").write(rec)


def case(defect, clean_fps):
    name, fname, old, new, gates, maps = defect
    lab = tempfile.mkdtemp(prefix="plant-")
    try:
        copy_lab(lab)
        plant(lab, fname, old, new, clean_fps)
        return [(name, g) + run_gate(lab, g, maps, cross=(fname == "fingerprints")) for g in gates]
    finally:
        shutil.rmtree(lab, ignore_errors=True)


def load_average():
    return "load average %.1f on %d CPUs" % (os.getloadavg()[0], os.cpu_count()) if hasattr(os, "getloadavg") else "load average unavailable"


def main():
    t0 = time.time()
    workers = max(1, min(4, (os.cpu_count() or 2) - 1))
    print("INFO     Python %s; %s at the start; defect cases run %d at a time\n" % (sys.version.split()[0], load_average(), workers), flush=True)
    control = tempfile.mkdtemp(prefix="plant-control-")
    control_ok, missed = True, 0
    try:
        copy_lab(control)
        for gate in "ABL":
            code, nfail, first, secs = run_gate(control, gate, "F,G,F4,F5,F6,F7", cross=True)
            ok = code == 0 and nfail == 0
            control_ok &= ok
            print("%-8s control (no defect), %s: exit %d, %d FAIL lines, %.0f s%s"
                  % (gate, "F and G in Lean" if gate == "L" else "all six maps", code, nfail, secs,
                     "" if ok else "  <-- CONTROL FAILED: " + first), flush=True)
        clean_fps = os.path.join(tempfile.mkdtemp(prefix="plant-fps-"), "fingerprints.json")
        shutil.copy2(os.path.join(control, "results", "fingerprints.json"), clean_fps)
    finally:
        shutil.rmtree(control, ignore_errors=True)
    print("\n%-5s %-46s %-5s %5s %6s  %s" % ("gate", "planted defect", "exit", "FAILs", "secs", "first FAIL line"))
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
        for rows in pool.map(lambda d: case(d, clean_fps), DEFECTS):
            for name, gate, code, nfail, first, secs in rows:
                caught = code != 0 and nfail > 0
                missed += not caught
                print("%-5s %-46s %-5d %5d %6.0f  %s%s" % (gate, name, code, nfail, secs, first,
                                                            "" if caught else "  <-- NOT CAUGHT"), flush=True)
    shutil.rmtree(os.path.dirname(clean_fps), ignore_errors=True)
    total = sum(len(d[4]) for d in DEFECTS)
    print("\nSUMMARY  %d of %d planted-defect gate runs reported the defect (nonzero exit and a FAIL line); control run %s; %.0f s; %s at the end"
          % (total - missed, total, "clean" if control_ok else "FAILED", time.time() - t0, load_average()))
    sys.exit(0 if control_ok and not missed else 1)


if __name__ == "__main__":
    main()
