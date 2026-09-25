# The gates, the Lean proof and the logs

Everything that checks Gao's six Keller maps lives in this folder. The [repository README](../README.md) states what was found and what was not checked.

| File | Role |
|---|---|
| `recipes.py` | The paper's data, transcribed once: each map's recipe, the claimed constants, degrees, term counts and fibers, and where each printed display sits in the LaTeX source. Every gate reads it, and it pins the SHA-256 of the LaTeX source. One entry, `G_COLLISION`, is this repository's, not the paper's. |
| `verify_exact.py` | Gate A: rebuilds the six maps over ℚ with sympy and checks them exactly. Writes `results/fingerprints.json`. |
| `verify_modp.py` | Gate B: rebuilds the maps mod 2⁶¹ − 1 with the standard library only, sharing no code with A, and compares its values with A's fingerprints. |
| `texparse.py` | Reads polynomial displays from the LaTeX source, for A and L. B has its own parser. |
| `check_lean.py` | Gate L: compiles `lean/KellerCE.lean`, replays it in the kernel, runs the probe, and compares the Lean definitions and statements with the paper and `recipes.py`. |
| `check_lean_probe.lean` | Run by L in a separate process: loads the compiled module and prints each theorem's axioms and the constants its statement mentions. |
| `plant_defects.py` | Plants 29 defects, one at a time in scratch copies, and confirms that every gate covering a defect reports it. |
| [`lean/`](lean/) | The Lean 4 proof for F and G. |
| [`source/`](source/) | The paper's LaTeX source, unmodified. |
| [`results/`](results/) | The logs of the last run and A's fingerprint file. |

## Running

Run the scripts from this folder. Gates A and L need Python 3 with sympy, and A also needs mpmath; gate B needs only Python 3. Gate L needs [elan](https://github.com/leanprover/elan).

```
python3 verify_exact.py      # gate A, 1 to 4 minutes, most of it on F7
python3 verify_modp.py       # gate B, seconds; reads A's fingerprints, so run A first
python3 check_lean.py        # gate L, 15 s to about a minute
python3 plant_defects.py     # the harness, 2 to 5 minutes; runs A, B and L many times
```

A and B take `--maps` with any comma-separated subset of `F,G,F4,F5,F6,F7`, and `--points N` for the number of random points at which the determinant is evaluated, 3 by default. A also takes `--no-lift`, to skip the numerical lift of fiber points, and `--no-extras`, to skip the Theorem 3.4 and Appendix A checks for F and G. B takes `--no-cross`, to skip the comparison with A's fingerprints. Running A rewrites `results/fingerprints.json`.
