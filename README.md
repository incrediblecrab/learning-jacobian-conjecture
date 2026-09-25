# Checking Gao's counterexamples to the Jacobian conjecture

The Jacobian conjecture says that a polynomial map ℂⁿ → ℂⁿ whose Jacobian determinant is a nonzero constant, a Keller map, has a polynomial inverse; in particular it is injective. Shuhong Gao's preprint *Counterexamples to the Jacobian conjecture in dimensions greater than two* ([arXiv:2608.00222v1](https://arxiv.org/abs/2608.00222v1), July 31, 2026) treats six explicit Keller maps that are not injective, in dimensions three, four and five: Alpöge's map F and five new ones. This repository rebuilds all six from the recipes in the paper and checks what the paper says about them.

**Result.** Each rebuilt map is polynomial, has the constant Jacobian determinant the paper states, and has a fiber of several points, so each is a counterexample to the Jacobian conjecture. The rebuilt maps agree with every component the paper prints. One formula in Appendix A.2 is off by a factor of 4, a discriminant normalization that does not affect the argument. For the two three-dimensional maps, Alpöge's F and Gao's G, a Lean 4 proof accepted by the kernel shows that each is a Keller map and is not injective on ℚ³.

**Limits.** Only the six explicit maps were checked, not the paper's general construction or its general theorems. Apart from F and G in Lean, the evidence is exact computer algebra in sympy, which is as trustworthy as sympy and this code, backed by independent sampled checks. The generic fiber size, the geometric degree, was not proved for any map. [What was not checked](#what-was-not-checked) has the full list.

## The six maps

| Map | Section | n | det J | Degrees of the components | Fibers counted |
|---|---|---|---|---|---|
| F, Alpöge's map | 3.4 | 3 | −2 | 7, 6, 4 | 3 points over a random target; none over (4/27, 4/3, 1), a point of the curve 𝒞 that Theorem 3.4 says F misses |
| G | 3.5 | 3 | 2 | 4, 11, 12 | 4 over a random target; none over a target lying over the node (X, Y) = (−4, 1/2), where Theorem A.1 says the fiber is empty |
| F4 | 4.4.1 | 4 | −44/9 | 4, 11, 12, 21 | 5 over the paper's target and 5 over a random one |
| F5 | 4.4.2 | 4 | 160/29 | 3, 12, 14, 16 | 10 over the paper's target and 10 over a random one |
| F6 | 4.5.1 | 5 | −290 | 7, 38, 40, 42, 44 | 6 over a random target; 4 over the axis point (1, 0, 0, 0, 0) |
| F7 | 4.6 | 5 | 119377 | 7, 86, 89, 92, 95 | 12 over the paper's target; 7 over the axis point (1, 0, 0, 0, 0) |

Every count is the one the paper states. F4, F5 and F7 are checked at the rational targets the paper names. The generic counts of F, G and F6 are checked at a random rational target, as the paper did for G and F6; for F the paper derives them in Theorem 3.4. The random targets come from seeded generators, so every run uses the same ones.

The two three-dimensional maps also have explicit rational collisions, checked in exact arithmetic by gates A and B and in Lean:

- F(0, 0, −1/4) = F(1, −3/2, 13/2) = F(−1, 3/2, 13/2) = (−1/4, 0, 0), printed in Section 3.4.
- G(0, 1/2, −9/4) = G(2, −1/2, 3/2) = G(−2, 5/6, 13/6) = (0, 1, 0). The paper prints no explicit collision for G. This one was found by a small search for this repository, whose script is not included, and it is an instance of the paper's Theorem A.1: over a target with v₁ = 0 and v₂² ≠ 24v₃ the fiber has three points, one with x = 0 and y = v₂/2 and two with x² = 4/(v₂² − 24v₃), here x = ±2. Gate A checks that structure.

## What kind of evidence each claim has

- **Machine-checked proof** (Lean 4 kernel, gate L): F is a Keller map over every commutative ring and G over every field of characteristic zero, and neither is injective on ℚ³. The kernel checks that the proofs prove the statements. That the statements mean what they say rests on about 40 lines of definitions that a reader has to check; [lean/README.md](09-25-26-verify-gao-keller-counterexamples/lean/README.md) lists them.
- **Exact computer algebra** (sympy over ℚ, gate A), for all six maps: that each map is polynomial; the component degrees; equality with the printed components, which are all components of F, G, F4 and F5 and the first component and stated term counts of F6 and F7, whose other components the paper does not print; the Jacobian determinant, through the chain rule over the paper's construction with every factor's determinant computed symbolically, and for F, G, F4 and F5 also by expanding the determinant of the explicit polynomials; the fiber counts in the table; and, for F and G, the identities of Theorem 3.4, Theorem A.1 and Appendix A.1 and A.2, including that the six polynomials of Appendix A.1 vanish on the graph of F and form a Gröbner basis. This is a proof only up to the correctness of sympy and of this code.
- **Sampled and independent checks**: the determinant at 3 random rational points per map, in exact arithmetic (gate A); a numerical lift of every counted fiber point to a source point, at 80 significant digits, whose image matches the target to a relative residual of at most 1.41 × 10⁻⁷⁹ (gate A); and gate B, a second rebuild of all six maps modulo the prime p = 2⁶¹ − 1, in plain Python without sympy. B reads the same transcribed paper data in `recipes.py`, but shares no code with A: it parses the recipes and the LaTeX with its own parser. It confirms mod p the determinant identities that the chain-rule argument uses, for all six maps; the full determinant as a polynomial identity mod p for F, G, F4 and F5, and at 3 random points of GF(p)ⁿ for all six; and the printed components. It also checks the collisions of F and G in exact rational arithmetic and matches A's values at A's sample points. An identity mod p is strong evidence for the identity over ℚ, not a proof of it.

A fiber is counted through the paper's construction. Over a target whose component C = γx is nonzero, as at every target used here, the points of the fiber correspond one to one with the solutions of the sweep equations S(γ, w) = Y that have γ ≠ 0. An exact lexicographic Gröbner basis in shape form reduces those solutions to the roots of one polynomial R(w₁). Gate A counts the roots with γ ≠ 0, checks that they are simple, and compares R(w₁) with the paper's fiber polynomial at that target. The correspondence follows from the construction but is not itself machine-checked; the numerical lift confirms each counted point.

## Finding: a discriminant normalization in Appendix A.2

Appendix A.2 states disc_w(W) = −E/64. With the standard discriminant, the convention of the paper's own Section 2 computation disc_w(w³ − 2w² + Xw − 2Y) = −4E, the value is −E/16. The printed −E/64 is the resultant Res_w(W, ∂W/∂w), that is, the discriminant without the division by the leading coefficient lc(W) = 1/4. The neighboring Res_w(W, X − p(w)) = −E/64 is correct as printed. The argument uses only the zero set E = 0, which is the same either way. Gate A checks both values and reports the difference as a NOTE, not a failure.

## What was not checked

- The paper's general construction and its general theorems, beyond these six instances.
- The complete fiber stratifications of Theorems 3.4 and A.1, which list every fiber size; only the fibers in the table, the collisions and the identities named above were computed.
- The geometric degree of any map. A fiber of k points shows that a map is not injective. That k is also the generic count, as the paper states, is only suggested by the random targets.
- The 174-element Gröbner basis for G in Appendix A.2 was not recomputed. For F4 to F7 the paper reports that Gröbner bases were out of reach of its implementation and treats the fibers through one-variable fiber polynomials instead, which gate A does check.
- The claims that F4, F5, F6 and F7 are not equivalent to Φ × id for a lower-dimensional Keller map Φ.
- The step from ℚ to ℂ in the Lean statements, a standard argument written out in the Lean file but not formalized.
- The works of Alpöge, Gallagher and Speyer that the paper cites.

## Planted defects

A check that never fails shows nothing, so `plant_defects.py` plants 29 defects one at a time in scratch copies and runs every gate that claims to cover each. A defect counts as caught only if the gate exits nonzero and prints a FAIL line. In the last run all 40 gate runs caught their defect, and the unmodified control copy passed all three gates. The harness was itself tested once, with a driver that is not included: an edit that changes nothing, and an edit that makes gate B crash without printing a FAIL line, were both reported as NOT CAUGHT, and the harness exited 1.

The defects change a coefficient in a recipe, in a transcribed formula of the paper, in the LaTeX source and in the Lean file; change the claimed determinant, degrees, term counts, fiber sizes and collision points; move the two empty-fiber targets; edit the LaTeX without updating its checksum; tamper with A's fingerprint file; and attack the Lean gate with `sorry`, an added axiom, `native_decide`, a false determinant and a sign error in `det3`. Three of the Lean defects pass every check that reads the Lean file or the output of compiling it. A declaration added by meta code with the kernel check switched off is caught only by the kernel replay. An axiom hidden behind a macro that fakes the file's `#print axioms` output, and a look-alike `Function.Injective` defined as `False`, are caught only by the probe that reads the compiled module.

## Runtimes

Measured on September 25, 2026 on an 11-core arm64 Mac shared with other jobs, at a load average of 6 to 9.

| Run | Result | real | user |
|---|---|---|---|
| Gate A, `verify_exact.py` | 153 passed, 0 failed, 1 note | 53.3 s | 52.5 s |
| Gate B, `verify_modp.py` | 103 passed, 0 failed | 2.0 s | 2.0 s |
| Gate L, `check_lean.py` | 27 passed, 0 failed | 15.6 s | 9.2 s |
| `plant_defects.py` | 40 of 40 gate runs caught their defect | 129.4 s | 254.5 s |

F7, whose components have up to 25,518 terms, takes 51.1 s of gate A's time. Load matters: an earlier run the same day, at a load average of 22 to 28 and with the same results, took 241.6 s real and 88.6 s user for gate A, 68.9 s real for gate L and 268.2 s real for the harness; its logs were not kept. The logs of the last run are in [results/](09-25-26-verify-gao-keller-counterexamples/results/).

## How to run

Gates A and L need Python 3 with sympy (A also uses mpmath); the runs above used Python 3.14.7, sympy 1.14.0 and mpmath 1.3.0. Gate B needs only the standard library. Gate L needs [elan](https://github.com/leanprover/elan), which installs the toolchain pinned in `lean/lean-toolchain`, Lean 4.34.0, if it is missing. No Lean library is used.

```
cd 09-25-26-verify-gao-keller-counterexamples
python3 verify_exact.py    # gate A
python3 verify_modp.py     # gate B
python3 check_lean.py      # gate L
python3 plant_defects.py   # planted defects; runs A, B and L many times
```

Each gate prints one PASS or FAIL line per check and exits 0 only if every check passes. `plant_defects.py` exits 0 only if the control run is clean and every planted defect is caught. B reads the fingerprint file that A writes to `results/`, so run A first. [The folder's README](09-25-26-verify-gao-keller-counterexamples/README.md) lists the options, such as `--maps F,G` to check only some maps.

## Layout

- `2608.00222v1.pdf`: the paper.
- [`09-25-26-verify-gao-keller-counterexamples/`](09-25-26-verify-gao-keller-counterexamples/): the gates, the Lean proof, the paper's LaTeX source and the logs.

## Source and license of the paper

The paper is by Shuhong Gao and is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) (DOI [10.48550/arXiv.2608.00222](https://doi.org/10.48550/arXiv.2608.00222)). Its PDF and its LaTeX source are included unmodified. The PDF is byte-identical to the file arXiv served for v1 on September 25, 2026, and the LaTeX source comes from arXiv's source archive for v1:

- `2608.00222v1.pdf`, SHA-256 `483208235e32ae69aaf83832916451707c78aa5a4410486c860950bd3eb6860f`
- `09-25-26-verify-gao-keller-counterexamples/source/Jacobian_CE.tex`, SHA-256 `c644040df10323c69de0b022986ee98563f659e70a53afd4a0c74c03d55d81aa`

The paper's abstract credits the refutation in dimension three to Alpöge on July 19, 2026, with an infinite family by Gallagher (July 20) and a geometric explanation by Speyer (July 23). The paper carries this disclosure: "The main idea and framework are due to the author, and Claude Fable 5 assisted in the proofs and in the writing up of the paper."

## How this was made

An AI agent, GitHub Copilot CLI running Claude Opus 5.5, wrote this repository in one session on September 25, 2026. The repository's owner asked for the paper's results to be reproduced from the paper in a public repository, using globally installed libraries and downloading no tools into the repository. The agent wrote the code, the Lean proof and the READMEs, and ran every check reported here. At the time of writing no one else had reviewed them.

What did not work at first:

- The rational collisions were first attempted in Lean with plain `decide`, which failed. `decide +kernel`, which leaves the evaluation to the kernel, succeeded and adds no axiom.
- The simp lemmas for numerals on dual numbers needed `no_index` before the determinant proofs went through.
- The planted-defect harness first counted any nonzero exit as a catch, so a crash would have passed for a caught defect. It now also requires a FAIL line.
- Gate L first read the axioms from the Lean file's own `#print axioms` output, which misses two attacks: meta code in the file can add a declaration with the kernel check switched off, and a macro can fake the `#print axioms` output. The second came to light only on re-reading a formal-proof checklist. With a planted macro, the file's own output listed only the standard axioms, while the probe found the added one. The gate now replays the compiled module in the kernel and reads the axioms with a separate probe.
- The collision for G came from a search. It was matched to the paper's Theorem A.1 only afterwards.
