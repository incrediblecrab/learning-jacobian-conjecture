# The Lean proof for F and G

`KellerCE.lean` proves in Lean 4, with no library beyond Lean core, that Alpöge's map F and Gao's map G are Keller maps and are not injective on ℚ³. `lean-toolchain` pins Lean 4.34.0, which elan installs on first use if it is missing.

| Theorem | Statement |
|---|---|
| `F_keller` | det J(F) = −2 at every point, over every commutative ring (Lean core's `Lean.Grind.CommRing`) |
| `G_keller` | det J(G) = 2 at every point, over every field of characteristic zero (`Lean.Grind.Field` with `Lean.Grind.IsCharP α 0`) |
| `F_collision` | F(0, 0, −1/4) = F(1, −3/2, 13/2) = F(−1, 3/2, 13/2) = (−1/4, 0, 0) over ℚ |
| `G_collision` | G(0, 1/2, −9/4) = G(2, −1/2, 3/2) = G(−2, 5/6, 13/6) = (0, 1, 0) over ℚ |
| `F_not_injective`, `G_not_injective` | the map is not injective on ℚ³ |
| `F_counterexample`, `G_counterexample` | both together: det J is the constant at every point of ℚ³, and the map is not injective on ℚ³ |

Every theorem depends only on Lean's three standard axioms, `propext`, `Classical.choice` and `Quot.sound`. The determinants are proved by `simp` and then `grind`'s commutative-ring normalizer, the collisions by `decide +kernel`.

## What the proof establishes

The kernel accepts the proofs, so the statements follow from the definitions. Whether the statements say what the paper says depends on the definitions, which are not proved and have to be read: the dual numbers `Dual` and their arithmetic, `Dual.pow`, `deriv`, `det3`, `jacDet`, `F` and `G`, about 40 lines. The docstring of `KellerCE.lean` explains why each is right. `check_lean.py` compares `F` and `G` with the components printed in the paper's LaTeX source, as polynomials over ℚ, and compares the constants and points in the statements with `recipes.py`. Nothing checks `jacDet` against the textbook definition of the Jacobian determinant except a reader.

The conjecture is about ℂⁿ, and Lean core has no complex numbers. The step from ℚ to ℂ is written out in the docstring and not formalized: two distinct rational points with one image are also two distinct complex points with one image, and a polynomial identity with rational coefficients that holds on ℚ³ holds on ℂ³.

## How it is checked

`python3 ../check_lean.py` runs these steps and prints PASS or FAIL for each:

1. `lean KellerCE.lean` must exit 0, with no error and no `sorry`.
2. `leanchecker`, which ships with the toolchain, replays every declaration of the compiled module in the kernel, in a separate process. This catches a declaration that meta code added with the kernel check switched off.
3. `../check_lean_probe.lean`, run in another process, loads the compiled module without its environment extensions, so that no table the file computed while compiling is reused. It prints each theorem's axioms and the constants of this file that its statement mentions. This catches an axiom even when the file fakes its own `#print axioms` output, and it catches a look-alike, such as a `Function.Injective` defined in the file.
4. The comparisons with the paper and with `recipes.py` described above.

The `#print axioms` lines at the end of `KellerCE.lean` are for a reader in an editor; the gate does not use them. `check_lean.py` sets `LEAN_SYSROOT` to the pinned toolchain when it runs `leanchecker` and the probe from a temporary directory. Without it they would use elan's default toolchain, which can be a different Lean version that cannot read the compiled module.

In the logged run, at a load average of 5.0 on 11 CPUs, compiling took 6.6 s, the kernel replay 2.8 s and the probe 5.6 s.

Compiling a Lean file runs code on the host with the user's permissions, and nothing here isolates it. `KellerCE.lean` has no imports and no meta code: no `#eval`, `macro`, `syntax`, `elab` or `notation`. Read any changed version before compiling it.
