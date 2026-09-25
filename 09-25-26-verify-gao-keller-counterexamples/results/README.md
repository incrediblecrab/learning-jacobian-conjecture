# Logs of the last run

These files are the output of the last full run of the three gates and the harness, on September 25, 2026 from 16:49 to 16:53 EDT. The [repository README](../../README.md#runtimes) tabulates their results and runtimes. From the folder above, each script ran as

```
export PYTHONDONTWRITEBYTECODE=1
/usr/bin/time -p perl -e 'alarm shift; exec @ARGV' 3600 python3 verify_exact.py > results/verify_exact.log 2>&1
```

and likewise for `verify_modp.py`, `check_lean.py` and `plant_defects.py`, in that order, with a cap of 7200 s for the harness. No run reached its cap. `python3` was Python 3.14.7, with sympy 1.14.0 and mpmath 1.3.0.

| File | Written by | Contents |
|---|---|---|
| `verify_exact.log` | gate A | one PASS, FAIL, NOTE or INFO line per step, then a summary |
| `verify_modp.log` | gate B | the same format |
| `check_lean.log` | gate L | the same format, including the Lean version and each step's time |
| `plant_defects.log` | the harness | the control runs, one row per planted defect and gate, and a summary |
| `fingerprints.json` | gate A | the values B compares against |

Each log begins with an INFO line giving the software versions and the load average, and ends with the `real`, `user` and `sys` seconds from `/usr/bin/time -p`. The one NOTE, in `verify_exact.log`, is the discriminant normalization in Appendix A.2 that the repository README describes. No file here contains a path on the machine that produced it.

`fingerprints.json` holds, for each map, the prime p = 2⁶¹ − 1 (`prime`), three sample points of GF(p)ⁿ (`points`), the values mod p of the n components at each point (`values`), and the number of terms in each component (`terms`). B evaluates its own rebuild at A's points and compares the values and the term counts. Running A rewrites the file. Its contents are deterministic: this run wrote a file byte-identical to the previous run's.
