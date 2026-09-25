# The paper's LaTeX source

`Jacobian_CE.tex` is the LaTeX source of Shuhong Gao, *Counterexamples to the Jacobian conjecture in dimensions greater than two*, [arXiv:2608.00222v1](https://arxiv.org/abs/2608.00222v1) (July 31, 2026). It is copied unmodified from arXiv's source archive for v1, which contains only this file and a `00README.json`. The paper is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/), as the metadata of its arXiv PDF records.

SHA-256: `c644040df10323c69de0b022986ee98563f659e70a53afd4a0c74c03d55d81aa`

The gates read the printed polynomials straight from this file: gates A and L through `texparse.py`, and gate B through its own parser in `verify_modp.py`. `recipes.py` pins the checksum, so gate A fails if the file changes. Do not edit or reflow it. The repository's `.gitattributes` stops git from converting its line endings on checkout, which would also change the checksum.
