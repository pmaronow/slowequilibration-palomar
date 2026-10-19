# Slow Equilibration and Persistent Stationary Correlations in Spherical Spin Glasses

This private repository contains the six-headline manuscript and a Palomar
submission package. The independent statements are in `Challenge.lean`, their
proofs are in `Solution.lean`, and `comparator.json` selects the advertised
claims. The [manuscript](manuscript/main.pdf) and its buildable source accompany
the formalization. A static [project page](docs/index.html) is included for
local preview; hosting is disabled.

| Manuscript result | Formal scope |
| --- | --- |
| Theorem 1.2 | Exponential-time separation from equilibrium for the uniform initial law under the strict nondegenerate one-step certificate |
| Corollary 1.3 | All four model classes, including the degree-window and support-four-through-eleven specializations |
| Theorem 1.4 | The finite-dimensional Haar comparison and all three initial-law clauses at a common exponent |
| Theorem 1.5 | All five stationary-memory conclusions for finite mixtures |
| Theorem 1.6 | The stronger plateau below `qStar`, with the stated distinction between probability rates |
| Theorem 1.7 | The actual infinite-mixture differential-operator spectrum near the dynamical threshold |

Theorem 1.2, Corollary 1.3, and the asymptotic clauses of Theorem 1.4 retain
Chen's finite-mixture Parisi formula as an explicit premise. Universal
`PressureLowerTails` is proved internally, so no Subag premise remains.
The finite-dimensional Haar inequality and Theorems 1.5–1.7 have no literature
premise. The model, certificate, threshold, summability, temperature, and other
hypotheses remain part of the exact statements.

`Challenge.lean` imports only Mathlib and defines its mathematical objects
directly. Its deliberate theorem placeholders specify the claims to compare;
they are not solution proofs. `Solution.lean` connects the independent
specification to the included physical-model proof development. `Audit.lean`
checks the advertised exports and permits only `propext`, `Classical.choice`,
and `Quot.sound` in their transitive proof dependencies.

The retained Lean files are the import closure needed by the selected proofs
and statement bridges. Build caches, old working archives, unrelated result
surfaces, and historical comparator certificates are excluded. Upstream source
attribution and required notices are retained in `NOTICE`, `LICENSES/`, and
`vendor/`. [Provenance](PROVENANCE.json) records inherited-source identities and
manuscript hashes; the [claim map](submission/claims.json) connects the six
groups to the compared declarations. Current evidence is recorded in
[verification](verification/README.md); no registry registration or acceptance
is asserted.

## Build and verify

Install Elan, Python 3.11 or later, and Linux bubblewrap 0.12.0. The project
pins Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; keep the included manifest.

```sh
lake exe cache get
lake build
```

The default build targets are `Solution` and `Audit`. For the local protected
Comparator replay, obtain the pinned official verifier outside this repository:

```sh
git clone https://github.com/PalomarRegistry/PalomarSubmission.git ../PalomarSubmission
git -C ../PalomarSubmission checkout d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44
python3 -m pip install --require-hashes --no-deps -r ../PalomarSubmission/requirements.txt
bash scripts/verify.sh ../PalomarSubmission
```

The scripts check the official source/configuration contract, compile a fresh
canonical Challenge against trusted Mathlib only, and compare the two sides
with the toolchain's bundled Lean, NanoDa, and con-ron kernels. Large temporary
exports remain outside the package. Local results are distinct from Palomar's
own intake workflow. `comparator.json` is the configuration to use for the
eventual submission at an immutable commit.

## Supporting manuscript and local page

With TeX, BibTeX, and `latexmk` installed:

```sh
cd manuscript
latexmk -pdf -interaction=nonstopmode -halt-on-error -no-shell-escape main.tex
python3 verify-thermal-example.py
```

To preview the static page, run `python3 -m http.server 8787 --bind 127.0.0.1`
from the repository root and open `http://127.0.0.1:8787/docs/`. The page uses
only local HTML and CSS. Neither a public deployment nor a registry submission
is performed by these commands.
