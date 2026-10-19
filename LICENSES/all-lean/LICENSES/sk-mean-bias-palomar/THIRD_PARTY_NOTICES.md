# Third-party licenses and notices

The [MIT license](LICENSE) covers original code and documentation. Third-party material retains its original license, copyright, author and adaptation notices. The full [Apache License 2.0](LICENSES/Apache-2.0.txt) is included for Apache-licensed sources. The license text was recovered byte-for-byte from the known public repositories linked below; their license files were identical. Most linked commits identify recovered license files rather than original source revisions. The supplied provenance for `ParisiFormula/GuerraToninelli.lean` separately identifies an originating source revision.

Where a preserved vendor header says its Apache-2.0 terms are described in `LICENSE`, that refers to the original vendor license, reproduced here as `LICENSES/Apache-2.0.txt`. Flattening the sources does not redirect that grant to this project's MIT license.

| Local material | Preserved attribution and license | Public reference |
| --- | --- | --- |
| `StochasticCalculus/` | Copyright (c) 2026 Ezzeri Esa; Apache-2.0; author Ezzeri Esa. | [savarin/lean-stochastic-calculus](https://github.com/savarin/lean-stochastic-calculus/blob/bde839683ba3cf1bf149355a40e9de9522babe92/LICENSE) |
| `BrownianMotion/` | Notice-bearing files attribute Rémy Degenne (2025 or 2026) and Etienne Marion (2025); Apache-2.0. | [RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion/blob/a7ad7af662044313bc80a7c0756360fb3745f931/LICENSE) |
| `KolmogorovExtension4/` | Copyright (c) 2023 Rémy Degenne; Apache-2.0; authors Rémy Degenne and Peter Pfaffelhuber. | [RemyDegenne/kolmogorov_extension4](https://github.com/RemyDegenne/kolmogorov_extension4/blob/7d76e184c3d2138a2741baf923b57e9a01b9cf25/LICENSE) |
| Notice-bearing files under `Common/` and `Lemmas/` | Copyright notices attribute Matteo Cipollina (2025 or 2026), or Rémy Degenne (2025) and Matteo Cipollina (2026); Apache-2.0. | [or4nge19/SpinGlass](https://github.com/or4nge19/SpinGlass/blob/dc1d3820af6e443c09bd1177ec3e409cf0640d5c/LICENSE) |
| `QuantitativeFollowup/External/PrekopaBasic.lean` and `PrekopaLeindler.lean` | Copyright (c) 2026 Jonathan Ho; Apache-2.0; author Jonathan Ho. Existing port notices are preserved. | The supplied source headers contain the grant; an exact originating upstream repository and revision were not identified. |
| `ParisiFormula/GuerraToninelli.lean` | Existing provenance identifies an Apache-2.0 source port and records its earlier import adaptations. | [Original source at commit f3b34d2](https://github.com/njimaMath/research_public/blob/f3b34d2071d9cde5262c6672b6ebab132d4a7b43/perceptronFixed/Lean/SpinGlass/GuerraToninelli.lean) |
| Apache-source adaptations in `FourPapersCommon/` | Existing Gaussian, mixed-model and scheme-algebra comments identify adapted Apache-2.0 sources. | Attribution and adaptation comments in the source files. |

The [source-origin manifest](provenance/source-origins.json) preserves supplied local lineage, including the `brownian-foundations`, `cole-hopf-foundations`, `lean-stochastic-calculus`, and `spin-glass-foundations` vendor roots. Those local labels do not supply an upstream URL or revision. Some original source revisions and the lineage of headerless vendor additions remain incompletely documented. No copyright owner is inferred for headerless source. The original-code MIT grant does not remove applicable Apache-2.0 obligations from derivative material.

The supplied source contained no standalone vendor license or notice files. Public tree inspections found no separate `NOTICE` file in the four initially referenced repositories at the linked license-reference commits. The additional `njimaMath/research_public` source reference supplied an [RSAT notice](LICENSES/RSAT-NOTICE.txt), retained verbatim, and an [Apache-2.0 license file](https://github.com/njimaMath/research_public/blob/f3b34d2071d9cde5262c6672b6ebab132d4a7b43/RSAT/LICENSE). The notice attributes portions of `Lemmas/SpinGlass/` to the Apache-2.0 `or4nge19/SpinGlass` project. The [public notice](https://github.com/njimaMath/research_public/blob/f3b34d2071d9cde5262c6672b6ebab132d4a7b43/RSAT/NOTICE) has SHA-256 `6df21abf9a7aa85a795aa4e198722c338183a4ad8158994cfc18517230305323`.

## Modification notices

Changed Apache-derived source files retain the per-file modification notice required by Apache-2.0 section 4(b):

```text
Modified for this distribution (2026): Lean compiler/module compatibility and
library interface adaptations. Existing source notices are retained.
```

Compiler compatibility changes may alter module modifiers, import resolution, namespaces or proof elaboration. Existing copyright, license, author and adaptation notices remain present. The modification comment does not assign a license or copyright owner to headerless material.

## External build dependencies

Mathlib and its transitive Lake dependencies are resolved by [lake-manifest.json](lake-manifest.json). Their source trees, caches, binaries and downloaded package directories are excluded from this repository's distributable source archive. Lake retrieves them from pinned upstream repositories, which retain their own license files and notices. Lean and the external verification tools likewise retain their upstream licenses; their binaries are not redistributed here.

Upstream licensing references include [Mathlib's license at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/LICENSE) and [Lean's license](https://github.com/leanprover/lean4/blob/v4.35.0-rc2/LICENSE).
