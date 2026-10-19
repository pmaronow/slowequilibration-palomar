# License mapping

Original repository code and documentation are licensed under [MIT](../LICENSE), copyright © 2026 P. M. Aronow and Patrick Lopatto. This includes the Challenge/Solution interface, original proof developments (`DepthPaper`, `GeneralDepthPaper`, `FourPapersCommon`, `Paper`, `FRSB`, `OverlapPaper`, `PositiveFieldPaper`, and `QuantitativePaper`), build configuration, verification tools, and project documentation.

Vendored source licenses and copyright/author notices are preserved. The [per-file inventory](LICENSES.json) lists every retained vendored file, with the upstream repository/revision and applicable license for each Lean module.

| Retained source | Lean modules | License |
|---|---:|---|
| `vendor/brownian-foundations/BrownianMotion` | 27 | [Apache 2.0](../vendor/brownian-foundations/LICENSE.BrownianMotion) |
| `vendor/brownian-foundations/KolmogorovExtension4` | 3 | [Apache 2.0](../vendor/brownian-foundations/LICENSE.KolmogorovExtension4) |
| `vendor/lean-stochastic-calculus/StochasticCalculus` | 57 | [Apache 2.0](../vendor/lean-stochastic-calculus/LICENSE) |
| `vendor/cole-hopf-foundations/Common` | 15 | [Apache 2.0](../vendor/cole-hopf-foundations/LICENSE) |
| `vendor/spin-glass-foundations` — ParisiFormula source | 303 | [Apache 2.0](../vendor/spin-glass-foundations/LICENSE-ParisiFormula) |
| `vendor/spin-glass-foundations` — RSAT source | 56 | [Apache 2.0](../vendor/spin-glass-foundations/LICENSE-RSAT) |

The 461 vendored Lean modules remain under their respective Apache licenses, including their adaptations. Vendored provenance documents, compatibility patches, and accompanying notices remain with those dependencies. Package-manager downloads such as mathlib retain their upstream licenses; caches and downloaded dependency trees are excluded from the source distribution. The root MIT license does not replace a vendored license.
