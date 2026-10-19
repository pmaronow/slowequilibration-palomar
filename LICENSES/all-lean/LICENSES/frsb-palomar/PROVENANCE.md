# Provenance and attribution

The formalization authors and responsible maintainers are P. M. Aronow and Patrick Lopatto. Patrick Lopatto is the manuscript author. Sol 6.1 autoformalized the original development. Subsequent Codex work prepared this repository, constructed the independent submission interface, repaired compiler compatibility, and performed automated review and verification. These roles are recorded separately in [formalization.yaml](formalization.yaml); no human mathematical review is inferred from them.

## Mathematical source and retained development

The mathematical source is [Full replica symmetry breaking in the Sherrington–Kirkpatrick model, arXiv:2607.11756v4](https://arxiv.org/abs/2607.11756v4). [results.json](results.json) identifies the exact local source by SHA-256 and preserves the claim ledger and source locations. That source differs from the public v4 TeX only in abstract line wrapping. The original source and bibliography accompany the local delivery separately; the arXiv distribution license does not supply a general open redistribution license for the manuscript.

The substantive `FRSB` development is retained. The `Paper` namespace is the supplied earlier replica-symmetry and Parisi PDE foundation. Its original source revision was not supplied as a Git commit. The reproducible source manifest identifies the prepared files; the compatibility patches describe changes from the supplied originals. Its positive-field results refer to the earlier [arXiv:2604.11921v2](https://arxiv.org/abs/2604.11921v2) paper. Conditional assembly lemmas are retained with their explicit hypotheses; they are not counted as unconditional physical conclusions.

The public-facing layout and verification interface follow [pmaronow/at-palomar](https://github.com/pmaronow/at-palomar/tree/915bca99f46bad65629ef35c8be4bf8fc962af9a), revision `915bca99f46bad65629ef35c8be4bf8fc962af9a`. Reused MIT verification code retains attribution. [compatibility/](compatibility/) records the subsequent port of the supplied Lean sources.

## Vendored proof foundations

| Source | Pinned revision | Local slice and license |
| --- | --- | --- |
| [ParisiFormula](https://github.com/qiangwu2/ParisiFormula) | `9fd12231429de72fa524b471c43f4a237553a711` | Finite-step Parisi formula; [provenance](vendor/spin-glass-foundations/PROVENANCE.json), [Apache-2.0](vendor/spin-glass-foundations/LICENSE-ParisiFormula). |
| [research_public/RSAT](https://github.com/njimaMath/research_public) | `f3b34d2071d9cde5262c6672b6ebab132d4a7b43` | Quantitative strict AT theorem and Gaussian lemmas; [Apache-2.0](vendor/spin-glass-foundations/LICENSE-RSAT). |
| [brownian-motion](https://github.com/RemyDegenne/brownian-motion) | `0d5b6eb928e616d3b1f774ad7d233c167d9f42c9` | Canonical Brownian construction; [provenance](vendor/brownian-foundations/PROVENANCE.md), [Apache-2.0](vendor/brownian-foundations/LICENSE.BrownianMotion). |
| [kolmogorov_extension4](https://github.com/RemyDegenne/kolmogorov_extension4) | `7d76e184c3d2138a2741baf923b57e9a01b9cf25` | Gaussian projective-limit construction; [Apache-2.0](vendor/brownian-foundations/LICENSE.KolmogorovExtension4). |
| [lean-stochastic-calculus](https://github.com/savarin/lean-stochastic-calculus) | `bde839683ba3cf1bf149355a40e9de9522babe92` | Selected Girsanov/Itô closure with generic sample-space adaptation; [provenance](vendor/lean-stochastic-calculus/PROVENANCE.md), [Apache-2.0](vendor/lean-stochastic-calculus/LICENSE). |
| [SpinGlass](https://github.com/or4nge19/SpinGlass) | `dc1d3820af6e443c09bd1177ec3e409cf0640d5c` | Gaussian heat/Cole–Hopf closure with namespace adaptation; [provenance](vendor/cole-hopf-foundations/PROVENANCE.json), [Apache-2.0](vendor/cole-hopf-foundations/LICENSE). |

Each slice preserves its licenses and source notices. Included-module lists and prior adaptation patches remain alongside it. Earlier adapted-source hashes describe the supplied Lean 4.34.1 version; the new module and compiler changes are separate patches. Supplied historical audit summaries are provenance, not evidence that this revision passed. Current verification is recorded in [VERIFICATION.md](VERIFICATION.md). Off-path upstream unfinished files were excluded in the supplied slices; the remaining source is audited and built locally.

The independent weak-PDE Challenge does not import these slices. Solution uses their checked source through the substantive proof development. Literature citations are not introduced as theorem axioms.

## Verification-policy sources

The preparation used requirements checked on 8 October 2026:

- [PalomarPolicy](https://github.com/PalomarRegistry/PalomarPolicy/tree/96b034cc31a72a63d4f4041911dce337a85c9a04), `96b034cc31a72a63d4f4041911dce337a85c9a04`.
- [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission/tree/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44), `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`.
- [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml/tree/99c678e569c7c4c0772db297c5ddd5e4c9b6322e), `99c678e569c7c4c0772db297c5ddd5e4c9b6322e`.

The exact v0.4 metadata schema is retained with its own [license and provenance](vendor/verification-metadata/README.md). Remote policy may change after this snapshot. Local checks do not authenticate the repository for Palomar, register a submission, or establish editorial approval.
