# Vendored Gaussian heat-flow concavity proof

This directory contains the smallest import closure for
`OAI.GaussianPropeller.EhrhardSmooth.qheat_concave` from
[`openai/math`](https://github.com/openai/math), commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a` (upstream path
`lean/OAI/Probability/GaussianPropeller`).

The twelve Lean modules are distributed under the upstream Apache License,
Version 2.0, reproduced in [LICENSE](LICENSE). They are adapted to the
repository's Lean module-system conventions by adding license and source
headers, `module`, `public import`, and `@[expose] public section`; the
upstream proof bodies are unchanged and contain no `sorry` or additional
axioms. The original upstream configuration
uses Lean 4.34.1, mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and `autoImplicit = false`.

Only this import closure is vendored; the other dependencies and results of
the upstream project are not required.
