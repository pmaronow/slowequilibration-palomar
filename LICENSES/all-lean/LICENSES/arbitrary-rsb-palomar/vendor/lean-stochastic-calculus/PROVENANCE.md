# Stochastic calculus provenance

Upstream: [savarin/lean-stochastic-calculus](https://github.com/savarin/lean-stochastic-calculus), revision `bde839683ba3cf1bf149355a40e9de9522babe92`. Original author: **Ezzeri Esa**. The Apache 2.0 [license](LICENSE) and source author/copyright notices are retained.

The 57-module dependency closure of `StochasticCalculus.GirsanovTheorem` is listed in [included-modules.json](included-modules.json). The unrelated upstream Black–Scholes challenge is excluded.

Upstream uses Lean/mathlib 4.35.0-rc3. The supplied version had been adapted to Lean/mathlib 4.34.1 by removing `Lean.Elab.Recall` imports and redundant `recall` signature checks. [generality.patch](generality.patch) records the additional generic-sample-space adaptation of 17 Itô-related files. It replaces inherited normed/Gaussian sample-space conditions with measurable probability-space conditions. The scalar expectation map retains the same `lpPairing` with constant-one formula, allowing use on the canonical Brownian projective-limit space.

The local-martingale interface uses localizing sequences of martingales. Quadratic variation uses limits in probability of uniform partition sums. The Girsanov theorem takes explicit Novikov, predictability, and cross-variation hypotheses. Instantiation for a concrete Parisi process is an application in the enclosing development; these generic theorem inputs do not themselves assert that application.

The supplied provenance reports successful compilation and `#print axioms` checks of the natural Itô integral, general Itô formula, predictable Girsanov theorem, and probability normalization on Lean 4.34.1. Reported dependencies used only `propext`, `Classical.choice`, and `Quot.sound`. These historical checks do not verify the present source revision. Current module/compiler work and completed checks are recorded in the enclosing [verification record](../../docs/VERIFICATION.md).
