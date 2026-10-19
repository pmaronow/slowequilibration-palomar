# Canonical Brownian foundations provenance

[BrownianMotion](https://github.com/RemyDegenne/brownian-motion) is retained at upstream revision `0d5b6eb928e616d3b1f774ad7d233c167d9f42c9`. [KolmogorovExtension4](https://github.com/RemyDegenne/kolmogorov_extension4) is retained at upstream revision `7d76e184c3d2138a2741baf923b57e9a01b9cf25`. Original Rémy Degenne author/copyright notices remain in the source files. Both projects use Apache 2.0; their [BrownianMotion license](LICENSE.BrownianMotion) and [KolmogorovExtension4 license](LICENSE.KolmogorovExtension4) remain separate.

The retained 30-module closure of `BrownianMotion.Gaussian.BrownianMotion` is listed in [included-modules.json](included-modules.json). Unrelated upstream stochastic-integral and iterated-logarithm developments are excluded.

The sources construct the Brownian measure through Kolmogorov extension of a Gaussian projective family, then obtain continuous paths using Kolmogorov–Chentsov. The concrete process and measure have `IsBrownianReal` proofs; this property is not merely a field assumed in an abstract model.

[compatibility.patch](compatibility.patch) records the earlier Lean 4.34.1 adaptation: removal of declarations already in mathlib, explicit chaining supremum bounds, subtype/measurability inference updates, explicit Gaussian-law constructor fields, and a Polish-space import. The chaining argument keeps the triangle inequality and three supremum bounds.

The supplied provenance reports compilation on Lean 4.34.1 and transitive-axiom checks for the Brownian construction and continuous-path measurability, with only `propext`, `Classical.choice`, and `Quot.sound`. Those historical statements concern the supplied pre-port revision. They do not verify the current Lean 4.35.0-rc2 repository. Current evidence is identified in the enclosing [verification record](../../docs/VERIFICATION.md).
