-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSParisiMeasure
public import SlowEquilibration.SphericalParisiBound

/-!
# Conditional spherical Parisi endpoint

Wei-Kuo Chen, *The Aizenman–Sims–Starr scheme and Parisi formula for mixed
p-spin spherical models*, Electronic Journal of Probability **18** (2013),
paper 94, Theorem 1, arXiv:1204.5115v1, proves the limiting pressure for an
ordered iid Gaussian tensor Hamiltonian on the radius-`sqrt N` sphere with
normalized surface measure. The theorem allows odd degrees and degree one.

`Chen2013FiniteParisi` below is the finite, degree-at-least-two specialization
needed for the repository's `FiniteMixture`. Its covariance coefficients are
the squares of Chen's tensor amplitudes. The Crisanti–Sommers value is the
repository's already defined minimum over actual admissible probability
measures. This proposition is an explicit *hypothesis* of downstream results;
it is neither an axiom nor a purported proof of the published theorem.

The arbitrary-degree-one specialization of Chen's theorem is kept separate:
the repository's `FiniteMixture` deliberately excludes linear covariance
terms, and its current `CSParisiMeasure.variationalValue` has that domain.
-/

@[expose] public section

namespace SlowEquilibration.SourceLiteratureParisi

open Filter SphericalModel CrisantiSommers
open scoped Topology

/-- Chen's finite-mixture Parisi identity, expressed for every canonical
nonzero, nonnegative finite covariance of supported degree at least two.
No parity restriction is imposed. The quantifier covers every finite
auxiliary mixture in this class, not just a selected original covariance. -/
def Chen2013FiniteParisi : Prop :=
  ∀ (μ : FiniteMixture) (β : ℝ), 0 ≤ β →
    Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop
      (𝓝 (CSParisiMeasure.variationalValue μ β))

/-- A direct instantiation of the explicitly supplied literature endpoint. -/
theorem finite_pressure_limit (hChen : Chen2013FiniteParisi)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop
      (𝓝 (CSParisiMeasure.variationalValue μ β)) :=
  hChen μ β hβ

/-- The limit's variational normalization is the actual value of the
repository's attained canonical Crisanti–Sommers minimizer. -/
theorem finite_limit_value_is_minimum (μ : FiniteMixture) (β : ℝ) :
    (∀ ζ : Admissible,
      CSParisiMeasure.variationalValue μ β ≤ ζ.value β μ.xi) ∧
    (CSParisiMeasure.canonicalMinimizer μ β).value β μ.xi =
      CSParisiMeasure.variationalValue μ β := by
  constructor
  · exact CSParisiMeasure.canonicalMinimizer_isMinimizer μ β
  · rfl

end SlowEquilibration.SourceLiteratureParisi
