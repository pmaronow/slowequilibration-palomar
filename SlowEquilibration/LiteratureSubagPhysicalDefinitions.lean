-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCertificate
public import SlowEquilibration.SphericalParisiBound
public import SlowEquilibration.SphericalGibbsAllDimensions
public import SlowEquilibration.GaussianReplicaKernel

@[expose] public section

/-!
# Physical objects in Subag's spherical TAP theorems

Eliran Subag, *Free energy landscapes in spherical spin glasses*, Duke Math. J.
173 (2024), arXiv:1804.10576v6.  These definitions use the original ordered
Gaussian-tensor field, its radius-`sqrt N` sphere law and the annealed Gibbs
replicas.  In particular, no independent residual field is silently substituted
for the replicated band of (1.10) in that paper.
-/

namespace SlowEquilibration.LiteratureSubagPhysicalDefinitions

noncomputable section
open MeasureTheory Filter Set
open SphericalModel CrisantiSommers CSParisiMeasure
open scoped Topology BigOperators
set_option autoImplicit false

/-- The disorder-averaged probability from Subag's Definition 2, (1.15),
on the repository's literal original Gibbs replicas. -/
def expectedOverlapBlockProbability (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) : ℝ :=
  (GaussianReplicaKernel.law (disorderLaw N μ.maxDegree)
    (allDimensionGibbsKernel (mixtureCoefficients μ) β) k).real
    {σ : Fin k → Vector N |
      ∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < ρ}

/-- Subag's Definition 2 with the asymptotic logarithm interpreted only
where its probability is positive.  Eventual positivity excludes Lean's
convention `Real.log 0 = 0`, which would otherwise weaken the paper's claim. -/
def MultiSamplable (μ : FiniteMixture) (β q : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
    (∀ᶠ N : ℕ in atTop, 0 < expectedOverlapBlockProbability N k μ β q ρ) ∧
    Tendsto (fun N : ℕ =>
      Real.log (expectedOverlapBlockProbability N k μ β q ρ) / (N : ℝ))
      atTop (nhds (0 : ℝ))

/-- Subag's optimality contact set `S_β` in (1.38), written using the
repository's exact first variation.  Its `firstVariation` is Subag's
`φ(s)` since both are `β² ξ(s) - ∫₀ˢ∫₀ᵗ xHat(r)⁻² dr dt` and vanish at zero. -/
def Contact (μ : FiniteMixture) (β q : ℝ) : Prop :=
  q ∈ Ico (0 : ℝ) 1 ∧
    ∀ r ∈ Ico (0 : ℝ) 1,
      firstVariation β μ.xi (canonicalMinimizer μ β).law r ≤
        firstVariation β μ.xi (canonicalMinimizer μ β).law q

/-- The physical replicated band in Subag (1.10), with the paper's `q`
equal to squared center norm divided by `N`.  The center condition is
`|R(σᵢ,m)-q| ≤ δ sqrt(q)`; replica pairs use the strict tolerance `ρ`. -/
def ReplicatedBand {N : ℕ} (k : ℕ) (q δ ρ : ℝ)
    (m : Vector N) : Set (Fin k → Vector N) :=
  {σ | (∀ i, |overlap (σ i) m - q| ≤ δ * Real.sqrt q) ∧
    (∀ i j, i ≠ j → |overlap (σ i) (σ j) - q| < ρ)}

/-- The literal replicated partition with the center field value removed
once for each replica, matching Subag's `\widetilde F_{N,β}`. -/
def replicatedBandPartition {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) : ℝ :=
  ∫ σ in ReplicatedBand k q δ ρ m,
    Real.exp (β * ∑ i : Fin k,
      (field (mixtureCoefficients μ) J (σ i) -
        field (mixtureCoefficients μ) J m))
    ∂Measure.pi (fun _ : Fin k => sphereLaw N)

/-- Subag's normalized log replicated-band partition, (1.10). -/
def replicatedBandPressure {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (β q δ ρ : ℝ) (J : Disorder N μ.maxDegree) (m : Vector N) : ℝ :=
  Real.log (replicatedBandPartition k μ β q δ ρ J m) / ((N : ℝ) * (k : ℝ))

/-- The actual original-disorder expectation of the replicated pressure.
The source's rotational invariance makes this independent of `m` on the
specified center sphere; no such invariance is built into the definition. -/
def expectedReplicatedBandPressure {N : ℕ} (k : ℕ) (μ : FiniteMixture)
    (β q δ ρ : ℝ) (m : Vector N) : ℝ :=
  ∫ J, replicatedBandPressure k μ β q δ ρ J m
    ∂disorderLaw N μ.maxDegree

end
end SlowEquilibration.LiteratureSubagPhysicalDefinitions
