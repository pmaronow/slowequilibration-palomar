-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiFiniteMixtureGroundBridge
public import SlowEquilibration.SphericalParisiOneStepDualPressureLimit

/-! The actual finite-mixture ordered Gaussian tensor field inherits the
one-step pressure bound for every probability reference on the unit sphere.
The reference may depend on dimension. This does not identify the reference
with the uniform physical sphere law, nor prove the Parisi lower bound. -/
@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalParisiFiniteMixtureDualPressure

open MeasureTheory Filter PureTensorJetBounds
open SphericalParisiFiniteMixtureGroundBridge
open SphericalParisiLabeledCovariance
open SphericalParisiLabeledOriginalEndpoint
open SphericalParisiOneStepDualScalar
open SphericalParisiOneStepDualPressureLimit
open scoped Topology

/-- The literal one-step dual scalar evaluated at the physical covariance
polynomial and its first derivative. -/
def sourceDual (μ : FiniteMixture) (α q κ : ℝ) : ℝ :=
  κ / 2 +
    Real.log (κ / (κ - α * (μ.xi1 1 - μ.xi1 q))) / (2 * α) +
    μ.xi1 q / (2 * (κ - α * (μ.xi1 1 - μ.xi1 q))) -
    α * ((μ.xi1 1 - μ.xi 1) - (q * μ.xi1 q - μ.xi q)) / 2

/-- The dual arising from the genuine labeled Gaussian interpolation is
exactly the source polynomial dual, including all odd-degree terms. -/
theorem sourceDual_eq_tensorDual (μ : FiniteMixture) (α q κ : ℝ) :
    sourceDual μ α q κ =
      oneStepDual (tensorDegree μ) (tensorCoefficient μ) α q κ := by
  simp only [sourceDual, oneStepDual, theta,
    tensorXi1_eq, tensorXi_eq, one_mul]

/-- Actual all-parity tensor pressure upper for any dimension-dependent
probability reference on the unit sphere. The Gaussian field is the original
finite ordered-tensor feature field, and the pressure is its expected log
partition. No limiting physical-pressure or Parisi conclusion is assumed. -/
theorem eventual_tensor_pressure_le_sourceDual
    (μ : FiniteMixture)
    (ν : (N : ℕ) → Measure (UnitSphere N))
    (hν : ∀ N, 0 < N → IsProbabilityMeasure (ν N))
    {α β κ q ε : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hmargin : 0 < κ - α * (μ.xi1 1 - μ.xi1 q))
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      originalSpinPressure (ν N) (tensorDegree μ) (tensorCoefficient μ) β /
        (β * (N : ℝ)) ≤ sourceDual μ α q κ + ε := by
  have hdegree : ∀ p, 1 ≤ tensorDegree μ p := by
    intro p
    have hp := tensorDegree_ge_two μ p
    omega
  have hmargin' : 0 < κ - α *
      (xi1 (tensorDegree μ) (tensorCoefficient μ) 1 -
        xi1 (tensorDegree μ) (tensorCoefficient μ) q) := by
    simpa only [tensorXi1_eq] using hmargin
  have H := eventual_spin_pressure_oneStepDual_upper
    (tensorDegree μ) (tensorCoefficient μ)
    (tensorCoefficient_nonnegative μ) hdegree ν hν
    hα hαβ hq hq1 hmargin' ε hε
  simpa only [← sourceDual_eq_tensorDual] using H

end SlowEquilibration.SphericalParisiFiniteMixtureDualPressure
