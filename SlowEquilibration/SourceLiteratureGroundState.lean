-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiFiniteMixtureGroundBridge

/-!
# Conditional spherical ground-state endpoint

Wei-Kuo Chen and Arnab Sen, *Parisi formula, disorder chaos and fluctuation
for the ground state energy in the spherical mixed p-spin models*,
Communications in Mathematical Physics **350** (2017), Theorem 1, equation
(10), together with equation (8) and Lemma 6, arXiv:1512.08492v2.

Their model's covariance is `N * ξ(R)` with a mixture supported on `p ≥ 2`.
Theorem 1's variational formula permits odd degrees; the later assumptions
of evenness in its disorder-chaos and fluctuation results do not apply here.
The optional deterministic external field is specialized to zero below.

`ChenSenFiniteGround` is an explicit hypothesis, not an axiom. Its finite
ordered-tensor maximum is exactly the repository's original Hamiltonian
maximum under the canonical coefficient identification. In particular the
hypothesis is not phrased as a source-specific retained-count or capture
claim. The full monotone right-continuous profile class is used; no one-step
restriction is inserted.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceLiteratureGroundState

open Filter MeasureTheory ProbabilityTheory Set SphericalModel
open SphericalParisiFiniteMixtureGroundBridge
open SphericalParisiGroundRSUpper
open SphericalParisiContinuousMaximum SphericalCriticalLatitude
open FiniteTensorMixtureMaximum PureTensorJetBounds
open scoped Topology

/-- Chen–Sen's zero-temperature variational domain at zero deterministic
external field. Values outside `[0,1)` are immaterial to the integrals. -/
structure GroundProfile where
  L : ℝ
  alpha : ℝ → ℝ
  alpha_nonnegative : ∀ q ∈ Ico (0 : ℝ) 1, 0 ≤ alpha q
  alpha_monotone : MonotoneOn alpha (Ico (0 : ℝ) 1)
  alpha_rightContinuous : ∀ q ∈ Ico (0 : ℝ) 1,
    ContinuousWithinAt alpha (Ici q) q
  alpha_integrable : IntervalIntegrable alpha MeasureTheory.volume 0 1
  height_gt_mass : (∫ q in (0 : ℝ)..1, alpha q) < L

/-- The full Chen–Sen ground-state Crisanti–Sommers functional `Q(L,α)`
from their equation (10), for zero deterministic external field. The
repository's `xi1` and `xi2` are the exact first and second derivatives of
its canonical finite covariance polynomial. -/
def groundFunctional (μ : FiniteMixture) (u : GroundProfile) : ℝ :=
  (μ.xi1 1 * u.L -
      (∫ q in (0 : ℝ)..1, μ.xi2 q *
        (∫ s in (0 : ℝ)..q, u.alpha s)) +
      (∫ q in (0 : ℝ)..1,
        (u.L - ∫ s in (0 : ℝ)..q, u.alpha s)⁻¹)) / 2

/-- The expected finite-dimensional maximum of the literal original
ordered Gaussian tensor field, per spin. For the canonical mixture the
degrees and coefficients are respectively `p` and `μ.coeff p`; Gaussian
tensor amplitudes are their nonnegative square roots. -/
def canonicalGroundEnergy (μ : FiniteMixture) (N : ℕ) : ℝ :=
  (∫ g, actualMaximum (N := N) (tensorDegree μ) (tensorCoefficient μ) g
      ∂SYK.standardGaussianMeasureOnEuclidean
        (Coordinate N (tensorDegree μ))) / (N : ℝ)

/-- The same expectation for the physical continuous residual field with
equal ambient and transverse dimensions. Its disorder coordinates need not
be identified pointwise with those of the ordered tensor construction: the
repository proves equality of the entire continuous Gaussian field laws. -/
def physicalResidualGroundEnergy (μ : FiniteMixture) (N : ℕ) : ℝ :=
  (∫ g, maximum (physicalResidualContinuousField μ N N
    (fun x : UnitSphere N => x.val) continuous_subtype_val g)
      ∂stdGaussian (EuclideanDisorder N μ.maxDegree)) / (N : ℝ)

/-- Exact normalization and Gaussian-law adapter from the repository's
physical residual field to the finite ordered-tensor ground energy. -/
theorem physicalResidualGroundEnergy_eq_canonical (μ : FiniteMixture)
    {N : ℕ} (hN : 0 < N) :
    physicalResidualGroundEnergy μ N = canonicalGroundEnergy μ N := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hOne : (N : ℝ) / (N : ℝ) = 1 := div_self hNr
  rw [physicalResidualGroundEnergy,
    physicalResidualContinuousField_expected_maximum μ N N hN]
  rw [hOne, Real.sqrt_one, one_mul]
  rfl

/-- The published zero-temperature endpoint in its finite, zero-field
specialization, quantified over every canonical finite mixture. The
source proves a stronger `L¹` and almost-sure ground-state limit; this
interface uses the expected limit sufficient for downstream arguments. -/
def ChenSenFiniteGround : Prop :=
  ∀ μ : FiniteMixture, ∃ u : GroundProfile,
    (∀ v : GroundProfile, groundFunctional μ u ≤ groundFunctional μ v) ∧
    Tendsto (canonicalGroundEnergy μ) atTop (𝓝 (groundFunctional μ u))

/-- The exact variational minimum and the physical expected maximum
limit, upon supplying the cited result as a theorem hypothesis. -/
theorem canonical_ground_limit (hChenSen : ChenSenFiniteGround)
    (μ : FiniteMixture) :
    ∃ u : GroundProfile,
      (∀ v : GroundProfile, groundFunctional μ u ≤ groundFunctional μ v) ∧
      Tendsto (canonicalGroundEnergy μ) atTop (𝓝 (groundFunctional μ u)) :=
  hChenSen μ

/-- The cited endpoint is transported to the repository's genuine
continuous residual field, with no additional ground-state hypothesis. -/
theorem physical_residual_ground_limit (hChenSen : ChenSenFiniteGround)
    (μ : FiniteMixture) :
    ∃ u : GroundProfile,
      (∀ v : GroundProfile, groundFunctional μ u ≤ groundFunctional μ v) ∧
      Tendsto (physicalResidualGroundEnergy μ) atTop
        (𝓝 (groundFunctional μ u)) := by
  obtain ⟨u, hmin, hlim⟩ := hChenSen μ
  refine ⟨u, hmin, ?_⟩
  have heq : physicalResidualGroundEnergy μ =ᶠ[atTop]
      canonicalGroundEnergy μ := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact physicalResidualGroundEnergy_eq_canonical μ hN
  exact hlim.congr' heq.symm

end SlowEquilibration.SourceLiteratureGroundState
