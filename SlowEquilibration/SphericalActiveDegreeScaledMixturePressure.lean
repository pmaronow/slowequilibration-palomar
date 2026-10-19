-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreeCoefficientPressure

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreeScaledMixturePressure

open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalActiveDegreeKernel
open SphericalActiveDegreePhysicalPressure SphericalActiveDegreeScaledField
open SphericalActiveDegreeCoefficientPressure
open FiniteMixtureActiveDegreeScaling
open GaussianSpinInterpolation
open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem scaleActiveDegree_coefficients_on_original
    (μ : FiniteMixture) (p : Degree μ.maxDegree)
    (s : ℝ) (hs : 0 < s) (hcp : 0 < mixtureCoefficients μ p)
    (q : Degree μ.maxDegree) :
    (scaleActiveDegree μ p s hs hcp).coeff q.val.val =
      scaleCoefficients (mixtureCoefficients μ) p s q := by
  by_cases hq : q=p
  · subst q
    rw [scaleActiveDegree_coeff_self]
    simp [scaleCoefficients,mixtureCoefficients]
  · rw [scaleActiveDegree_coeff_other μ p s hs hcp
      (by intro heq; exact hq (Subtype.ext (Fin.ext heq)))]
    simp [scaleCoefficients,mixtureCoefficients,hq]

theorem scaledMixture_quenchedPressure_eq_coefficientPressure
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (p : Degree μ.maxDegree) (s : ℝ) (hs : 0 < s)
    (hcp : 0 < mixtureCoefficients μ p) :
    quenchedPressure N (scaleActiveDegree μ p s hs hcp) β =
      averagedLogPartition (sphereLaw N)
        (sphereLinear (scaleCoefficients (mixtureCoefficients μ) p s)) β /
          (N : ℝ) := by
  let ν := scaleActiveDegree μ p s hs hcp
  have hmax : ν.maxDegree=μ.maxDegree := scaleActiveDegree_maxDegree μ p s hs hcp
  have hh := (gaussianMeanLogPartition_eq_quenchedPressure hN ν β).symm
  unfold mixtureCoefficients at hh
  rw [hmax] at hh
  rw [hh]
  congr 2
  congr 1
  funext q
  exact scaleActiveDegree_coefficients_on_original μ p s hs hcp q

/-- The interior amplitude pressure is exactly the ordinary physical
quenched pressure of a genuine finite mixture with that degree rescaled. -/
theorem activeDegreePressure_eq_scaledMixture_quenchedPressure
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (p : Degree μ.maxDegree) (s : ℝ) (hs : 0 < s)
    (hcp : 0 < mixtureCoefficients μ p) :
    activeDegreePressure N μ β p s =
      quenchedPressure N (scaleActiveDegree μ p s hs hcp) β := by
  rw [activeDegreePressure_eq_scaledCoefficientPressure μ β p s hs.le,
    scaledMixture_quenchedPressure_eq_coefficientPressure hN μ β p s hs hcp]

end SlowEquilibration.SphericalActiveDegreeScaledMixturePressure
