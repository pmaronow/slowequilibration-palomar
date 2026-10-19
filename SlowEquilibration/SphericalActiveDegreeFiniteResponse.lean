-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreeTrace

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreeFiniteResponse

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalActiveDegreeKernel
open SphericalActiveDegreePhysicalPressure SphericalActiveDegreePhysicalMoment
open SphericalActiveDegreeTrace SphericalPureProbePhysicalMomentTransfer
open PureCapturePhysicalFullOverlapArray
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging GaussianPerturbationResponse
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem activeDegree_traceMean_eq_physicalMoment
    (μ : FiniteMixture) (β : ℝ) (n : ℕ)
    (p : Degree μ.maxDegree) :
    (∫ g : EuclideanDisorder (n+2) μ.maxDegree,
      varianceTrace (sphereLaw (n+2))
        (activeDegreeLinear (mixtureCoefficients μ) β)
        (activeDegreeLabel p) 1 g
      ∂SYK.standardGaussianMeasureOnEuclidean _) =
      β^2*(mixtureCoefficients μ p)*((n+2 : ℕ) : ℝ)*
        (1-∫ c, (c 0 1)^p.val.val ∂(physicalFullOverlapLaw
          (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2))) := by
  let E := Coordinate (n+2) μ.maxDegree
  let F : EuclideanSpace ℝ E → ℝ := fun g =>
    ∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p.val.val
      ∂(gibbsMeasure (sphereLaw (n+2))
        (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
          (activeDegreeLabel p) 1) g).prod
        (gibbsMeasure (sphereLaw (n+2))
          (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
            (activeDegreeLabel p) 1) g)
  have hF : StronglyMeasurable F := by
    have hd := (physical_pairPower_disorder_measurable_bounded (N := n+2)
      (by omega) μ β p.val.val).1
    have hproj : Measurable (unpackDisorder (N:=n+2) (P:=μ.maxDegree)) := by
      unfold unpackDisorder
      fun_prop
    have heq : F = fun g =>
        (fun J : Disorder (n+2) μ.maxDegree =>
          ∫ z : Vector (n+2) × Vector (n+2), (overlap z.1 z.2)^p.val.val
            ∂(gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)).prod
              (gibbsLaw (n+2) β (field (mixtureCoefficients μ) J)))
        (unpackDisorder g) := by
      funext g
      unfold F
      rw [activeDegreeGibbs_one_eq_original]
    rw [heq]
    exact hd.comp_measurable hproj
  have hFi : Integrable F (SYK.standardGaussianMeasureOnEuclidean E) := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    apply Eventually.of_forall
    intro g
    change ‖F g‖ ≤ 1
    rw [Real.norm_eq_abs]
    have hh := (physical_pairPower_disorder_measurable_bounded (N := n+2)
      (by omega) μ β p.val.val).2 (unpackDisorder g)
    simpa only [F, activeDegreeGibbs_one_eq_original] using hh
  have hpoint (g : EuclideanSpace ℝ E) :
      varianceTrace (sphereLaw (n+2))
        (activeDegreeLinear (mixtureCoefficients μ) β)
        (activeDegreeLabel p) 1 g =
        β^2*(mixtureCoefficients μ p)*((n+2 : ℕ) : ℝ)*(1-F g) :=
    activeDegree_varianceTrace_eq_replicaPower (by omega) μ β p g
  rw [integral_congr_ae (.of_forall hpoint), integral_const_mul,
    integral_sub (integrable_const (1 : ℝ)) hFi, integral_const]
  simp only [probReal_univ, one_smul]
  rw [activeDegree_one_pairPower_eq_physical μ β n p]

/-- Exact finite-dimensional response of the original tensor p-block.
The amplitude one is the source model itself, and the response is its
physical two-replica overlap-power moment. -/
theorem activeDegreePressure_hasDerivAt_one
    (μ : FiniteMixture) (β : ℝ) (n : ℕ)
    (p : Degree μ.maxDegree) :
    HasDerivAt (activeDegreePressure (n+2) μ β p)
      (β^2*(mixtureCoefficients μ p)*
        (1-∫ c, (c 0 1)^p.val.val ∂(physicalFullOverlapLaw
          (n := n) (m := 2) μ β : Measure (FullOverlapCoordinates 2)))) 1 := by
  obtain ⟨K,hK,hL,hbound⟩ :=
    activeDegreeLinear_measurable_bound (N := n+2) (by omega) μ β
  have hd := parameterMean_hasDerivAt (sphereLaw (n+2))
    (activeDegreeLinear (mixtureCoefficients μ) β)
    hL hK hbound (activeDegreeLabel p) 1
  have hm := meanScore_response (sphereLaw (n+2))
    (activeDegreeLinear (mixtureCoefficients μ) β)
    hL hK hbound (activeDegreeLabel p) 1
  change HasDerivAt _
    (meanScore (sphereLaw (n+2))
      (activeDegreeLinear (mixtureCoefficients μ) β) (activeDegreeLabel p) 1) 1 at hd
  rw [hm, one_mul, activeDegree_traceMean_eq_physicalMoment μ β n p] at hd
  have hdiv := hd.div_const ((n+2 : ℕ) : ℝ)
  convert hdiv using 1
  · rfl
  · field_simp [show ((n+2 : ℕ) : ℝ) ≠ 0 by
      exact_mod_cast (by omega : n+2≠0)]

end SlowEquilibration.SphericalActiveDegreeFiniteResponse
