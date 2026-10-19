-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreeKernel
public import SlowEquilibration.SphericalPureProbePhysicalMomentTransfer

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreePhysicalPressure

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalActiveDegreeKernel
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def activeDegreePressure (N : ℕ) (μ : FiniteMixture) (β : ℝ)
    (p : Degree μ.maxDegree) (s : ℝ) : ℝ :=
  parameterMean (sphereLaw N)
    (activeDegreeLinear (mixtureCoefficients μ) β)
    (activeDegreeLabel (N := N) p) s / (N : ℝ)

theorem activeDegree_operator_one {N P : ℕ}
    (p : Degree P) :
    parameterOperator (activeDegreeLabel (N := N) p) 1 =
      ContinuousLinearMap.id ℝ (EuclideanDisorder N P) := by
  ext g i
  cases h : activeDegreeLabel p i <;>
    simp [parameterOperator,coordinateMask,diagonal_apply,h]

theorem activeDegreeGibbs_one_eq_original {N : ℕ}
    (μ : FiniteMixture) (β : ℝ) (p : Degree μ.maxDegree)
    (g : EuclideanDisorder N μ.maxDegree) :
    gibbsMeasure (sphereLaw N)
      (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
        (activeDegreeLabel p) 1) g =
      gibbsLaw N β (field (mixtureCoefficients μ) (unpackDisorder g)) := by
  have heq (x : Vector N) :
      (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
        (activeDegreeLabel p) 1 x) g =
        sphereLinear (mixtureCoefficients μ) x (β • g) := by
    simp only [parameterLinear, ContinuousLinearMap.comp_apply,
      activeDegree_operator_one, ContinuousLinearMap.id_apply]
    simp only [activeDegreeLinear, scaledLinear, smul_apply, map_smul, smul_eq_mul]
  have hm : gibbsMeasure (sphereLaw N)
      (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
        (activeDegreeLabel p) 1) g =
      gibbsMeasure (sphereLaw N) (sphereLinear (mixtureCoefficients μ)) (β • g) := by
    unfold gibbsMeasure
    congr 1
    funext x
    congr 1
    unfold GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
    simp_rw [heq]
  rw [hm, gaussianGibbs_eq_gibbsLaw]

theorem activeDegreePressure_one_eq_quenchedPressure {N : ℕ}
    (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (p : Degree μ.maxDegree) :
    activeDegreePressure N μ β p 1 = quenchedPressure N μ β := by
  unfold activeDegreePressure parameterMean parameterLogPartition
  rw [activeDegree_operator_one]
  change (∫ g : EuclideanDisorder N μ.maxDegree,
      logPartition (sphereLaw N)
        (activeDegreeLinear (mixtureCoefficients μ) β) g
      ∂SYK.standardGaussianMeasureOnEuclidean _) / (N : ℝ) = _
  rw [← gaussianMeanLogPartition_eq_quenchedPressure hN μ β]
  unfold averagedLogPartition
  congr 1
  apply integral_congr_ae
  exact .of_forall fun g => by
    unfold logPartition GaussianSpinInterpolation.moment
      GaussianSpinInterpolation.weight
    congr 1
    apply integral_congr_ae
    exact .of_forall fun x => by
      simp only [activeDegreeLinear,scaledLinear,smul_apply,map_smul,smul_eq_mul]

theorem activeDegreePressure_convex {N : ℕ}
    (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (p : Degree μ.maxDegree) :
    ConvexOn ℝ univ (activeDegreePressure N μ β p) := by
  let c := mixtureCoefficients μ
  let L := activeDegreeLinear (N := N) c β
  let K := |β| * Real.sqrt ((N : ℝ) * covariancePolynomial c 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : ∀ᵐ x ∂sphereLaw N, ‖L x‖ ≤ K :=
    scaledLinear_bound (sphereLaw N) (sphereLinear c)
      (sphereLinear_bound hN c (mixtureCoefficients_nonnegative μ)) β
  have hL : Measurable L :=
    scaledLinear_measurable _ (sphereLinear_measurable c) β
  have hc := parameterMean_convex (sphereLaw N) L hL hK hb
    (activeDegreeLabel p)
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb' hab
  have h := hc.2 hx hy ha hb' hab
  change parameterMean (sphereLaw N) L (activeDegreeLabel p)
    (a*x+b*y)/(N : ℝ) ≤
      a*(parameterMean (sphereLaw N) L (activeDegreeLabel p) x/(N : ℝ))+
      b*(parameterMean (sphereLaw N) L (activeDegreeLabel p) y/(N : ℝ))
  simp only [smul_eq_mul] at h
  convert div_le_div_of_nonneg_right h (Nat.cast_nonneg N) using 1; ring

end SlowEquilibration.SphericalActiveDegreePhysicalPressure
