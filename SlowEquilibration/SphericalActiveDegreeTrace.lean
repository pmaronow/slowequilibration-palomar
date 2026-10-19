-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalActiveDegreePhysicalMoment

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalActiveDegreeTrace

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalActiveDegreeKernel
open SphericalActiveDegreePhysicalPressure
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging GaussianPerturbationResponse
open GaussianSelectedReplicaTrace
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem activeDegreeLinear_measurable_bound {N : ℕ}
    (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      Measurable (activeDegreeLinear (N := N) (mixtureCoefficients μ) β) ∧
      ∀ᵐ x ∂sphereLaw N,
        ‖activeDegreeLinear (mixtureCoefficients μ) β x‖ ≤ K := by
  let c := mixtureCoefficients μ
  let K := |β| * Real.sqrt ((N : ℝ) * covariancePolynomial c 1)
  refine ⟨K, by dsimp [K]; positivity, ?_, ?_⟩
  · exact scaledLinear_measurable _ (sphereLinear_measurable c) β
  · exact scaledLinear_bound (sphereLaw N) (sphereLinear c)
      (sphereLinear_bound hN c (mixtureCoefficients_nonnegative μ)) β

theorem activeDegree_varianceTrace_eq_replicaPower
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (p : Degree μ.maxDegree) (g : EuclideanDisorder N μ.maxDegree) :
    varianceTrace (sphereLaw N)
      (activeDegreeLinear (mixtureCoefficients μ) β)
      (activeDegreeLabel p) 1 g =
      β^2*(mixtureCoefficients μ p)*(N : ℝ)*
        (1-∫ z : Vector N × Vector N, (overlap z.1 z.2)^p.val.val
          ∂(gibbsMeasure (sphereLaw N)
            (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
              (activeDegreeLabel p) 1) g).prod
            (gibbsMeasure (sphereLaw N)
              (parameterLinear (activeDegreeLinear (mixtureCoefficients μ) β)
                (activeDegreeLabel p) 1) g)) := by
  obtain ⟨K,hK,hL,hbound⟩ := activeDegreeLinear_measurable_bound hN μ β
  let L := activeDegreeLinear (N := N) (mixtureCoefficients μ) β
  let label := activeDegreeLabel (N := N) p
  let G := gibbsMeasure (sphereLaw N) (parameterLinear L label 1) g
  have hG : IsProbabilityMeasure G := gibbsMeasure_probability
    (sphereLaw N) _ (parameterLinear_measurable L hL label 1)
    (parameterLinear_bound (sphereLaw N) L hK hbound label 1) g
  have hsphere : ∀ᵐ x ∂G, ‖x‖^2=(N : ℝ) :=
    (sphereLaw_support hN).filter_mono
      (gibbsMeasure_absolutelyContinuous (sphereLaw N)
        (parameterLinear L label 1) g).ae_le
  have hdiag : (∫ x : Vector N, (overlap x x)^p.val.val ∂G) = 1 := by
    rw [integral_congr_ae (hsphere.mono fun x hx => by
      rw [overlap_self (by omega) x hx])]
    simp
  have ht := varianceTrace_eq_selectedKernel (sphereLaw N) L hL hK hbound
    label 1 g
  rw [ht]
  dsimp only [L,label]
  simp_rw [activeDegree_selectedKernel hN (mixtureCoefficients μ)
    (mixtureCoefficients_nonnegative μ) β p]
  rw [integral_const_mul, integral_const_mul, hdiag]
  ring

end SlowEquilibration.SphericalActiveDegreeTrace
