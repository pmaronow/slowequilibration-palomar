-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPureResidualIndependence
public import SlowEquilibration.SphericalQuadraticLatitudeJetPosteriorDeterminantBlock
public import SlowEquilibration.SphericalTAPPhysicalHessianSource

@[expose] public section

/-! Under the actual proper-pure scalar-value posterior, Euler's identity
fixes the radial Hessian shift at `p*e`, so the intrinsic determinant is a
function of the joint true quadratic/Hessian Gaussian block. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression IntrinsicHessianLaw SphericalSequentialRegression
open ConditionedIntrinsicHessian ConditionedDeterminantMoments
open SphericalMarkedWindows SphericalTAPPhysicalHessianSource
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem intrinsicDet_eq_quadraticHessianBlockDet_pure_ae
    {n : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) (a : ℝ) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ)) (e : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∀ᵐ J ∂valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu e,
      intrinsicDet μ Q u J =
        quadraticHessianBlockDet n ((p:ℝ)*e)
          (actualObservation (flatQuadraticHessianBlock μ Q a u ω hu) J) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hval := valueConditioned_value_ae μ hQ u hu e
  change ∀ᵐ J ∂valueConditionedLaw c u hu e,
    field c J u / (n+2 : ℕ) = e at hval
  filter_upwards [hval] with J hJ
  have hrad : jet c 1 u (fun _ => u) J/((n+2:ℕ):ℝ)=(p:ℝ)*e := by
    rw [pure_radial_score_eq_degree_value p hp alpha halpha Q u J]
    change (p:ℝ)*field c J u/((n+2:ℕ):ℝ)=(p:ℝ)*e
    rw [mul_div_assoc, hJ]
  have hmat :
      (fun i j : Fin (n+1) =>
        (actualObservation (flatQuadraticHessianBlock μ Q a u ω hu) J)
          (Sum.inr (i,j))) =
      hessianMatrix c u (tangentFrame u hu) J := by
    ext i j
    change flatQuadraticHessianBlock μ Q a u ω hu (euclideanDisorder J)
      (Sum.inr (i,j)) = hessianEntry c u (tangentFrame u hu) i j J
    rw [flatQuadraticHessianBlock_inr,ambientHessianCLM_apply,
      unpack_euclideanDisorder]
  unfold intrinsicDet quadraticHessianBlockDet
  rw [intrinsicHessian_det c J u hu,hrad,hmat]

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
