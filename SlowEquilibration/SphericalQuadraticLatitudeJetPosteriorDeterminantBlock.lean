-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPosteriorResidualIndependence
public import SlowEquilibration.SphericalMarkedWindows

@[expose] public section

/-! The genuine intrinsic determinant is a Borel function of the Hessian
coordinates in the independent quadratic/Hessian block, at a fixed posterior
radial mark. The identification holds almost surely at every mark target. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression IntrinsicHessianLaw SphericalSequentialRegression
open ConditionedIntrinsicHessian ConditionedDeterminantMoments
open SphericalMarkedWindows
open scoped RealInnerProductSpace
set_option autoImplicit false

def quadraticHessianBlockDet (n : ℕ) (k : ℝ)
    (v : EuclideanSpace ℝ (Sum (Fin 1) (Fin (n+1) × Fin (n+1)))) : ℝ :=
  let M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    fun i j => v (Sum.inr (i,j))
  |(M - k • 1).det|

theorem quadraticHessianBlockDet_measurable (n : ℕ) (k : ℝ) :
    Measurable (quadraticHessianBlockDet n k) := by
  let M : EuclideanSpace ℝ
      (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) →
      Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
    fun v i j => v (Sum.inr (i,j))
  have hmat : Continuous M := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (EuclideanSpace.proj (Sum.inr (i,j))).continuous
  have h := (hmat.sub (continuous_const : Continuous
    (fun _ : EuclideanSpace ℝ
      (Sum (Fin 1) (Fin (n+1) × Fin (n+1))) =>
      k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)))).matrix_det.abs.measurable
  convert h using 1
  ext v
  rfl

/-- The original determinant is exactly decoded from the joint true Y₂/W
block on the canonical physical mixed Palm posterior. -/
theorem intrinsicDet_eq_quadraticHessianBlockDet_ae
    {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (a : ℝ) (u ω : Vector (n+2))
    (hu : ‖u‖^2=((n+2:ℕ):ℝ))
    (z : EuclideanSpace ℝ (Fin 2)) :
    ∀ᵐ J ∂mixedLaw μ Q u hu z,
      intrinsicDet μ Q u J =
        quadraticHessianBlockDet n (z 1)
          (actualObservation (flatQuadraticHessianBlock μ Q a u ω hu) J) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hscore := SphericalMarkedWindows.mixedConditioned_score_ae μ hQ hnp u hu z
  change ∀ᵐ J ∂mixedLaw μ Q u hu z, actualScore c J u=z at hscore
  filter_upwards [hscore] with J hJ
  have hrad : jet c 1 u (fun _ => u) J/((n+2:ℕ):ℝ)=z 1 := by
    have hr := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hJ
    change ((n+2:ℕ):ℝ)⁻¹ *
      scoreCLM c u (euclideanDisorder J) 1=z 1 at hr
    rw [scoreCLM_apply_one,unpack_euclideanDisorder] at hr
    simpa only [inv_mul_eq_div] using hr
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
