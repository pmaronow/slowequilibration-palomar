-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairJetIntensity
public import SlowEquilibration.SphericalCountIntensity

/-! Exact one-point physical jet normalization by the true round-sphere
area. This identifies the marginals in the physical pair ratio with the
actual one-point critical-count intensity. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity IntrinsicHessianLaw PairObservationTargets
open SphericalMarkedWindows SphericalSequentialRegression SphericalIntrinsicChartKacRice
open SphereChartVolume
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

lemma source_tangent_gradient_zero_density {n:ℕ} (μ:FiniteMixture) {Q:ℝ} (hQ:0<Q)
    (x:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) :
    realObservationDensity (gradientCLM (centerCoefficients (mixtureCoefficients μ) Q) x
      (tangentFrame x hx)) 0=(intrinsicGradientDensity (n+2) μ Q).toReal:=by
  rw [realObservationDensity_eq_toReal _
    (center_gradient_surjective (by omega) μ hQ x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)),
    center_gradient_pdf_zero (by omega) μ hQ.le x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx)]
  rfl

theorem source_mixed_one_point_jet_intensity {n:ℕ} (μ:FiniteMixture) {Q:ℝ} (hQ:0<Q)
    (hnp:μ.minDegree<μ.maxDegree) (x:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (h k:ℝ) :
    ENNReal.ofReal (sourceMixedOnePointJetIntensity μ Q x hx h k)=
      intrinsicGradientDensity (n+2) μ Q*physicalScorePdf (n+3) μ Q (WithLp.toLp 2 ![h,k])*
        ENNReal.ofReal (GOEPhysicalPotential.physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) k):=by
  unfold sourceMixedOnePointJetIntensity
  dsimp only
  rw [source_tangent_gradient_zero_density μ hQ,
    normalizedScorePdf_eq (by omega) μ hQ hnp x hx]
  rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (show intrinsicGradientDensity (n+2) μ Q≠⊤ from ENNReal.ofReal_ne_top),
    ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]
  rfl

theorem source_pure_one_point_jet_intensity {n:ℕ} (p:ℕ) (hp:2 ≤ p)
    (alpha:ℝ) (halpha:0<alpha) {Q:ℝ} (hQ:0<Q)
    (x:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (h:ℝ) :
    let μ:=FiniteMixture.pure p hp alpha halpha
    ENNReal.ofReal (sourcePureOnePointJetIntensity p hp alpha halpha Q x hx h)=
      intrinsicGradientDensity (n+2) μ Q*physicalValuePdf (n+3) μ Q h*
        ENNReal.ofReal (GOEPhysicalPotential.physicalMean (n+1) (n+3) (Q^2*μ.xi2 Q) ((p:ℝ)*h)):=by
  dsimp only
  unfold sourcePureOnePointJetIntensity
  dsimp only
  rw [source_tangent_gradient_zero_density _ hQ,
    normalizedValuePdf_eq _ hQ x hx]
  rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (show intrinsicGradientDensity (n+2) (FiniteMixture.pure p hp alpha halpha) Q≠⊤ from ENNReal.ofReal_ne_top),
    ENNReal.ofReal_toReal ENNReal.ofReal_ne_top]
  rfl

theorem source_mixed_one_point_jet_area_normalization {n:ℕ} (μ:FiniteMixture) {Q:ℝ} (hQ:0<Q)
    (hnp:μ.minDegree<μ.maxDegree) (x:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (h k:ℝ) :
    manuscriptRoundVolume (n+2) Set.univ*ENNReal.ofReal (sourceMixedOnePointJetIntensity μ Q x hx h k)=
      mixedCriticalIntensity (n+1) μ Q (WithLp.toLp 2 ![h,k]):=by
  rw [source_mixed_one_point_jet_intensity μ hQ hnp]
  unfold mixedCriticalIntensity sphereKRPrefactor
  ac_rfl

theorem source_pure_one_point_jet_area_normalization {n:ℕ} (p:ℕ) (hp:2 ≤ p)
    (alpha:ℝ) (halpha:0<alpha) {Q:ℝ} (hQ:0<Q)
    (x:Vector (n+3)) (hx:‖x‖^2=(n+3:ℕ)) (h:ℝ) :
    manuscriptRoundVolume (n+2) Set.univ*ENNReal.ofReal (sourcePureOnePointJetIntensity p hp alpha halpha Q x hx h)=
      pureCriticalIntensity (n+1) p hp alpha halpha Q h:=by
  rw [source_pure_one_point_jet_intensity p hp alpha halpha hQ]
  unfold pureCriticalIntensity sphereKRPrefactor
  ac_rfl

end
end SlowEquilibration.PairConditionalDeterminantMoments
