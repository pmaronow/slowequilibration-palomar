-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudePosteriorMoments

@[expose] public section

/-! An arbitrary measurable bad-band event has small literal determinant
weight under the genuine affine critical-point posterior. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphereHessian SlowEquilibration.WholeFieldRegression
open SlowEquilibration.SphericalSequentialRegression
open scoped ENNReal
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual normalized posterior bad-event estimate in precisely the
nonnegative-integral form consumed by marked Kac--Rice. -/
theorem latitude_posterior_bad_event_weight (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1) {g Z : ℝ} (hg : 0<g) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∃ C : ℝ,0<C ∧ ∀ (n : ℕ) (w : Vector (n+3)) (_hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
      (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (_he : ∀ x,inner ℝ (e x) w=0)
      (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)),
      2*Real.sqrt (latitudeCurvatureVariance c q)+g≤z 1 → z 1≤Z →
      ∀ A : Set (Disorder (n+3) μ.maxDegree),MeasurableSet A →
      ∀ δ : ℝ,(latitudeNormalizedPosterior μ Q w e q y hy z).real A≤δ →
      (∫⁻ J,ENNReal.ofReal (latitudeAbsoluteDet c w e q y J)*(if J∈A then 1 else 0)
        ∂latitudeNormalizedPosterior μ Q w e q y hy z)≤
      ENNReal.ofReal (Real.sqrt C*Real.sqrt δ)*
        latitudeDeterminantMean (n+1) (Q^2*μ.xi2 Q) q (((n+3 : ℕ) : ℝ)*z 1) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  obtain ⟨C,hC,hM⟩ := latitude_posterior_normalized_moments μ hQ hq0 hq1
    (Z := Z) (r := 2) hg (by norm_num)
  refine ⟨C,hC,?_⟩
  intro n w hw e he y hy z hzg hzZ A hA δ hδ
  let ν := latitudeNormalizedPosterior μ Q w e q y hy z
  let D := latitudeAbsoluteDet c w e q y
  have hp := hM n w hw e he y hy z hzg hzZ
  have hD : ∀ J,0≤D J := fun _ => abs_nonneg _
  have hh := GOEMaximumDeterminant.determinant_event_holder ν D hp.1
    (.of_forall hD) hp.2.2.1 A hA hp.2.2.2.1 hp.2.2.2.2 hδ
  have hb := (div_le_iff₀ hp.2.2.1).mp hh
  have hevent : (∫⁻ J,ENNReal.ofReal (D J)*(if J∈A then 1 else 0) ∂ν)=
      ENNReal.ofReal (∫ J in A,D J ∂ν) := by
    rw [show (fun J => ENNReal.ofReal (D J)*(if J∈A then 1 else 0))=
      A.indicator (fun J => ENNReal.ofReal (D J)) by
        funext J
        by_cases hJ : J∈A <;> simp [hJ]]
    rw [lintegral_indicator hA]
    exact (ofReal_integral_eq_lintegral_ofReal hp.1.restrict (.of_forall hD)).symm
  have hmean : ENNReal.ofReal (∫ J,D J ∂ν)=
      latitudeDeterminantMean (n+1) (Q^2*μ.xi2 Q) q (((n+3 : ℕ) : ℝ)*z 1) := by
    rw [ofReal_integral_eq_lintegral_ofReal hp.1 (.of_forall hD)]
    exact latitude_posterior_det_mean μ hQ w hw e he hq0 hq1 y hy (((n+3 : ℕ) : ℝ) • z)
  change (∫⁻ J,ENNReal.ofReal (D J)*(if J∈A then 1 else 0) ∂ν)≤_
  rw [hevent]
  apply (ENNReal.ofReal_le_ofReal hb).trans_eq
  rw [ENNReal.ofReal_mul (by positivity),hmean]

end
end SlowEquilibration.SphericalLatitudeChartKacRice
