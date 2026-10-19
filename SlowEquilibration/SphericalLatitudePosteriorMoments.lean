-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeDeterminantLaw
public import SlowEquilibration.ScaledLawNormalizedMoments
public import SlowEquilibration.GOEPhysicalNormalizedMoments
public import SlowEquilibration.GOEMaximumDeterminant

@[expose] public section

/-! Genuine affine-latitude posterior determinant moments and event weights.
All constants come from the actual finite-dimensional physical GOE law. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.GOERawMoments SlowEquilibration.GOEPhysicalPotential
open SlowEquilibration.GOEPhysicalNormalizedMoments
open SlowEquilibration.ScaledLawNormalizedMoments
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every actual posterior target in a fixed exterior radial interval has
bounded own-mean normalized moments, uniformly in dimension and center. -/
theorem latitude_posterior_normalized_moments (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1) {g Z r : ℝ} (hg : 0<g) (hr : 0≤r) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∃ C : ℝ,0<C ∧ ∀ (n : ℕ) (w : Vector (n+3)) (_hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
      (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (_he : ∀ x,inner ℝ (e x) w=0)
      (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)),
      2*Real.sqrt (latitudeCurvatureVariance c q)+g≤z 1 → z 1≤Z →
      let ν := latitudeNormalizedPosterior μ Q w e q y hy z
      let D := latitudeAbsoluteDet c w e q y
      Integrable D ν ∧
        (∫ J,D J ∂ν)=latitudeDeterminantScale n*physicalMean n (n+3) (latitudeCurvatureVariance c q) (z 1) ∧
        0<∫ J,D J ∂ν ∧
        Integrable (fun J => (D J/(∫ K,D K ∂ν))^r) ν ∧
        (∫ J,(D J/(∫ K,D K ∂ν))^r ∂ν)≤C := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hb := center_latitudeCurvatureVariance_pos μ hQ hq1
  obtain ⟨C,hC,hM⟩ := normalized_physical_moments 2 (Z := Z) (r := r) hb hg hr
  refine ⟨C,hC,?_⟩
  intro n w hw e he y hy z hzg hzZ
  have hp := hM n (z 1) hzg hzZ
  have hL := latitude_posterior_absDet_hasLaw μ hQ w hw e he hq0 hq1 y hy z
  have hh := normalized_moments_of_scaled_law _ _ _ _ (latitudeDeterminantScale_pos n)
    (matrixAbsoluteDet_measurable n (z 1)) hL hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  exact hh

/-- The full tensor event may depend on the same Hessian. A genuine
uniform normalized second moment controls its determinant-weighted mass. -/
theorem latitude_posterior_determinant_event_bound (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1) {g Z : ℝ} (hg : 0<g) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∃ C : ℝ,0<C ∧ ∀ (n : ℕ) (w : Vector (n+3)) (_hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
      (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (_he : ∀ x,inner ℝ (e x) w=0)
      (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)),
      2*Real.sqrt (latitudeCurvatureVariance c q)+g≤z 1 → z 1≤Z →
      ∀ A : Set (Disorder (n+3) μ.maxDegree),MeasurableSet A →
      let ν := latitudeNormalizedPosterior μ Q w e q y hy z
      let D := latitudeAbsoluteDet c w e q y
      (∫ J in A,D J ∂ν)≤Real.sqrt C*Real.sqrt (ν.real A)*(∫ J,D J ∂ν) := by
  dsimp only
  obtain ⟨C,hC,hM⟩ := latitude_posterior_normalized_moments μ hQ hq0 hq1
    (Z := Z) (r := 2) hg (by norm_num)
  refine ⟨C,hC,?_⟩
  intro n w hw e he y hy z hzg hzZ A hA
  let ν := latitudeNormalizedPosterior μ Q w e q y hy z
  let D := latitudeAbsoluteDet (centerCoefficients (mixtureCoefficients μ) Q) w e q y
  have hp := hM n w hw e he y hy z hzg hzZ
  have h := GOEMaximumDeterminant.determinant_event_holder ν D hp.1
    (.of_forall fun _ => abs_nonneg _) hp.2.2.1 A hA hp.2.2.2.1 hp.2.2.2.2 (le_refl (ν.real A))
  exact (div_le_iff₀ hp.2.2.1).mp h

end
end SlowEquilibration.SphericalLatitudeChartKacRice
