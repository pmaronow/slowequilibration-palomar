-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeNormalizedMarkedComparison
public import SlowEquilibration.SphericalLatitudePosteriorMarks

@[expose] public section

/-! Actual critical-point counts with a measurable bad full-field event.
The genuine score posterior, physical determinant moments and marked
Kac--Rice theorem supply the complete finite-dimensional comparison. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphereHessian SlowEquilibration.WholeFieldRegression
open SlowEquilibration.SphericalSequentialRegression
open scoped ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitudeNormalizedPosterior_score_ae {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (w : Vector (n+3)) (hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
    (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (he : ∀ x,inner ℝ (e x) w=0)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂latitudeNormalizedPosterior μ Q w e q y hy z,actualLatitudeScore c w e q J y=z := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  filter_upwards [coefficientKernel_observation_ae _
    (center_latitudeJointCLM_surjective μ hQ w hw e he hq0 hq1 y hy)
      (jointScoreTarget (n+1) (((n+3 : ℕ) : ℝ) • z))] with J hJ
  have hs : latitudeScoreCLM c w e q y (euclideanDisorder J)=((n+3 : ℕ) : ℝ) • z := by
    apply PiLp.ext
    intro i
    exact congrArg (fun v => v (Sum.inl i)) hJ
  change ((n+3 : ℕ) : ℝ)⁻¹ • latitudeScoreCLM c w e q y (euclideanDisorder J)=z
  rw [hs,smul_smul,inv_mul_cancel₀ (by positivity : ((n+3 : ℕ) : ℝ)≠0),one_smul]

/-- A bad-event probability under the literal every-target posterior yields
an actual marked critical-count bound. No posterior determinant estimate or
conditional independence is assumed. -/
theorem latitude_actual_bad_mark_count_bound (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1) {g Z : ℝ} (hg : 0<g) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∃ C : ℝ,0<C ∧ ∀ (n : ℕ) (w : Vector (n+3)) (_hw : ‖w‖^2=((n+3 : ℕ) : ℝ))
      (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)) (_he : ∀ x,inner ℝ (e x) w=0)
      (S : Set (EuclideanSpace ℝ (Fin 2))),MeasurableSet S →
      (∀ z∈S,2*Real.sqrt (latitudeCurvatureVariance c q)+g≤z 1 ∧ z 1≤Z) →
      ∀ E : Set (Disorder (n+3) μ.maxDegree × Vector (n+2)),MeasurableSet E →
      ∀ δ : ℝ,
      (∀ (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)),z∈S →
        (latitudeNormalizedPosterior μ Q w e q y hy z).real {J | (J,y)∈E}≤δ) →
      (∫⁻ J,actualLatitudeSphereCount c w e q
        (fun J y => if actualLatitudeScore c w e q J y∈S ∧ (J,y)∈E then 1 else 0) J
          ∂disorderLaw (n+3) μ.maxDegree)≤
      ENNReal.ofReal (Real.sqrt C*Real.sqrt δ)*
        (∫⁻ J,actualLatitudeSphereCount c w e q
          (fun J y => if actualLatitudeScore c w e q J y∈S then 1 else 0) J
            ∂disorderLaw (n+3) μ.maxDegree) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  obtain ⟨C,hC,hweight⟩ := latitude_posterior_bad_event_weight μ hQ hq0 hq1 (Z := Z) hg
  refine ⟨C,hC,?_⟩
  intro n w hw e he S hS hrad E hE δ hprob
  let f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun z => if z∈S then 1 else 0
  let psi : Disorder (n+3) μ.maxDegree → Vector (n+2) → ℝ≥0∞ :=
    fun J y => if actualLatitudeScore c w e q J y∈S ∧ (J,y)∈E then 1 else 0
  have hf : Measurable f := Measurable.ite hS measurable_const measurable_const
  have hscore : Measurable (fun p : Disorder (n+3) μ.maxDegree × Vector (n+2) =>
      actualLatitudeScore c w e q p.1 p.2) :=
    (latitudeScore_jointContinuous c w e q).measurable.const_smul (((n+3 : ℕ) : ℝ)⁻¹)
  have hpsi : Measurable (fun p : Disorder (n+3) μ.maxDegree × Vector (n+2) => psi p.1 p.2) :=
    Measurable.ite ((hS.preimage hscore).inter hE) measurable_const measurable_const
  apply actual_latitude_marked_count_le_normalized_score_count μ hQ w hw e he hq0 hq1
    psi hpsi f hf (Real.sqrt C*Real.sqrt δ)
  intro y hy z
  dsimp only
  change (∫⁻ J,ENNReal.ofReal (latitudeAbsoluteDet c w e q y J)*psi J y
    ∂latitudeNormalizedPosterior μ Q w e q y hy z)≤_
  have hfixed := latitudeNormalizedPosterior_score_ae μ hQ w hw e he hq0 hq1 y hy z
  by_cases hz : z∈S
  · have hA : MeasurableSet {J : Disorder (n+3) μ.maxDegree | (J,y)∈E} :=
      hE.preimage (measurable_id.prodMk measurable_const)
    have hb := hweight n w hw e he y hy z (hrad z hz).1 (hrad z hz).2 _ hA δ (hprob y hy z hz)
    have heq : (∫⁻ J,ENNReal.ofReal (latitudeAbsoluteDet c w e q y J)*psi J y
        ∂latitudeNormalizedPosterior μ Q w e q y hy z)=
        ∫⁻ J,ENNReal.ofReal (latitudeAbsoluteDet c w e q y J)*(if (J,y)∈E then 1 else 0)
          ∂latitudeNormalizedPosterior μ Q w e q y hy z := by
      apply lintegral_congr_ae
      filter_upwards [hfixed] with J hJ
      change actualLatitudeScore c w e q J y=z at hJ
      simp only [psi,hJ,hz,true_and]
    rw [heq]
    simpa [f,hz,c] using hb
  · have heq : (∫⁻ J,ENNReal.ofReal (latitudeAbsoluteDet c w e q y J)*psi J y
        ∂latitudeNormalizedPosterior μ Q w e q y hy z)=0 := by
      apply (lintegral_congr_ae (g := fun _ => 0) ?_).trans (lintegral_zero)
      filter_upwards [hfixed] with J hJ
      change actualLatitudeScore c w e q J y=z at hJ
      simp [psi,hJ,hz]
    rw [heq]
    exact bot_le

end
end SlowEquilibration.SphericalLatitudeChartKacRice
