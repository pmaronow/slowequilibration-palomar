-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorPhysicalPressureLaw
public import SlowEquilibration.SphericalResidualTemperatureConcentration
public import SlowEquilibration.StrongFieldLaplace

@[expose] public section

/-! Genuine exponential thermal-band typicality under every actual affine
critical-point posterior. The canonical residual limit, static certificate,
dimension correction and Gaussian concentration are all instantiated. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.SphericalLatitudeChartKacRice
open scoped Topology ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem sublevel_measure_eq_of_map_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (R : Measure Y) (f : X → ℝ) (g : Y → ℝ)
    (hf : Measurable f) (hg : Measurable g) (h : P.map f=R.map g) (M : ℝ) :
    P {x | f x<M}=R {y | g y<M} := by
  have hh := congrArg (fun ν : Measure ℝ => ν (Iio M)) h
  rw [Measure.map_apply hf measurableSet_Iio,Measure.map_apply hg measurableSet_Iio] at hh
  exact hh

theorem latitude_posterior_residual_sublevel_measure_eq {n : ℕ} (hn : 1≤n)
    (μ : FiniteMixture) {Q : ℝ} (hQ : Q∈Ioo (0 : ℝ) 1) (β M : ℝ)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ y,inner ℝ (e y) w=0)
    {q : ℝ} (hq : |q|≤1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let θ := μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
    coefficientKernel (latitudeJointCLM c w e q y hy) target
      {J | transverseRemainderPressure c w e q Q β J y<M}=
    disorderLaw n θ.maxDegree {J | Real.log (mixturePartition θ (dimensionCorrectedTemperature β 2 n) J)/
      ((n+2 : ℕ) : ℝ)<M} := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let θ := μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)
  have hp : Measurable (fun J : Disorder (n+2) μ.maxDegree => (J,y)) :=
    measurable_id.prodMk measurable_const
  have hL := (transverseRemainderPressure_jointMeasurable c w e q Q β).comp hp
  have hR := (partition_measurable (N := n) (mixtureCoefficients θ)
    (dimensionCorrectedTemperature β 2 n)).log.div_const (((n+2 : ℕ) : ℝ))
  have hLaw := latitude_posterior_transverseRemainderPressure_map hn μ hQ β w hw e he hq y hy target
  exact sublevel_measure_eq_of_map_eq
    (coefficientKernel (latitudeJointCLM c w e q y hy) target)
    (disorderLaw n θ.maxDegree)
    (fun J => transverseRemainderPressure c w e q Q β J y)
    (fun J => Real.log (mixturePartition θ (dimensionCorrectedTemperature β 2 n) J)/((n+2 : ℕ) : ℝ))
    hL hR hLaw M

/-- Uniform actual posterior thermal-band lower tail for every original
covariance convex on [-1,1], including the true residual static endpoint. -/
theorem qStar_posterior_transverse_pressure_lower_tail (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hε : 0<ε) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+2)),‖w‖^2=((n+2 : ℕ) : ℝ) →
      ∀ (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)),(∀ z,inner ℝ (e z) w=0) →
      ∀ q : ℝ,|q|≤1 → ∀ (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
      (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))),
      coefficientKernel (latitudeJointCLM c w e q y hy) target
        {J | transverseRemainderPressure c w e q Q β J y<F-ε}≤
      ENNReal.ofReal (2*Real.exp (-γ*((n+2 : ℕ) : ℝ))) := by
  dsimp only
  obtain ⟨γ,hγ,hbound⟩ := μ.qStar_taylorResidual_corrected_logPartition_lower_tail hconv hβ 2 hε
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with n hn hdim
  intro w hw e he q hq y hy target
  rw [latitude_posterior_residual_sublevel_measure_eq hdim μ (μ.qStar_solves_plateau hβ).1 β _ w hw e he hq y hy target]
  exact hn

/-- The same genuine posterior typicality for arbitrary parity when
minimum degree three proves the residual's nonnegative covariance range. -/
theorem qStar_posterior_transverse_pressure_lower_tail_of_minDegree (μ : FiniteMixture)
    (hd : 3≤μ.minDegree) {β ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hε : 0<ε) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+2)),‖w‖^2=((n+2 : ℕ) : ℝ) →
      ∀ (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)),(∀ z,inner ℝ (e z) w=0) →
      ∀ q : ℝ,|q|≤1 → ∀ (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
      (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))),
      coefficientKernel (latitudeJointCLM c w e q y hy) target
        {J | transverseRemainderPressure c w e q Q β J y<F-ε}≤
      ENNReal.ofReal (2*Real.exp (-γ*((n+2 : ℕ) : ℝ))) := by
  dsimp only
  obtain ⟨γ,hγ,hbound⟩ := μ.qStar_taylorResidual_corrected_logPartition_lower_tail_of_minDegree hd hβ 2 hε
  refine ⟨γ,hγ,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with n hn hdim
  intro w hw e he q hq y hy target
  rw [latitude_posterior_residual_sublevel_measure_eq hdim μ (μ.qStar_solves_plateau hβ).1 β _ w hw e he hq y hy target]
  exact hn

/-- A pure exponential version for direct physical marked-count use. -/
theorem qStar_posterior_transverse_pressure_exponential (μ : FiniteMixture)
    (hscope : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi ∨ 3≤μ.minDegree) {β ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hε : 0<ε) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
    ∃ γ : ℝ,0<γ ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+2)),‖w‖^2=((n+2 : ℕ) : ℝ) →
      ∀ (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)),(∀ z,inner ℝ (e z) w=0) →
      ∀ q : ℝ,|q|≤1 → ∀ (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
      (target : EuclideanSpace ℝ (Sum (Fin 2) (Fin n))),
      coefficientKernel (latitudeJointCLM c w e q y hy) target
        {J | transverseRemainderPressure c w e q Q β J y<F-ε}≤
      ENNReal.ofReal (Real.exp (-γ*((n+2 : ℕ) : ℝ))) := by
  dsimp only
  have hbound := hscope.elim
    (fun hc => qStar_posterior_transverse_pressure_lower_tail μ hc hβ hε)
    (fun hd => qStar_posterior_transverse_pressure_lower_tail_of_minDegree μ hd hβ hε)
  obtain ⟨γ,hγ,hbound⟩ := hbound
  have hdim : ∀ᶠ n : ℕ in atTop,
      StrongFieldComplexity.polynomialAbsorptionThreshold 2 0 (γ/2)≤((n+2 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (StrongFieldComplexity.polynomialAbsorptionThreshold 2 0 (γ/2)))] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (StrongFieldComplexity.polynomialAbsorptionThreshold 2 0 (γ/2))≤n+2 by omega))
  refine ⟨γ/2,by positivity,?_⟩
  filter_upwards [hbound,hdim] with n hn hdim
  intro w hw e he q hq y hy target
  apply (hn w hw e he q hq y hy target).trans
  apply ENNReal.ofReal_le_ofReal
  have hp := StrongFieldComplexity.polynomial_le_exp_of_threshold 0 (by norm_num : (0 : ℝ)≤2)
    (show 0<γ/2 by positivity) hdim
  simp only [pow_zero,mul_one] at hp
  calc
    _ ≤ Real.exp ((γ/2)*((n+2 : ℕ) : ℝ))*Real.exp (-γ*((n+2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end
end SlowEquilibration.SphericalTaylorRemainder
