-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorPosteriorConcentration
public import SlowEquilibration.SphericalLatitudeBadCountDecay

@[expose] public section

/-! Actual exponentially small count of strong-field critical points whose
physical transverse thermal band violates its genuine residual lower bound.
No conditional pressure, independence or moment premise remains. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalLatitudeChartKacRice SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.SphericalSequentialRegression
open scoped Topology ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem qStar_actual_bad_thermal_critical_count (μ : FiniteMixture)
    (hscope : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi ∨ 3≤μ.minDegree)
    {β ε : ℝ} (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hε : 0<ε)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (hab : latitudeCurvatureVariance
        (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q)
    (L U K Z : ℝ) {g : ℝ} (hg : 0<g)
    (hK : 2*Real.sqrt (latitudeCurvatureVariance
      (centerCoefficients (mixtureCoefficients μ) (Thresholds.qStar μ.xi β)) q)+g≤K) :
    let Q := Thresholds.qStar μ.xi β
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
    let S := rectangularScoreWindow (Icc L U) (Icc K Z)
    ∃ η : ℝ,0<η ∧ ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ z,inner ℝ (e z) w=0) →
      (∫⁻ J,actualLatitudeSphereCount c w e q
        (fun J y => if actualLatitudeScore c w e q J y∈S ∧
          transverseRemainderPressure c w e q Q β J y<F-ε then 1 else 0) J
            ∂disorderLaw (n+3) μ.maxDegree)≤ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
  obtain ⟨γ,hγ,hpost⟩ := qStar_posterior_transverse_pressure_exponential μ hscope hβ hε
  have hcount := latitude_actual_bad_count_eventually_exponential μ
    (μ.qStar_solves_plateau hβ).1.1 hq0 hq1 hab L U K Z hg hγ hK
  refine ⟨γ/4,by positivity,?_⟩
  filter_upwards [hcount,(tendsto_add_atTop_nat 1).eventually hpost] with n hn hp
  intro w hw e he
  let E : Set (Disorder (n+3) μ.maxDegree × Vector (n+2)) :=
    {p | transverseRemainderPressure c w e q Q β p.1 p.2<F-ε}
  have hE : MeasurableSet E := measurableSet_transverseRemainder_bad c w e q Q β (F-ε)
  apply hn w hw e he E hE
  intro y hy z _
  have hh := hp w hw e he q hq1.le y hy (jointScoreTarget (n+1) (((n+3 : ℕ) : ℝ) • z))
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at ht
  exact ht

end
end SlowEquilibration.SphericalTaylorRemainder
