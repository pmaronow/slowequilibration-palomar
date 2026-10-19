-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorBadCriticalCount
public import SlowEquilibration.SphericalLatitudeBadCriticalProbability

@[expose] public section

/-! Actual exponential probability of any bad thermal critical point in an
exterior score window, obtained from its genuine marked critical count. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalLatitudeChartKacRice SlowEquilibration.SphericalMarkedWindows
open SlowEquilibration.SphericalSequentialRegression SlowEquilibration.SphericalForm
open scoped Topology ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem qStar_bad_thermal_critical_probability (μ : FiniteMixture)
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
      disorderLaw (n+3) μ.maxDegree
        {J | ∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
          surfaceGradient (latitudeField c J w e q) y=0 ∧
          actualLatitudeScore c w e q J y∈S ∧
          transverseRemainderPressure c w e q Q β J y<F-ε}≤
        ENNReal.ofReal (Real.exp (-η*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let Q := Thresholds.qStar μ.xi β
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let F := (β^2*(μ.xi 1-μ.xi Q)-Q)/2
  let S := rectangularScoreWindow (Icc L U) (Icc K Z)
  have hQ : 0<Q := (μ.qStar_solves_plateau hβ).1.1
  have hc : ∀ p,0≤c p := centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le
  have hfirst : 0<firstCovariance c 1 := by
    dsimp only [c]
    rw [firstCovariance_center,firstCovariance_mixture]
    exact mul_pos hQ (μ.xi1_pos hQ)
  obtain ⟨η,hη,hcount⟩ := qStar_actual_bad_thermal_critical_count μ hscope hβ hε hq0 hq1 hab L U K Z hg hK
  refine ⟨η,hη,?_⟩
  filter_upwards [hcount] with n hn
  intro w hw e he
  let E : Set (Disorder (n+3) μ.maxDegree × Vector (n+2)) :=
    {p | actualLatitudeScore c w e q p.1 p.2∈S ∧
      transverseRemainderPressure c w e q Q β p.1 p.2<F-ε}
  have hS : MeasurableSet S := rectangularScoreWindow_measurable _ _ measurableSet_Icc measurableSet_Icc
  have hscore : Measurable (fun p : Disorder (n+3) μ.maxDegree × Vector (n+2) =>
      actualLatitudeScore c w e q p.1 p.2) :=
    (latitudeScore_jointContinuous c w e q).measurable.const_smul (((n+3 : ℕ) : ℝ)⁻¹)
  have hE : MeasurableSet E := (hS.preimage hscore).inter
    (measurableSet_transverseRemainder_bad c w e q Q β (F-ε))
  let psi : Disorder (n+3) μ.maxDegree → Vector (n+2) → ℝ≥0∞ :=
    fun J y => if actualLatitudeScore c w e q J y∈S ∧
      transverseRemainderPressure c w e q Q β J y<F-ε then 1 else 0
  let C := actualLatitudeSphereCount c w e q psi
  have hpsi : Measurable (fun p : Disorder (n+3) μ.maxDegree × Vector (n+2) => psi p.1 p.2) :=
    Measurable.ite hE measurable_const measurable_const
  have hC : AEMeasurable C (disorderLaw (n+3) μ.maxDegree) :=
    (actual_latitude_sphere_marked_kacRice (by omega) c hc hfirst w hw e he hq1 psi hpsi).1
  have hsub : {J : Disorder (n+3) μ.maxDegree | ∃ y,‖y‖^2=((n+2 : ℕ) : ℝ) ∧
      surfaceGradient (latitudeField c J w e q) y=0 ∧
      actualLatitudeScore c w e q J y∈S ∧ transverseRemainderPressure c w e q Q β J y<F-ε}⊆
      {J | 1≤C J} := by
    rintro J ⟨y,hy,hcrit,hscorey,hbad⟩
    have ht := ENNReal.le_tsum (f := fun z : {z : Vector (n+2) | ‖z‖^2=((n+2 : ℕ) : ℝ) ∧
        surfaceGradient (latitudeField c J w e q) z=0} => psi J z) ⟨y,hy,hcrit⟩
    have hvalue : psi J y=1 := ite_eq_left ⟨hscorey,hbad⟩
    rw [hvalue] at ht
    exact ht
  have hm : disorderLaw (n+3) μ.maxDegree {J | 1≤C J}≤∫⁻ J,C J ∂disorderLaw (n+3) μ.maxDegree := by
    simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hC 1
  exact ((measure_mono hsub).trans hm).trans (hn w hw e he)

/-- A good actual critical point gives the stated physical band pressure,
with bottom energy and thermal residual both in their original normalizations. -/
theorem good_critical_transverseBandPressure_lower {n : ℕ} (hn : 1≤n)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q) {β L T : ℝ} (hβ : 0≤β)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2))
    {q : ℝ} (hq : |q|<1) (J : Disorder (n+2) μ.maxDegree)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (hcrit : surfaceGradient (latitudeField (centerCoefficients (mixtureCoefficients μ) Q) J w e q) y=0)
    (hheight : L≤actualLatitudeScore (centerCoefficients (mixtureCoefficients μ) Q) w e q J y 0)
    (hthermal : T≤transverseRemainderPressure (centerCoefficients (mixtureCoefficients μ) Q) w e q Q β J y) :
    β*L+T≤transverseBandPressure μ w e q Q β J y := by
  rw [latitude_critical_transverseBandPressure_identity hn μ hQ w e hq β J y hy hcrit]
  rw [actualLatitudeScore_zero] at hheight
  have hh := mul_le_mul_of_nonneg_left hheight hβ
  rw [← mul_div_assoc] at hh
  exact add_le_add hh hthermal

end
end SlowEquilibration.SphericalTaylorRemainder
