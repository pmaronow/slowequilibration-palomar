-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeBadMarkedCounts
public import SlowEquilibration.SphericalLatitudeCompactCount

@[expose] public section

/-! Exponential posterior bad-event probabilities remain exponential after
actual strong-field critical-point counting. All dimension thresholds are
uniform in the physical axis, frame and measurable full-field event. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Classical
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalMarkedWindows SlowEquilibration.StrongFieldComplexity
open scoped ENNReal Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_actual_bad_count_eventually_exponential (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (hab : latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q <
      latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q)
    (L U K Z : ℝ) {g γ : ℝ} (hg : 0<g) (hγ : 0<γ)
    (hK : 2*Real.sqrt (latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q)+g≤K) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let S := rectangularScoreWindow (Icc L U) (Icc K Z)
    ∀ᶠ n : ℕ in atTop,∀ (w : Vector (n+3)),‖w‖^2=((n+3 : ℕ) : ℝ) →
      ∀ (e : Vector (n+2) →ₗᵢ[ℝ] Vector (n+3)),(∀ x,inner ℝ (e x) w=0) →
      ∀ E : Set (Disorder (n+3) μ.maxDegree × Vector (n+2)),MeasurableSet E →
      (∀ (y : Vector (n+2)) (hy : ‖y‖^2=((n+2 : ℕ) : ℝ)) (z : EuclideanSpace ℝ (Fin 2)),z∈S →
        (latitudeNormalizedPosterior μ Q w e q y hy z).real {J | (J,y)∈E}≤
          Real.exp (-γ*((n+3 : ℕ) : ℝ))) →
      (∫⁻ J,actualLatitudeSphereCount c w e q
        (fun J y => if actualLatitudeScore c w e q J y∈S ∧ (J,y)∈E then 1 else 0) J
          ∂disorderLaw (n+3) μ.maxDegree)≤ENNReal.ofReal (Real.exp (-(γ/4)*((n+3 : ℕ) : ℝ))) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let S := rectangularScoreWindow (Icc L U) (Icc K Z)
  obtain ⟨C,hC,hbad⟩ := latitude_actual_bad_mark_count_bound μ hQ hq0 hq1 (Z := Z) hg
  have hcount := latitude_actual_compact_count_subexponential μ hQ hq0 hq1 hab L U K Z
    (show 0<γ/8 by positivity)
  have hdim : ∀ᶠ n : ℕ in atTop,polynomialAbsorptionThreshold (Real.sqrt C) 0 (γ/8)≤((n+3 : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop (Nat.ceil (polynomialAbsorptionThreshold (Real.sqrt C) 0 (γ/8)))] with n hn
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (polynomialAbsorptionThreshold (Real.sqrt C) 0 (γ/8))≤n+3 by omega))
  filter_upwards [hcount,hdim] with n hn hdim
  intro w hw e he E hE hprob
  have hS : MeasurableSet S := rectangularScoreWindow_measurable _ _ measurableSet_Icc measurableSet_Icc
  have hrad : ∀ z∈S,2*Real.sqrt (latitudeCurvatureVariance c q)+g≤z 1 ∧ z 1≤Z := by
    intro z hz
    exact ⟨hK.trans hz.2.1,hz.2.2⟩
  have hb := hbad n w hw e he S hS hrad E hE (Real.exp (-γ*((n+3 : ℕ) : ℝ))) hprob
  apply hb.trans
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt C*Real.sqrt (Real.exp (-γ*((n+3 : ℕ) : ℝ))))*
        ENNReal.ofReal (Real.exp ((γ/8)*((n+3 : ℕ) : ℝ))) := by
      gcongr
      exact hn w hw e he
    _ ≤ _ := ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hp := polynomial_le_exp_of_threshold 0 (Real.sqrt_nonneg C) (show 0<γ/8 by positivity) hdim
  simp only [pow_zero,mul_one] at hp
  have hsq : (Real.exp (-γ*((n+3 : ℕ) : ℝ)/2))^2=Real.exp (-γ*((n+3 : ℕ) : ℝ)) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [← hsq,Real.sqrt_sq (Real.exp_pos _).le]
  calc
    _ ≤ (Real.exp ((γ/8)*((n+3 : ℕ) : ℝ))*Real.exp (-γ*((n+3 : ℕ) : ℝ)/2))*
        Real.exp ((γ/8)*((n+3 : ℕ) : ℝ)) := by gcongr
    _ = _ := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring

end
end SlowEquilibration.SphericalLatitudeChartKacRice
