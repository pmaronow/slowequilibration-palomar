-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureUniformComplexity

/-! Actual expected score-window counts bounded by the complexity integrals. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Filter Set Function
open SphericalModel SphericalGaussianJet SphericalSequentialRegression
open GOEPhysicalPotential GOEPhysicalNormalizedMoments
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma ennreal_exp_bounds_of_log_rate {d : ℝ≥0∞} {N T ε : ℝ}
    (hN : 0 < N) (hd : 0 < d.toReal) (h : |Real.log d.toReal / N - T| < ε) :
    ENNReal.ofReal (Real.exp (N * (T-ε))) ≤ d ∧
      d ≤ ENNReal.ofReal (Real.exp (N * (T+ε))) := by
  have htop : d ≠ ⊤ := by intro he; simp only [he, ENNReal.toReal_top] at hd; exact lt_irrefl _ hd
  have he := ENNReal.ofReal_toReal htop
  have hl : N * (T-ε) ≤ Real.log d.toReal := by
    have hh : T-ε < Real.log d.toReal / N := by linarith [(abs_lt.mp h).1]
    have ht := (lt_div_iff₀ hN).mp hh
    nlinarith
  have hu : Real.log d.toReal ≤ N * (T+ε) := by
    have hh : Real.log d.toReal / N < T+ε := by linarith [(abs_lt.mp h).2]
    have ht := (div_lt_iff₀ hN).mp hh
    nlinarith
  constructor
  · have hh := Real.exp_le_exp.mpr hl
    rw [Real.exp_log hd] at hh
    exact (ENNReal.ofReal_le_ofReal hh).trans_eq he
  · have hh := Real.exp_le_exp.mpr hu
    rw [Real.exp_log hd] at hh
    exact he.symm.trans_le (ENNReal.ofReal_le_ofReal hh)

lemma mixedCriticalIntensity_toReal_pos (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < z 1) :
    0 < (mixedCriticalIntensity n μ Q z).toReal := by
  have hm := physicalMean_pos n 1 (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hz
  rw [mixedCriticalIntensity, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.le]
  exact mul_pos (mul_pos (ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ hQ)
    (sphereKRPrefactor_ne_top (n+1) μ Q))
    (physicalScorePdf_toReal_pos (n+2) (by omega) μ hQ hnp z)) hm

lemma pureCriticalIntensity_toReal_pos (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q) (h : ℝ)
    (hh : 2 * Real.sqrt (Q^2 * (FiniteMixture.pure p hp alpha halpha).xi2 Q) < (p:ℝ)*h) :
    0 < (pureCriticalIntensity n p hp alpha halpha Q h).toReal := by
  let μ := FiniteMixture.pure p hp alpha halpha
  have hm := physicalMean_pos n 1 (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hh
  rw [pureCriticalIntensity, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hm.le]
  exact mul_pos (mul_pos (ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ hQ)
    (sphereKRPrefactor_ne_top (n+1) μ Q))
    (physicalValuePdf_toReal_pos (n+2) (by omega) μ hQ h)) hm

/-- Genuine exponential complexity bounds for the expected literal mixed
critical count. The dimension threshold is uniform in every Borel score window
inside the fixed radial gap interval, including dimension-dependent windows. -/
theorem actual_mixed_window_complexity_bounds (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    {g Z ε : ℝ} (hg : 0 < g) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
      (∀ z ∈ K, z 1 ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z) →
      let c := centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ z in K, ENNReal.ofReal (Real.exp ((n+2 : ℕ) * (markedComplexity μ Q z - ε)))) ≤
        (∫⁻ J, actualScoreWindowCount (n+1) c K (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualScoreWindowCount (n+1) c K (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ∫⁻ z in K, ENNReal.ofReal (Real.exp ((n+2 : ℕ) * (markedComplexity μ Q z + ε))) := by
  filter_upwards [actual_mixed_complexity_uniform μ hQ hnp hg hε] with n hn
  intro K hK hgap
  dsimp only
  rw [actual_mixed_count_intensity n μ hQ hnp K hK]
  have hb (z) (hz : z ∈ K) := ennreal_exp_bounds_of_log_rate (by positivity : (0:ℝ)<(n+2 : ℕ))
    (mixedCriticalIntensity_toReal_pos n μ hQ hnp z (by linarith [(hgap z hz).1]))
    (hn z (hgap z hz))
  exact ⟨setLIntegral_mono' hK (fun z hz => (hb z hz).1),
    setLIntegral_mono' hK (fun z hz => (hb z hz).2)⟩

/-- The pure expected-count counterpart uses only the scalar density and
the exact support window `{h | (h,p*h)∈K}`. -/
theorem actual_pure_window_complexity_bounds
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) {g Z ε : ℝ} (hg : 0 < g) (hε : 0 < ε) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∀ᶠ n : ℕ in atTop, ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
      (∀ h ∈ pureScoreWindow p K, (p:ℝ)*h ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z) →
      let c := centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ h in pureScoreWindow p K, ENNReal.ofReal
        (Real.exp ((n+2 : ℕ) * (pureMarkedComplexity p hp alpha halpha Q h - ε)))) ≤
        (∫⁻ J, actualScoreWindowCount (n+1) c K (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualScoreWindowCount (n+1) c K (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ∫⁻ h in pureScoreWindow p K, ENNReal.ofReal
          (Real.exp ((n+2 : ℕ) * (pureMarkedComplexity p hp alpha halpha Q h + ε))) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  filter_upwards [actual_pure_complexity_uniform p hp alpha halpha hQ hg hε] with n hn
  intro K hK hgap
  dsimp only
  rw [actual_pure_count_intensity n p hp alpha halpha hQ K hK]
  have hb (h) (hh : h ∈ pureScoreWindow p K) :=
    ennreal_exp_bounds_of_log_rate (by positivity : (0:ℝ)<(n+2 : ℕ))
      (pureCriticalIntensity_toReal_pos n p hp alpha halpha hQ h (by linarith [(hgap h hh).1]))
      (hn h (hgap h hh))
  have hI := pureScoreWindow_measurable p K hK
  exact ⟨setLIntegral_mono' hI (fun h hh => (hb h hh).1),
    setLIntegral_mono' hI (fun h hh => (hb h hh).2)⟩

end
end SlowEquilibration.SphericalMarkedWindows
