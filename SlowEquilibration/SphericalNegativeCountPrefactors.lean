-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalNegativeCriticalIntensity
public import SlowEquilibration.SphericalWindowPrefactors

/-! Uniform exterior prefactors for the actual negative-Hessian critical
counts. The determinant truncation is proved from Gaussian tails and moments. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalSequentialRegression
open GOEMaximumDeterminant GOEPhysicalPotential
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem mixedNegativeIntensity_comparison (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) {g Z : ℝ} (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, ∀ z : EuclideanSpace ℝ (Fin 2),
      z 1 ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      ENNReal.ofReal (1/2 : ℝ) * mixedCriticalIntensity n μ Q z ≤ mixedNegativeIntensity n μ Q z ∧
      mixedNegativeIntensity n μ Q z ≤ mixedCriticalIntensity n μ Q z := by
  filter_upwards [maximumMean_comparison_eventually (Z := Z)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hg] with n hn
  intro z hz
  obtain ⟨hl,hu⟩ := hn (z 1) hz
  have he : ENNReal.ofReal (1/2 : ℝ) * mixedCriticalIntensity n μ Q z =
      sphereKRPrefactor (n+1) μ Q * physicalScorePdf (n+2) μ Q z *
        ENNReal.ofReal (physicalMean n (n+2) (Q^2*μ.xi2 Q) (z 1)/2) := by
    rw [show physicalMean n (n+2) (Q^2*μ.xi2 Q) (z 1)/2 =
      (1/2:ℝ)*physicalMean n (n+2) (Q^2*μ.xi2 Q) (z 1) by ring,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    unfold mixedCriticalIntensity
    ring
  rw [he]
  exact ⟨mul_le_mul_right (ENNReal.ofReal_le_ofReal hl) _,
    mul_le_mul_right (ENNReal.ofReal_le_ofReal hu) _⟩

theorem pureNegativeIntensity_comparison (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q) {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∀ᶠ n : ℕ in atTop, ∀ h : ℝ,
      (p:ℝ)*h ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      ENNReal.ofReal (1/2 : ℝ) * pureCriticalIntensity n p hp alpha halpha Q h ≤
        pureNegativeIntensity n p hp alpha halpha Q h ∧
      pureNegativeIntensity n p hp alpha halpha Q h ≤ pureCriticalIntensity n p hp alpha halpha Q h := by
  let μ := FiniteMixture.pure p hp alpha halpha
  filter_upwards [maximumMean_comparison_eventually (Z := Z)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hg] with n hn
  intro h hh
  obtain ⟨hl,hu⟩ := hn ((p:ℝ)*h) hh
  have he : ENNReal.ofReal (1/2 : ℝ) * pureCriticalIntensity n p hp alpha halpha Q h =
      sphereKRPrefactor (n+1) μ Q * physicalValuePdf (n+2) μ Q h *
        ENNReal.ofReal (physicalMean n (n+2) (Q^2*μ.xi2 Q) ((p:ℝ)*h)/2) := by
    rw [show physicalMean n (n+2) (Q^2*μ.xi2 Q) ((p:ℝ)*h)/2 =
      (1/2:ℝ)*physicalMean n (n+2) (Q^2*μ.xi2 Q) ((p:ℝ)*h) by ring,
      ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    unfold pureCriticalIntensity
    dsimp only [μ]
    ring
  rw [he]
  exact ⟨mul_le_mul_right (ENNReal.ofReal_le_ofReal hl) _,
    mul_le_mul_right (ENNReal.ofReal_le_ofReal hu) _⟩

theorem actual_mixed_negative_intensity_prefactors (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) {g Z : ℝ} (hg : 0 < g) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ z : EuclideanSpace ℝ (Fin 2),
      z 1 ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      ENNReal.ofReal (c * (n+2 : ℕ) * Real.exp ((n+2 : ℕ) * markedComplexity μ Q z)) ≤
        mixedNegativeIntensity n μ Q z ∧
      mixedNegativeIntensity n μ Q z ≤
        ENNReal.ofReal (C * (n+2 : ℕ) * Real.exp ((n+2 : ℕ) * markedComplexity μ Q z)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := actual_mixed_intensity_prefactors μ hQ hnp (Z := Z) hg
  refine ⟨c/2,C,by positivity,hC,?_⟩
  filter_upwards [mixedNegativeIntensity_comparison μ hQ (Z := Z) hg] with n hn
  intro z hz
  refine ⟨?_, (hn z hz).2.trans (hbound n z hz).2⟩
  have he : ENNReal.ofReal (c/2 * (n+2 : ℕ) * Real.exp ((n+2 : ℕ)*markedComplexity μ Q z)) =
      ENNReal.ofReal (1/2:ℝ) * ENNReal.ofReal (c * (n+2 : ℕ) * Real.exp ((n+2 : ℕ)*markedComplexity μ Q z)) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    congr 1
    ring
  rw [he]
  exact (mul_le_mul_right (hbound n z hz).1 _).trans (hn z hz).1

theorem actual_pure_negative_intensity_prefactors (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q) {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ h : ℝ,
      (p:ℝ)*h ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      ENNReal.ofReal (c * Real.sqrt (n+2 : ℕ) *
        Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h)) ≤
        pureNegativeIntensity n p hp alpha halpha Q h ∧
      pureNegativeIntensity n p hp alpha halpha Q h ≤ ENNReal.ofReal (C * Real.sqrt (n+2 : ℕ) *
        Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := actual_pure_intensity_prefactors p hp alpha halpha hQ (Z := Z) hg
  refine ⟨c/2,C,by positivity,hC,?_⟩
  filter_upwards [pureNegativeIntensity_comparison p hp alpha halpha hQ (Z := Z) hg] with n hn
  intro h hh
  refine ⟨?_, (hn h hh).2.trans (hbound n h hh).2⟩
  have he : ENNReal.ofReal (c/2 * Real.sqrt (n+2 : ℕ) *
      Real.exp ((n+2 : ℕ)*pureMarkedComplexity p hp alpha halpha Q h)) =
      ENNReal.ofReal (1/2:ℝ) * ENNReal.ofReal (c * Real.sqrt (n+2 : ℕ) *
        Real.exp ((n+2 : ℕ)*pureMarkedComplexity p hp alpha halpha Q h)) := by
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
    congr 1
    ring
  rw [he]
  exact (mul_le_mul_right (hbound n h hh).1 _).trans (hn h hh).1

/-- The ambient factor `N` is exact because both scores in the actual count
window are normalized by `N`. Constants are independent of the window and dimension. -/
theorem actual_mixed_negative_window_prefactors (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) {g Z : ℝ} (hg : 0 < g) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
      (∀ z ∈ K, z 1 ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z) →
      let a := centerCoefficients (mixtureCoefficients μ) Q
      ENNReal.ofReal (c * (n+2 : ℕ)) *
        (∫⁻ z in K, ENNReal.ofReal (Real.exp ((n+2 : ℕ) * markedComplexity μ Q z))) ≤
          (∫⁻ J, actualNegativeCriticalCount (n+1) a K J ∂disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualNegativeCriticalCount (n+1) a K J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (C * (n+2 : ℕ)) *
          ∫⁻ z in K, ENNReal.ofReal (Real.exp ((n+2 : ℕ) * markedComplexity μ Q z)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := actual_mixed_negative_intensity_prefactors μ hQ hnp (Z := Z) hg
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound] with n hn
  intro K hK hgap
  dsimp only
  rw [(actual_mixed_negative_count_intensity n μ hQ hnp K hK).2,
    ← lintegral_ofReal_const_mul _ _ (mul_nonneg hc.le (by positivity)),
    ← lintegral_ofReal_const_mul _ _ (mul_nonneg hC.le (by positivity))]
  exact ⟨setLIntegral_mono' hK (fun z hz => (hn z (hgap z hz)).1),
    setLIntegral_mono' hK (fun z hz => (hn z (hgap z hz)).2)⟩

/-- The pure count has the exact square-root dimension factor and is
integrated on its genuine one-dimensional score support. -/
theorem actual_pure_negative_window_prefactors
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
      (∀ h ∈ pureScoreWindow p K, (p:ℝ)*h ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z) →
      let a := centerCoefficients (mixtureCoefficients μ) Q
      ENNReal.ofReal (c * Real.sqrt (n+2 : ℕ)) *
        (∫⁻ h in pureScoreWindow p K, ENNReal.ofReal
          (Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h))) ≤
        (∫⁻ J, actualNegativeCriticalCount (n+1) a K J ∂disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualNegativeCriticalCount (n+1) a K J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (C * Real.sqrt (n+2 : ℕ)) *
          ∫⁻ h in pureScoreWindow p K, ENNReal.ofReal
            (Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := actual_pure_negative_intensity_prefactors p hp alpha halpha hQ (Z := Z) hg
  refine ⟨c,C,hc,hC,?_⟩
  filter_upwards [hbound] with n hn
  intro K hK hgap
  dsimp only
  rw [(actual_pure_negative_count_intensity n p hp alpha halpha hQ K hK).2,
    ← lintegral_ofReal_const_mul _ _ (mul_nonneg hc.le (by positivity)),
    ← lintegral_ofReal_const_mul _ _ (mul_nonneg hC.le (by positivity))]
  have hI := pureScoreWindow_measurable p K hK
  exact ⟨setLIntegral_mono' hI (fun h hh => (hn h (hgap h hh)).1),
    setLIntegral_mono' hI (fun h hh => (hn h (hgap h hh)).2)⟩

end
end SlowEquilibration.SphericalMarkedWindows
