-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCountPrefactors

/-! Uniform multiplicative bounds for literal expected critical counts in
arbitrary measurable score windows, including dimension-dependent windows. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory Set
open SphericalModel SphericalGaussianJet SphericalSequentialRegression
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma lintegral_ofReal_const_mul {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (a : ℝ) (ha : 0 ≤ a) (f : X → ℝ) :
    (∫⁻ x, ENNReal.ofReal (a * f x) ∂ν) =
      ENNReal.ofReal a * ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  simp_rw [ENNReal.ofReal_mul ha]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The ambient factor `N` is exact because both scores in the actual count
window are normalized by `N`. Constants are independent of the window and dimension. -/
theorem actual_mixed_window_prefactors (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) {g Z : ℝ} (hg : 0 < g) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
      (∀ z ∈ K, z 1 ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z) →
      let a := centerCoefficients (mixtureCoefficients μ) Q
      ENNReal.ofReal (c * (n+2 : ℕ)) *
        (∫⁻ z in K, ENNReal.ofReal (Real.exp ((n+2 : ℕ) * markedComplexity μ Q z))) ≤
          (∫⁻ J, actualScoreWindowCount (n+1) a K (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualScoreWindowCount (n+1) a K (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (C * (n+2 : ℕ)) *
          ∫⁻ z in K, ENNReal.ofReal (Real.exp ((n+2 : ℕ) * markedComplexity μ Q z)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := actual_mixed_intensity_prefactors μ hQ hnp (Z := Z) hg
  refine ⟨c,C,hc,hC,?_⟩
  intro n K hK hgap
  dsimp only
  rw [actual_mixed_count_intensity n μ hQ hnp K hK,
    ← lintegral_ofReal_const_mul _ _ (mul_nonneg hc.le (by positivity)),
    ← lintegral_ofReal_const_mul _ _ (mul_nonneg hC.le (by positivity))]
  exact ⟨setLIntegral_mono' hK (fun z hz => (hbound n z (hgap z hz)).1),
    setLIntegral_mono' hK (fun z hz => (hbound n z (hgap z hz)).2)⟩

/-- The pure count has the exact square-root dimension factor and is
integrated on its genuine one-dimensional score support. -/
theorem actual_pure_window_prefactors
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) {g Z : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
      (∀ h ∈ pureScoreWindow p K, (p:ℝ)*h ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z) →
      let a := centerCoefficients (mixtureCoefficients μ) Q
      ENNReal.ofReal (c * Real.sqrt (n+2 : ℕ)) *
        (∫⁻ h in pureScoreWindow p K, ENNReal.ofReal
          (Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h))) ≤
        (∫⁻ J, actualScoreWindowCount (n+1) a K (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualScoreWindowCount (n+1) a K (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (C * Real.sqrt (n+2 : ℕ)) *
          ∫⁻ h in pureScoreWindow p K, ENNReal.ofReal
            (Real.exp ((n+2 : ℕ) * pureMarkedComplexity p hp alpha halpha Q h)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := actual_pure_intensity_prefactors p hp alpha halpha hQ (Z := Z) hg
  refine ⟨c,C,hc,hC,?_⟩
  intro n K hK hgap
  dsimp only
  rw [actual_pure_count_intensity n p hp alpha halpha hQ K hK,
    ← lintegral_ofReal_const_mul _ _ (mul_nonneg hc.le (by positivity)),
    ← lintegral_ofReal_const_mul _ _ (mul_nonneg hC.le (by positivity))]
  have hI := pureScoreWindow_measurable p K hK
  exact ⟨setLIntegral_mono' hI (fun h hh => (hbound n h (hgap h hh)).1),
    setLIntegral_mono' hI (fun h hh => (hbound n h (hgap h hh)).2)⟩

end
end SlowEquilibration.SphericalMarkedWindows
