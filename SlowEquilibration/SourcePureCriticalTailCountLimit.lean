-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalWindowComparison
public import SlowEquilibration.SourcePureLocalMaxNormalizedLimits

/-! The source pure all-critical expected upper tail has the same exact
centered exponential limit as the negative-Hessian local maxima. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering GOEMaximumDeterminant
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 650000

theorem sourcePure_truncatedCritical_tail_relative_comparison
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      ∀ H : ℝ,
        tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) H ≤
          tail (sourcePureTruncatedCriticalDensity n p hp a ha Q
            ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) H ∧
        tail (sourcePureTruncatedCriticalDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) H ≤
          (1+C*Real.exp (-c*(n+2 : ℕ)))*
            tail (pureTruncatedLocalMaxDensity n p hp a ha Q
              ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) H := by
  obtain ⟨C,c,hC,hc,hComp⟩ :=
    sourcePure_critical_localMax_physical_comparison p hp a ha
      h.overlap_range.1 hg hLeft hRight
  refine ⟨C,c,hC,hc,?_⟩
  have hInt := pureTruncatedLocalMaxDensity_integrable_eventually
    p hp a ha h (hm.1.trans hm.2) hg hLeft hRight
  filter_upwards [hComp,hInt] with n hn hmax
  let d : ℝ := 1+C*Real.exp (-c*(n+2 : ℕ))
  let fmax : ℝ → ℝ := pureTruncatedLocalMaxDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  let fcrit : ℝ → ℝ := sourcePureTruncatedCriticalDensity n p hp a ha Q
    ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hpoint : ∀ H, 0 ≤ fmax H ∧ fmax H ≤ fcrit H ∧ fcrit H ≤ d*fmax H := by
    intro H
    by_cases hH : H ∈ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
    · simp only [fmax, fcrit, pureTruncatedLocalMaxDensity,
        sourcePureTruncatedCriticalDensity, indicator_of_mem hH]
      have hlo := pureLocalMaxPhysicalIntensity_le_critical_all_dimensions
        n p hp a ha Q H
      exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono
        (pureCriticalPhysicalIntensity_ne_top n p hp a ha Q H) hlo, hn H hH⟩
    · simp only [fmax, fcrit, pureTruncatedLocalMaxDensity,
        sourcePureTruncatedCriticalDensity, indicator_of_notMem hH]
      exact ⟨by simp, by simp, by simp⟩
  have hmeas : Measurable fcrit :=
    ((pureCriticalPhysicalIntensity_measurable n p hp a ha Q).ennreal_toReal).indicator
      measurableSet_Ioo
  have hcInt : Integrable fcrit := by
    apply (hmax.const_mul d).mono' hmeas.aestronglyMeasurable
    exact ae_of_all _ (fun H => by
      rw [Real.norm_of_nonneg ((hpoint H).1.trans (hpoint H).2.1)]
      exact (hpoint H).2.2)
  intro H
  change (∫ z in Ici H, fmax z) ≤ (∫ z in Ici H, fcrit z) ∧
    (∫ z in Ici H, fcrit z) ≤ d*(∫ z in Ici H, fmax z)
  constructor
  · exact integral_mono_ae hmax.integrableOn hcInt.integrableOn
      (ae_of_all _ fun z => (hpoint z).2.1)
  · calc
      (∫ z in Ici H, fcrit z) ≤ ∫ z in Ici H, d*fmax z :=
        integral_mono_ae hcInt.integrableOn (hmax.const_mul d).integrableOn
          (ae_of_all _ fun z => (hpoint z).2.2)
      _ = d*(∫ z in Ici H, fmax z) := integral_const_mul d fmax

/-- The true all-critical pure intensity has the exact centered upper-tail
mean for every fixed threshold, under the source unit-tail center. -/
theorem sourcePure_truncatedCritical_normalized_tail_limit_of_center
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {l r g Z : ℝ}
    (hm : markE (FiniteMixture.pure p hp a ha) β x Q ∈ Ioo l r)
    (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤ (p : ℝ)*l)
    (hRight : (p : ℝ)*r ≤ Z)
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
    (hcenter : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n)=1 ∧
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M)
    (t : ℝ) :
    Tendsto (fun n : ℕ =>
      tail (sourcePureTruncatedCriticalDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n+t))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  obtain ⟨C,c,hC,hc,hComp⟩ :=
    sourcePure_truncatedCritical_tail_relative_comparison p hp a ha h hm hg hLeft hRight
  have hMax := (sourcePure_truncatedLocalMax_normalized_limits_of_center
    p hp a ha h hm hg hLeft hRight m hM hcenter).2 t
  have hDim : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hExp : Tendsto (fun n : ℕ => Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp (hDim.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hFactor : Tendsto (fun n => 1+C*Real.exp (-c*(n+2 : ℕ)))
      atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hExp))
  have hUpper : Tendsto (fun n =>
      (1+C*Real.exp (-c*(n+2 : ℕ)))*
        tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n+t))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    simpa only [one_mul] using hFactor.mul hMax
  have hBounds : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n+t) ≤
      tail (sourcePureTruncatedCriticalDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n+t) ∧
      tail (sourcePureTruncatedCriticalDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n+t) ≤
        (1+C*Real.exp (-c*(n+2 : ℕ)))*
          tail (pureTruncatedLocalMaxDensity n p hp a ha Q
            ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) (m n+t) := by
    filter_upwards [hComp] with n hn
    exact hn (m n+t)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hMax hUpper
    (hBounds.mono fun _ hn => hn.1) (hBounds.mono fun _ hn => hn.2)

end SlowEquilibration.SphericalMarkedWindows
