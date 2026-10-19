-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedActualTailLimit

/-! Source §11.13--11.14 pure expected upper-tail counts: one exact
unit-tail center, selected before every fixed threshold, works for the
original local-max, all-critical raw-score and retained counts. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering LatitudeGroundTrial
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem source_pure_actual_upper_tail_all_counts
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ n₀ : ℕ, ∃ m : ℕ → ℝ, ∃ M C η ε δ : ℝ,
      0 < M ∧ 0 < δ ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p : ℝ)*(E-δ) ∧
      (p : ℝ)*δ < 1 ∧
      (∀ n < n₀, m n=(n+2 : ℕ)*E) ∧
      (∀ n ≥ n₀,
        tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) (m n)=1 ∧
        (∀ y : ℝ, tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) y=1 → y=m n) ∧
        |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M) ∧
      let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
      let G := gap μ Q (markY β Q) (markZ x Q) ε η
      ∀ t : ℝ,
        Tendsto (fun n : ℕ =>
          sourcePureTruncatedLocalMaxTailMean (n+1) p hp a ha Q
            (E-δ) (E+δ) (m (n+1)+t))
          atTop (𝓝 (Real.exp (-(β*x)*t))) ∧
        Tendsto (fun n : ℕ =>
          (∫⁻ J, actualScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            {b : EuclideanSpace ℝ (Fin 2) |
              b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧ b 1 ∈ U}
            (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal)
          atTop (𝓝 (Real.exp (-(β*x)*t))) ∧
        Tendsto (fun n : ℕ =>
          sourceRetainedValueWindowMean (n+2) μ Q
            (sourcePureCenteredUpperTailNormalizedWindow n m E δ t)
            (g/2) C ε η E G)
          atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  obtain ⟨n₀,m,M,C,cut,η,ε,δ,C₂,D,hM,hδ,hpδ,hLeft,hC,hcut,hcutOne,
    hη,hε,hεCut,hεη,hC₂,hD,
    hFallback,hCenter,hUnfiltered,hMean,hMoments⟩ :=
    source_pure_actual_retained_center_narrow_radial p hp a ha h
  refine ⟨n₀,m,M,C,η,ε,δ,hM,hδ,hLeft,hpδ,hFallback,hCenter,?_⟩
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hg : 0 < g := by
    have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
      simpa only [markB] using h.edge_margin.2.2
    exact div_pos hedge (by norm_num)
  have hcenterSharp : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) (m n)=1 ∧
      |m n-((n+2 : ℕ)*E-Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M := by
    filter_upwards [eventually_ge_atTop n₀] with n hn
    exact ⟨(hCenter n hn).1,(hCenter n hn).2.2⟩
  have hm : E ∈ Ioo (E-δ) (E+δ) := by constructor <;> dsimp [E] <;> linarith
  intro t
  have hMaxDensity :=
    (sourcePure_truncatedLocalMax_normalized_limits_of_center p hp a ha h
      hm hg hLeft le_rfl m hM hcenterSharp).2 t
  have hMaxShift := hMaxDensity.comp (tendsto_add_atTop_nat 1)
  have hMaxActual : Tendsto (fun n : ℕ =>
      sourcePureTruncatedLocalMaxTailMean (n+1) p hp a ha Q
        (E-δ) (E+δ) (m (n+1)+t))
      atTop (𝓝 (Real.exp (-(β*x)*t))) := by
    apply hMaxShift.congr'
    exact Filter.Eventually.of_forall fun n => by
      change tail (pureTruncatedLocalMaxDensity (n+1) p hp a ha Q
        ((n+1+2 : ℕ)*(E-δ)) ((n+1+2 : ℕ)*(E+δ))) (m (n+1)+t) = _
      exact (sourcePureTruncatedLocalMaxTailMean_eq_tail (n+1) p hp a ha
        h.overlap_range.1 (E-δ) (E+δ) (m (n+1)+t)).symm
  have hRaw := sourcePure_actual_raw_score_upper_tail_mean_limit_of_center
    p hp a ha h hδ hg hLeft m hM hcenterSharp t
  have hRet := source_pure_actual_retained_upper_tail_mean_limit_of_center
    p hp a ha h hδ hg hLeft m hM hcenterSharp
    (g/2) C ε η G hMean t
  exact ⟨hMaxActual,hRaw,hRet⟩

end SlowEquilibration.PairConditionalDeterminantMoments
