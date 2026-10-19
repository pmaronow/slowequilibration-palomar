-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedRawScoreTailLimit

/-! The source proper-pure upper-tail statement with one exact center
and literal original energy/radial-score counts, selected before t. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open SphericalMarkedWindows TwoAtomStationarity SphericalTAPCertificate
open ExpectedTailCentering LatitudeGroundTrial
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem source_pure_actual_upper_tail_score_complete
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ m : ℕ → ℝ, ∃ M C η ε δ : ℝ,
      0 < M ∧ 0 < δ ∧
      (∀ᶠ n : ℕ in atTop,
        tail (pureTruncatedLocalMaxDensity n p hp a ha Q
          ((n+2 : ℕ)*(E-δ)) ((n+2 : ℕ)*(E+δ))) (m n)=1 ∧
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
          atTop (𝓝 (Real.exp (-(β*x)*t))) ∧
        Tendsto (fun n : ℕ =>
          (∫⁻ J, sourceRetainedScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            {b : EuclideanSpace ℝ (Fin 2) |
              b 0 ∈ sourcePureCenteredRawUpperTailNormalizedWindow n m t ∧ b 1 ∈ U}
            (g/2) C ε η E G J ∂disorderLaw (n+3) μ.maxDegree).toReal)
          atTop (𝓝 (Real.exp (-(β*x)*t))) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  obtain ⟨n₀,m,M,C,η,ε,δ,hM,hδ,hLeft,hpδ,hFallback,hCenter,hTail⟩ :=
    source_pure_actual_upper_tail_all_counts p hp a ha h
  refine ⟨m,M,C,η,ε,δ,hM,hδ,?_,?_⟩
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    exact ⟨(hCenter n hn).1,(hCenter n hn).2.2⟩
  intro t
  obtain ⟨hMax,hRaw,hRet⟩ := hTail t
  have hRetRaw := sourcePureRetainedRawScoreUpperTail_mean_tendsto
    p hp a ha Q E δ m t (g/2) C ε η
    (gap μ Q (markY β Q) (markZ x Q) ε η)
    (Real.exp (-(β*x)*t)) hRet
  exact ⟨hMax,hRaw,hRet,hRetRaw⟩

end SlowEquilibration.PairConditionalDeterminantMoments
