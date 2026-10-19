-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCriticalWindowCardMean

/-! Source 11.13's ordinary real second-moment inequality for the same
literal retained count, center and selection parameters as the canonical
variance theorem. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice SphericalForm
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem source_second_moment_of_variance_bound
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (a err k : ℝ)
    (hX : MemLp X 2 ν) (hMean : (∫ ω, X ω ∂ν) = a)
    (hVar : ProbabilityTheory.variance X ν ≤ err*a^2+k*a) :
    (∫ ω, X ω^2 ∂ν) ≤ (1+err)*a^2+k*a := by
  rw [ProbabilityTheory.variance_eq_sub hX,hMean] at hVar
  simp only [Pi.pow_apply] at hVar
  nlinarith

/-- The printed mixed retained-count mean, second moment, and variance are
all obtained from the actual selected critical set without supplied moment
or pair bounds. One choice of center and filter works for every fixed
physical energy window. -/
theorem source_mixed_actual_retained_canonical_window_second_moment
    (μ : FiniteMixture) {β x Q δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) :
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ C cut η ε L R : ℝ,
      0 < C ∧ 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 hd ∧
      0 < η ∧ η ≤ sourceCriticalCollarOverlapLoss (g/2) C ∧
      0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧ sourceRadialEdge μ Q < L ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        ∀ {α : ℝ}, 1/4 < α → α < 1/2 →
          ∃ D : ℝ, 0 < D ∧
          ∀ a b : ℝ, a < b →
            let G := gap μ Q (markY β Q) (markZ x Q) ε η
            let K n := physicalEnergyWindow (n+3)
              (Icc (d.center (n+1)+a) (d.center (n+1)+b)) (Ioo L R)
            let aN n := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
              (g/2) C ε η E G
            let X n J := (sourceRetainedScoreWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) (K n)
              (g/2) C ε η E G J).toReal
            Tendsto aN atTop
              (𝓝 (Real.exp (-(β*x)*a)-Real.exp (-(β*x)*b))) ∧
              ∀ᶠ n : ℕ in atTop,
                (∫ J, (X n J)^2 ∂disorderLaw (n+3) μ.maxDegree) ≤
                  (1+D*sourcePrintedPairError α n)*(aN n)^2+
                    (1+(1-ε)/(cut^2-ε))*aN n ∧
                ProbabilityTheory.variance (X n)
                  (disorderLaw (n+3) μ.maxDegree) ≤
                  D*sourcePrintedPairError α n*(aN n)^2+
                    (1+(1-ε)/(cut^2-ε))*aN n ∧
                MemLp (X n) 2 (disorderLaw (n+3) μ.maxDegree) := by
  dsimp only
  obtain ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hall⟩ :=
    source_mixed_actual_retained_canonical_window_variance μ h hnp hd hδMax
  refine ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,?_⟩
  intro α hα hHalf
  obtain ⟨D,hD,hwindow⟩ := hall hα hHalf
  refine ⟨D,hD,?_⟩
  intro a b hab
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let K (n : ℕ) := physicalEnergyWindow (n+3)
    (Icc (d.center (n+1)+a) (d.center (n+1)+b)) (Ioo L R)
  let aN (n : ℕ) := sourceRetainedScoreWindowMean (n+2) μ Q (K n)
    (g/2) C ε η E G
  let X (n : ℕ) (J : Disorder (n+3) μ.maxDegree) :=
    (sourceRetainedScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) (K n)
      (g/2) C ε η E G J).toReal
  refine ⟨(hwindow a b hab).1,?_⟩
  filter_upwards [(hwindow a b hab).2] with n hn
  have hK : MeasurableSet (K n) := rectangularScoreWindow_measurable _ _
    (measurableSet_Icc.preimage (measurable_const_mul ((n+3:ℕ):ℝ))) measurableSet_Ioo
  have hMean : (∫ J, X n J ∂disorderLaw (n+3) μ.maxDegree) = aN n :=
    source_actual_retained_count_expectation_eq_mean (n+2) (by omega)
      μ h.overlap_range.1 hnp (K n) hK (g/2) C ε η E G
  exact ⟨source_second_moment_of_variance_bound
      (disorderLaw (n+3) μ.maxDegree) (X n) (aN n)
      (D*sourcePrintedPairError α n) (1+(1-ε)/(cut^2-ε))
      hn.2 hMean hn.1,hn⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
