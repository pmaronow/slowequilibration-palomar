-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPurePairFixedSharpBounds
public import SlowEquilibration.SourcePhysicalPairRetainedSquareCollar
public import SlowEquilibration.SourcePhysicalPairPosteriorSphereRegularity

/-! Original proper-pure retained value-window moments with the
posterior regularity cutoff and pair radius fixed before ε, η, α, and
the Borel energy window. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Proper-pure source 11.13 second-moment and variance inequalities for
the literal selected count. The first-moment convergence at the printed
logarithmic center is a separate outstanding pure Kac--Rice asymptotic. -/
theorem source_pure_actual_retained_fixed_window_second_moment
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q δMax : ℝ}
    (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hδMax : 0 < δMax) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ C cut η ε δ : ℝ, 0 < C ∧ 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 h.min_degree ∧
      0 < η ∧ η ≤ sourceCriticalCollarOverlapLoss (g/2) C ∧
      0 < ε ∧ ε < cut^2/2 ∧ ε < 1-η ∧
      let G := gap μ Q (markY β Q) (markZ x Q) ε η
      0 < δ ∧ δ < G/4 ∧ δ ≤ δMax ∧
      ∀ {α : ℝ}, 1/4 < α → α < 1/2 →
        ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
          ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
            let aN := sourceRetainedValueWindowMean (n+2) μ Q I
              (g/2) C ε η E G
            let bN := sourceUnfilteredValueWindowMean (n+2) μ Q I
            let X := fun J => (sourceRetainedValueWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) I
              (g/2) C ε η E G J).toReal
            aN ≤ bN ∧
              (∫ J, X J ∂disorderLaw (n+3) μ.maxDegree) = aN ∧
              MemLp X 2 (disorderLaw (n+3) μ.maxDegree) ∧
              sourceRetainedValueWindowSecondMoment (n+2) μ Q I
                (g/2) C ε η E G ≤
                (1+D*sourcePrintedPairError α n)*aN^2+
                  (1+(1-ε)/(cut^2-ε))*aN ∧
              ProbabilityTheory.variance X
                (disorderLaw (n+3) μ.maxDegree) ≤
                D*sourcePrintedPairError α n*aN^2+
                  (1+(1-ε)/(cut^2-ε))*aN := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let M := |E|+δMax+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMbound : |markE μ β x Q|+δMax+1 ≤ M := le_rfl
  obtain ⟨C,hC,hreg⟩ :=
    source_value_physical_posterior_sphere_regularity μ h.overlap_range.1 hM
  obtain ⟨cut,hcut,hcutOne,hcutRad,hall⟩ :=
    source_pure_actual_retained_sharp_pair_bounds_fixed_mark_box
      p hp a ha h hδMax hC hMbound hreg
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  have hκ : 0 < g/2 := div_pos hg (by norm_num)
  obtain ⟨η,ε,hη,hηCollar,hε,hεCut,hεη⟩ :=
    source_pair_cutoff_collar_parameters hκ hC hcut
  obtain ⟨δ,C₂,hδ,hδG,hδMax',hC₂,grid,hgrid,hError,hnorm,hpairAll⟩ :=
    hall hη hε hεη
  refine ⟨C,cut,η,ε,δ,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hδ,hδG,hδMax',?_⟩
  intro α hα hHalf
  obtain ⟨D,hD,hpair⟩ := hpairAll hα hHalf
  refine ⟨D,hD,?_⟩
  filter_upwards [hnorm,hpair] with n hn hpRaw
  intro I hI hsub
  have hδHalf : δ <
      gap μ Q (markY β Q) (markZ x Q) ε η / 2 := by
    linarith [hδG]
  have hεSq : ε < cut^2 := by nlinarith [sq_pos_of_pos hcut]
  have hwin : ∀ z ∈ I, E-δ ≤ z := by
    intro z hz
    exact (hsub hz).1
  have hN := hn.2.2 I hI hsub
  have hP := hpRaw I hI hsub
  have hMoments := source_actual_retained_pure_count_moments_of_pair_bound
    (n+2) (by omega) μ h.overlap_range.1
    hκ hC hηCollar hδHalf hcut hcutOne hεSq hcutRad
    I hI hwin hP.2 hP.1
  exact ⟨hN.2,hMoments.1,hMoments.2.1,hMoments.2.2.1,hMoments.2.2.2⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
