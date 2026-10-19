-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairFixedSharpBounds
public import SlowEquilibration.SourcePhysicalPairSelectedVariance

/-! The actual retained first mean, real second moment, and genuine variance
for every Borel window inside one source mark box.  The local pair cutoff
precedes ε and α, and the mark window precedes α. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_mixed_actual_retained_fixed_window_second_moment
    (μ : FiniteMixture) {β x Q δMax M C : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) (hC : 0 < C)
    (hMbound : |markE μ β x Q|+δMax+
      |2*Real.sqrt (Q^2*μ.xi2 Q)+
        (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2|+
      |markK μ β Q+1|+1 ≤ M)
    (hreg : ∀ n : ℕ, ∀ u : Vector (n+1), ∀ hu : ‖u‖^2=(n+1:ℕ),
      ∀ h₀ k₀ : ℝ, |h₀| ≤ M → |k₀| ≤ M →
        let c := centerCoefficients (mixtureCoefficients μ) Q
        (mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])).real
          {J | C < sourceSphereRegularity c J} ≤
          (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2)) :
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
    let b₀ := markK μ β Q+1
    ∃ cut : ℝ, 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 hd ∧
      ∀ {η ε : ℝ}, 0 < η → 0 < ε → ε < 1-η →
        η ≤ sourceCriticalCollarOverlapLoss (g/2) C → ε < cut^2/2 →
        let G := gap μ Q (markY β Q) (markZ x Q) ε η
        ∃ L R ω C₂ : ℝ,
          L < markK μ β Q ∧ markK μ β Q < R ∧
          Icc L R ⊆ Ioo a₀ b₀ ∧ a₀ < L ∧
          0 < ω ∧ ω < G/4 ∧ ω ≤ δMax ∧ 0 < C₂ ∧
          ∃ grid : ℕ, 1 ≤ grid ∧
            Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
            ∀ {α : ℝ}, 1/4 < α → α < 1/2 →
              ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
                ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
                K ⊆ {z | z 0 ∈ Icc (E-ω) (E+ω) ∧ z 1 ∈ Icc L R} →
                let a := sourceRetainedScoreWindowMean (n+2) μ Q K
                  (g/2) C ε η E G
                let b := sourceUnfilteredScoreWindowMean (n+2) μ Q K
                let second := sourceRetainedScoreWindowSecondMoment (n+2)
                  μ Q K (g/2) C ε η E G
                let variance := ProbabilityTheory.variance
                  (fun J => (sourceRetainedScoreWindowCount (n+2)
                    (centerCoefficients (mixtureCoefficients μ) Q) K
                    (g/2) C ε η E G J).toReal)
                  (disorderLaw (n+3) μ.maxDegree)
                (1-sourceSelectionWeightError C₂ μ Q G g grid (n+1))*b ≤ a ∧
                  a ≤ b ∧
                  second ≤ (1+D*sourcePrintedPairError α n)*a^2+
                    (1+(1-ε)/(cut^2-ε))*a ∧
                  variance ≤ D*sourcePrintedPairError α n*a^2+
                    (1+(1-ε)/(cut^2-ε))*a ∧
                  MemLp
                    (fun J => (sourceRetainedScoreWindowCount (n+2)
                      (centerCoefficients (mixtureCoefficients μ) Q) K
                      (g/2) C ε η E G J).toReal) 2
                    (disorderLaw (n+3) μ.maxDegree) := by
  dsimp only
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  have hκ : 0 < g/2 := div_pos hg (by norm_num)
  obtain ⟨cut,hcut,hcutOne,hcutRad,hall⟩ :=
    source_mixed_actual_retained_sharp_pair_bounds_fixed_mark_box
      μ h hnp hd hδMax hC hMbound hreg
  refine ⟨cut,hcut,hcutOne,hcutRad,?_⟩
  intro η ε hη hε hεη hηCollar hεCut
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  obtain ⟨L,R,ω,C₂,hL,hR,hsub,hgapL,hω,hωG,hωMax,hC₂,
      grid,hgrid,hError,hnorm,hpairAll⟩ := hall hη hε hεη
  refine ⟨L,R,ω,C₂,hL,hR,hsub,hgapL,hω,hωG,hωMax,hC₂,
    grid,hgrid,hError,?_⟩
  intro α hα hHalf
  obtain ⟨D,hD,hpair⟩ := hpairAll hα hHalf
  refine ⟨D,hD,?_⟩
  filter_upwards [hnorm,hpair] with n hn hp
  intro K hK hwindow
  have hωHalf : ω < G/2 := by linarith [hωG]
  have hεSq : ε < cut^2 := by nlinarith [sq_pos_of_pos hcut]
  have hwin : ∀ z ∈ K, E-ω ≤ z 0 := by
    intro z hz
    exact (hwindow hz).1.1
  have hN := hn.2.2 K hK hwindow
  have hP := hp K hK hwindow
  have hSquare := (source_actual_retained_count_real_second_moment_of_pair_bound
    (n+2) (by omega) μ h.overlap_range.1 hnp
    hκ hC hηCollar hωHalf hcut hcutOne hεSq hcutRad
    K hK hwin hP.2 hP.1).1
  have hVar := source_actual_retained_count_variance_of_pair_bound
    (n+2) (by omega) μ h.overlap_range.1 hnp
    hκ hC hηCollar hωHalf hcut hcutOne hεSq hcutRad
    K hK hwin hP.2 hP.1
  have hLp := source_actual_retained_count_memLp_two_of_pair_finite
    (n+2) (by omega) μ h.overlap_range.1 hnp
    hκ hC hηCollar hωHalf hcut hcutOne hεSq hcutRad
    K hK hwin hP.2
  exact ⟨hN.1,hN.2,hSquare,hVar,hLp⟩

end
end SlowEquilibration.PairConditionalDeterminantMoments
