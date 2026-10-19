-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairFixedRetainedNormalization
public import SlowEquilibration.SourcePhysicalPairAlphaIndependentCutoff
public import SlowEquilibration.SourcePhysicalPairRetainedSharpBounds
public import SlowEquilibration.SourcePhysicalPairSelectedRealSecondMoment

/-! A common physical mark box and sphere-regularity constant are fixed
before the overlap parameters; the actual pair cutoff is fixed before both
the overlap parameters and the mesoscopic exponent.  The retained pair
bound uses the actual retained first moment. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_mixed_actual_retained_sharp_pair_bounds_fixed_mark_box
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
        let G := gap μ Q (markY β Q) (markZ x Q) ε η
        ∃ L R δ C₂ : ℝ,
          L < markK μ β Q ∧ markK μ β Q < R ∧
          Icc L R ⊆ Ioo a₀ b₀ ∧ a₀ < L ∧
          0 < δ ∧ δ < G/4 ∧ δ ≤ δMax ∧ 0 < C₂ ∧
          ∃ grid : ℕ, 1 ≤ grid ∧
            Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
            (∀ᶠ n : ℕ in atTop,
              0 ≤ sourceSelectionWeightError C₂ μ Q G g grid (n+1) ∧
              sourceSelectionWeightError C₂ μ Q G g grid (n+1) < 1 ∧
              ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
                K ⊆ {z | z 0 ∈ Icc (E-δ) (E+δ) ∧ z 1 ∈ Icc L R} →
                (1-sourceSelectionWeightError C₂ μ Q G g grid (n+1))*
                    sourceUnfilteredScoreWindowMean (n+2) μ Q K ≤
                  sourceRetainedScoreWindowMean (n+2) μ Q K (g/2) C ε η E G ∧
                sourceRetainedScoreWindowMean (n+2) μ Q K (g/2) C ε η E G ≤
                  sourceUnfilteredScoreWindowMean (n+2) μ Q K) ∧
            ∀ {α : ℝ}, 1/4 < α → α < 1/2 →
              ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
                ∀ K : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet K →
                K ⊆ {z | z 0 ∈ Icc (E-δ) (E+δ) ∧ z 1 ∈ Icc L R} →
                sourceRetainedMixedPairMean (n+2) μ Q
                    (pairRadius μ h.overlap_range.1 hd) cut K
                    (g/2) C ε η E G ≤
                  (1+D*sourcePrintedPairError α n)*
                    (sourceRetainedScoreWindowMean (n+2) μ Q K
                      (g/2) C ε η E G)^2 ∧
                (∫⁻ J, sourceRetainedMixedPairCount (n+2)
                    (centerCoefficients (mixtureCoefficients μ) Q)
                    (pairRadius μ h.overlap_range.1 hd) cut K
                    (g/2) C ε η E G J
                    ∂disorderLaw (n+3) μ.maxDegree) < ⊤ := by
  dsimp only
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
  let b₀ := markK μ β Q+1
  change |E|+δMax+|a₀|+|b₀|+1 ≤ M at hMbound
  have hM : 0 ≤ M := by linarith [abs_nonneg E, abs_nonneg a₀, abs_nonneg b₀]
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  obtain ⟨cut,hcut,hcutOne,hcutRad,hcutAll⟩ :=
    source_mixed_actual_subcritical_pair_cutoff_before_alpha
      μ h.overlap_range.1 hnp hd hM hg
  refine ⟨cut,hcut,hcutOne,hcutRad,?_⟩
  intro η ε hη hε hεη
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hG : 0 < G := (source_trial_gap μ h hnp hε hη hεη).1
  obtain ⟨L,R,δ,C₂,hL,hR,hsub,hgapL,hδ,hδG,hδMax',hC₂,
      grid,hgrid,hError,hnorm⟩ :=
    source_mixed_actual_retained_normalization_fixed_regularity
      μ h hnp hε hη hεη hδMax hC hMbound hreg
  have hnorm' : ∀ᶠ n : ℕ in atTop, _ :=
    (tendsto_add_atTop_nat 1).eventually hnorm
  refine ⟨L,R,δ,C₂,hL,hR,hsub,hgapL,hδ,hδG,hδMax',
    hC₂,grid,hgrid,hError,?_,?_⟩
  · exact hnorm'
  intro α hα hHalf
  obtain ⟨Cpair,hCpair,hpair⟩ := hcutAll hα
  refine ⟨9*Cpair+8,by positivity,?_⟩
  filter_upwards [hnorm',hpair,
    sourceRetainedPairCoefficient_printed_bound μ h.overlap_range.1 hG hg
      hα hHalf hC₂ hCpair.le grid] with n hn hp hsharp
  intro K hK hwindow
  have hmarks : ∀ z ∈ K, |z 0| ≤ M ∧ |z 1| ≤ M ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1 := by
    intro z hz
    have hzbox := hwindow hz
    have hzk := hsub hzbox.2
    change a₀ < z 1 ∧ z 1 < b₀ at hzk
    refine ⟨?_,?_,hgapL.le.trans hzbox.2.1⟩
    · apply abs_le.mpr
      constructor <;> linarith [hzbox.1.1,hzbox.1.2,hδMax',hMbound,
        le_abs_self E,neg_le_abs E,abs_nonneg a₀,abs_nonneg b₀]
    · apply abs_le.mpr
      constructor <;> linarith [hzk.1,hzk.2,hMbound,
        le_abs_self b₀,neg_le_abs a₀,abs_nonneg E,abs_nonneg a₀,abs_nonneg b₀]
  have hN := hn.2.2 K hK hwindow
  have hP := source_mixed_retained_pair_mean_bound_of_normalization
    (n+2) (by omega) μ h.overlap_range.1
    _ cut K (g/2) C ε η E G _ _ (by positivity) hn.2.1
    (hp K hK hmarks) hN.1
  refine ⟨?_,?_⟩
  · exact hP.trans (mul_le_mul_of_nonneg_right hsharp (sq_nonneg _))
  · exact source_retained_pair_lintegral_lt_top_of_unfiltered_bound
      (n+2) (by omega) μ h.overlap_range.1
      (pairRadius μ h.overlap_range.1 hd) cut K (g/2) C ε η E G
      (1+Cpair*sourcePrintedPairError α n) (hp K hK hmarks)

end
end SlowEquilibration.PairConditionalDeterminantMoments
