-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPurePairFixedNormalization
public import SlowEquilibration.SourcePhysicalPairPureAlphaIndependentCutoff
public import SlowEquilibration.SourcePhysicalPurePairSelectedVariance

/-! For proper-pure mixtures the raw pair cutoff and posterior jet cutoff
can both be fixed from a compact value-mark box before ε and η. The
retained pair estimate then has the printed error with its actual mean
and a finite genuine pair integral. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem source_pure_actual_retained_sharp_pair_bounds_fixed_mark_box
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q δMax M C : ℝ}
    (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hδMax : 0 < δMax) (hC : 0 < C)
    (hMbound : |markE (FiniteMixture.pure p hp a ha) β x Q|+δMax+1 ≤ M)
    (hreg : ∀ n : ℕ, ∀ u : Vector (n+1), ∀ hu : ‖u‖^2=(n+1:ℕ),
      ∀ h₀ : ℝ, |h₀| ≤ M →
        let μ := FiniteMixture.pure p hp a ha
        let c := centerCoefficients (mixtureCoefficients μ) Q
        (valueConditionedLaw c u hu h₀).real
          {J | C < sourceSphereRegularity c J} ≤
          (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2)) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ cut : ℝ, 0 < cut ∧ cut ≤ 1 ∧
      cut ≤ pairRadius μ h.overlap_range.1 h.min_degree ∧
      ∀ {η ε : ℝ}, 0 < η → 0 < ε → ε < 1-η →
        let G := gap μ Q (markY β Q) (markZ x Q) ε η
        ∃ δ C₂ : ℝ, 0 < δ ∧ δ < G/4 ∧ δ ≤ δMax ∧ 0 < C₂ ∧
          ∃ grid : ℕ, 1 ≤ grid ∧
            Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
            (∀ᶠ n : ℕ in atTop,
              0 ≤ sourceSelectionWeightError C₂ μ Q G g grid (n+1) ∧
              sourceSelectionWeightError C₂ μ Q G g grid (n+1) < 1 ∧
              ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
                (1-sourceSelectionWeightError C₂ μ Q G g grid (n+1))*
                  sourceUnfilteredValueWindowMean (n+2) μ Q I ≤
                  sourceRetainedValueWindowMean (n+2) μ Q I (g/2) C ε η E G ∧
                sourceRetainedValueWindowMean (n+2) μ Q I (g/2) C ε η E G ≤
                  sourceUnfilteredValueWindowMean (n+2) μ Q I) ∧
            ∀ {α : ℝ}, 1/4 < α → α < 1/2 →
              ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
                ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
                  sourceRetainedPurePairMean (n+2) μ Q
                    (pairRadius μ h.overlap_range.1 h.min_degree) cut I
                    (g/2) C ε η E G ≤
                    (1+D*sourcePrintedPairError α n)*
                      (sourceRetainedValueWindowMean (n+2) μ Q I
                        (g/2) C ε η E G)^2 ∧
                  (∫⁻ J, sourceRetainedPurePairCount (n+2)
                      (centerCoefficients (mixtureCoefficients μ) Q)
                      (pairRadius μ h.overlap_range.1 h.min_degree) cut I
                      (g/2) C ε η E G J
                      ∂disorderLaw (n+3) μ.maxDegree) < ⊤ := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  have hp4 : 4 ≤ p := by
    simpa [FiniteMixture.minDegree,FiniteMixture.pure,
      Finsupp.support_single p ha.ne'] using h.min_degree
  have hpR : (0:ℝ) < p := by exact_mod_cast (show 0<p by omega)
  have hM : 0 ≤ M := by linarith [abs_nonneg E]
  obtain ⟨cut,hcut,hcutOne,hcutRad,hcutAll⟩ :=
    source_pure_actual_subcritical_pair_cutoff_before_alpha
      p hp4 a ha h.overlap_range.1 hM hg
  refine ⟨cut,hcut,hcutOne,hcutRad,?_⟩
  intro η ε hη hε hεη
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  have hG : 0 < G := (pure_source_trial_gap p hp a ha h hε hη hεη).1
  let δBound := min δMax (g/(2*(p:ℝ)))
  have hδBound : 0 < δBound := lt_min hδMax (div_pos hg (by positivity))
  have hMbound' : |E|+δBound+1 ≤ M := by
    linarith [min_le_left δMax (g/(2*(p:ℝ)))]
  obtain ⟨δ,C₂,hδ,hδG,hδB,hC₂,grid,hgrid,hError,hnorm⟩ :=
    source_pure_actual_retained_normalization_fixed_regularity
      p hp a ha h hε hη hεη hδBound hC hMbound' hreg
  have hδMax' : δ ≤ δMax := hδB.trans (min_le_left _ _)
  have hδedge : δ ≤
      (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(4*(p:ℝ)) := by
    have H := hδB.trans (min_le_right _ _)
    convert H using 1
    dsimp only [g]
    ring
  have hnorm' : ∀ᶠ n : ℕ in atTop, _ :=
    (tendsto_add_atTop_nat 1).eventually hnorm
  refine ⟨δ,C₂,hδ,hδG,hδMax',hC₂,grid,hgrid,hError,hnorm',?_⟩
  intro α hα hHalf
  obtain ⟨Cpair,hCpair,hpair⟩ := hcutAll hα
  refine ⟨9*Cpair+8,by positivity,?_⟩
  filter_upwards [hnorm',hpair,
    sourceRetainedPairCoefficient_printed_bound μ h.overlap_range.1
      hG hg hα hHalf hC₂ hCpair.le grid] with n hn hpRaw hsharp
  intro I hI hsub
  have hmarks : ∀ h₀ ∈ I,
      |h₀| ≤ M ∧ 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*h₀ := by
    intro h₀ hh
    have hm := hsub hh
    refine ⟨?_,source_pure_value_box_edge_margin
      p hp a ha h hδedge h₀ hm⟩
    apply abs_le.mpr
    constructor <;> linarith [hm.1,hm.2,hδMax',hMbound,
      le_abs_self E,neg_le_abs E]
  have hN := hn.2.2 I hI hsub
  have hPair := source_pure_retained_pair_mean_bound_of_normalization
    (n+2) (by omega) μ h.overlap_range.1
    _ cut I (g/2) C ε η E G _ _ (by positivity) hn.2.1
    (hpRaw I hI hmarks) hN.1
  refine ⟨?_,?_⟩
  · exact hPair.trans (mul_le_mul_of_nonneg_right hsharp (sq_nonneg _))
  · exact source_retained_pure_pair_lintegral_lt_top_of_unfiltered_bound
      (n+2) (by omega) μ h.overlap_range.1
      (pairRadius μ h.overlap_range.1 h.min_degree) cut I
      (g/2) C ε η E G
      (1+Cpair*sourcePrintedPairError α n) (hpRaw I hI hmarks)

end
end SlowEquilibration.PairConditionalDeterminantMoments
