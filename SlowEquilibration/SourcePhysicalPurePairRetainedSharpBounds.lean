-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPurePairRetainedPairDefinitions
public import SlowEquilibration.SourcePhysicalPairRetainedSharpBounds

@[expose] public section
/-! Printed source11.9 sharp retained-pair error for the proper pure
model, with the literal actual retained a_N and original value windows. -/
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Every near-ground Borel value window shares the actual retained mean
comparison and printed pair error. Every constant precedes dimension. -/
theorem source_pure_actual_retained_sharp_pair_bounds
    (p:ℕ) (hp:2 ≤ p) (a:ℝ) (ha:0<a)
    {β x Q ε η δMax α:ℝ} (h:Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hε:0<ε) (hη:0<η) (hεη:ε<1-η) (hδMax:0<δMax)
    (hα:1/4<α) (hHalf:α<1/2) :
    let μ:=FiniteMixture.pure p hp a ha
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ δ C C₂ cut D:ℝ,0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ 0<C ∧ 0<C₂ ∧
      0<cut ∧ cut ≤ 1 ∧ cut ≤ pairRadius μ h.overlap_range.1 h.min_degree ∧ 0<D ∧
      ∃ grid:ℕ,1 ≤ grid ∧ Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
      ∀ᶠ n:ℕ in atTop,0 ≤ sourceSelectionWeightError C₂ μ Q G g grid (n+1) ∧
        sourceSelectionWeightError C₂ μ Q G g grid (n+1)<1 ∧
        ∀ (I:Set ℝ),MeasurableSet I → I ⊆ Icc (E-δ) (E+δ) →
          (1-sourceSelectionWeightError C₂ μ Q G g grid (n+1))*sourceUnfilteredValueWindowMean (n+2) μ Q I ≤
              sourceRetainedValueWindowMean (n+2) μ Q I (g/2) C ε η E G ∧
            sourceRetainedValueWindowMean (n+2) μ Q I (g/2) C ε η E G ≤
              sourceUnfilteredValueWindowMean (n+2) μ Q I ∧
            sourceRetainedPurePairMean (n+2) μ Q (pairRadius μ h.overlap_range.1 h.min_degree) cut I
              (g/2) C ε η E G ≤ (1+D*sourcePrintedPairError α n)*
                (sourceRetainedValueWindowMean (n+2) μ Q I (g/2) C ε η E G)^2:=by
  dsimp only
  let μ:=FiniteMixture.pure p hp a ha
  let E:=markE μ β x Q
  let G:=gap μ Q (markY β Q) (markZ x Q) ε η
  let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge:0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q):=by
    simpa only [markB] using h.edge_margin.2.2
  have hg:0<g:=div_pos hedge (by norm_num)
  have hG:0<G:=(pure_source_trial_gap p hp a ha h hε hη hεη).1
  have hpR:(0:ℝ)<p:=by exact_mod_cast (show 0<p by omega)
  have hp4:4 ≤ p:=by
    simpa [FiniteMixture.minDegree,FiniteMixture.pure,Finsupp.support_single p ha.ne'] using h.min_degree
  let δBound:=min δMax (g/(2*(p:ℝ)))
  have hδBound:0<δBound:=lt_min hδMax (div_pos hg (by positivity))
  obtain ⟨δ,C,C₂,hδ,hδG,hδB,hC,hC₂,grid,hgrid,hError,hnorm⟩:=
    source_pure_actual_retained_normalization p hp a ha h hε hη hεη hδBound
  have hδMax':δ ≤ δMax:=hδB.trans (min_le_left _ _)
  have hδedge:δ ≤ (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(4*(p:ℝ)):=by
    have H:=hδB.trans (min_le_right _ _)
    convert H using 1
    dsimp only [g]
    ring
  let M:=|E|+δ+1
  have hM:0 ≤ M:=by dsimp [M];positivity
  obtain ⟨cut,Cpair,hcut,hcutOne,hcutRad,hCpair,hpair⟩:=
    source_pure_actual_subcritical_pair_count_bound p hp4 a ha h.overlap_range.1 hM hg hα
  refine ⟨δ,C,C₂,cut,9*Cpair+8,hδ,hδG,hδMax',hC,hC₂,hcut,hcutOne,hcutRad,
    by positivity,grid,hgrid,hError,?_⟩
  have hnorm':∀ᶠ n:ℕ in atTop,_:=(tendsto_add_atTop_nat 1).eventually hnorm
  filter_upwards [hnorm',hpair,sourceRetainedPairCoefficient_printed_bound μ h.overlap_range.1 hG hg
    hα hHalf hC₂ hCpair.le grid] with n hn hP hsharp
  refine ⟨hn.1,hn.2.1,?_⟩
  intro I hI hsub
  have hmarks:∀ h₀∈I,|h₀| ≤ M ∧ 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ (p:ℝ)*h₀:=by
    intro h₀ hh
    have hm:=hsub hh
    refine ⟨?_,source_pure_value_box_edge_margin p hp a ha h hδedge h₀ hm⟩
    apply abs_le.mpr
    constructor <;> dsimp [M] <;> linarith [hm.1,hm.2,le_abs_self E,neg_le_abs E]
  have hN:=hn.2.2 I hI hsub
  have hPair:=source_pure_retained_pair_mean_bound_of_normalization (n+2) (by omega) μ h.overlap_range.1
    _ cut I (g/2) C ε η E G _ _ (by positivity) hn.2.1 (hP I hI hmarks) hN.1
  refine ⟨hN.1,hN.2,?_⟩
  exact hPair.trans (mul_le_mul_of_nonneg_right hsharp (sq_nonneg _))

end
end SlowEquilibration.PairConditionalDeterminantMoments
