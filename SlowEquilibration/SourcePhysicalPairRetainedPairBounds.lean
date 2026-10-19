-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairRetainedPairDefinitions

/-! Source11.9 retained normalization for the actual integrated mixed
subcritical pair count: a_N is the original selected maximum-count mean,
and the internally derived coefficient converges to one. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceRetainedPairCoefficient (μ:FiniteMixture) (Q G g C₂:ℝ) (grid:ℕ) (Cpair α:ℝ) (n:ℕ):ℝ:=
  (1+Cpair*(((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)+
    Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4)))/
    (1-sourceSelectionWeightError C₂ μ Q G g grid (n+1))^2

theorem sourceRetainedPairCoefficient_tendsto (μ:FiniteMixture) {Q G g α:ℝ}
    (hQ:0<Q) (hG:0<G) (hg:0<g) (hα:1/4<α) (hαHalf:α<1/2)
    (C₂:ℝ) (grid:ℕ) (Cpair:ℝ) :
    Tendsto (sourceRetainedPairCoefficient μ Q G g C₂ grid Cpair α) atTop (𝓝 1):=by
  have hLoss:=(sourceSelectionWeightError_tendsto C₂ μ hQ hG hg grid).comp (tendsto_add_atTop_nat 1)
  have hPair:=source_pair_count_error_tendsto Cpair hα hαHalf
  have hOne:Tendsto (fun _n:ℕ=>(1:ℝ)) atTop (𝓝 1):=tendsto_const_nhds
  have H:=(hOne.add hPair).div ((hOne.sub hLoss).pow 2)
    (show ((1:ℝ)-0)^2≠0 by norm_num)
  simp only [add_zero,sub_zero,one_pow,div_one] at H
  convert H using 1
  funext n
  rfl

theorem source_mixed_actual_retained_subcritical_pair_count_bound (μ:FiniteMixture)
    {β x Q ε η δMax α:ℝ} (h:Certificate μ β x Q)
    (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree)
    (hε:0<ε) (hη:0<η) (hεη:ε<1-η) (hδMax:0<δMax)
    (hα:1/4<α) (hαHalf:α<1/2) :
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ L R δ C C₂ cut Cpair:ℝ,L < markK μ β Q ∧ markK μ β Q<R ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+g<L ∧ 0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ 0<C ∧ 0<C₂ ∧
      0<cut ∧ cut ≤ 1 ∧ cut ≤ pairRadius μ h.overlap_range.1 hd ∧ 0<Cpair ∧
      ∃ grid:ℕ,1 ≤ grid ∧
      Tendsto (sourceRetainedPairCoefficient μ Q G g C₂ grid Cpair α) atTop (𝓝 1) ∧
      ∀ᶠ n:ℕ in atTop,∀ (K:Set (EuclideanSpace ℝ (Fin 2))),MeasurableSet K →
        K ⊆ {b|b 0 ∈ Icc (E-δ) (E+δ) ∧ b 1 ∈ Icc L R} →
        sourceRetainedMixedPairMean (n+2) μ Q (pairRadius μ h.overlap_range.1 hd) cut K
          (g/2) C ε η E G ≤ sourceRetainedPairCoefficient μ Q G g C₂ grid Cpair α n*
            (sourceRetainedScoreWindowMean (n+2) μ Q K (g/2) C ε η E G)^2:=by
  dsimp only
  let E:=markE μ β x Q
  let G:=gap μ Q (markY β Q) (markZ x Q) ε η
  let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge:0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q):=by
    simpa only [markB] using h.edge_margin.2.2
  have hg:0<g:=div_pos hedge (by norm_num)
  have hG:0<G:=(source_trial_gap μ h hnp hε hη hεη).1
  obtain ⟨L,R,δ,C,C₂,hL,hR,hgapL,hδ,hδG,hδMax',hC,hC₂,grid,hgrid,_hError,hnorm⟩:=
    source_mixed_actual_retained_normalization μ h hnp hε hη hεη hδMax
  let M:=|E|+δ+|L|+|R|+1
  have hM:0 ≤ M:=by dsimp [M];positivity
  obtain ⟨cut,Cpair,hcut,hcutOne,hcutRad,hCpair,hpair⟩:=
    source_mixed_actual_subcritical_pair_count_bound μ h.overlap_range.1 hnp hd hM hg hα
  refine ⟨L,R,δ,C,C₂,cut,Cpair,hL,hR,hgapL,hδ,hδG,hδMax',hC,hC₂,hcut,hcutOne,hcutRad,hCpair,
    grid,hgrid,sourceRetainedPairCoefficient_tendsto μ h.overlap_range.1 hG hg hα hαHalf C₂ grid Cpair,?_⟩
  have hnorm':∀ᶠ n:ℕ in atTop,_:=(tendsto_add_atTop_nat 1).eventually hnorm
  filter_upwards [hnorm',hpair] with n hn hp
  intro K hK hsub
  have hmarks:∀ b∈K,|b 0| ≤ M ∧ |b 1| ≤ M ∧ 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ b 1:=by
    intro b hb
    have hm:=hsub hb
    refine ⟨?_,?_,hgapL.le.trans hm.2.1⟩
    · apply abs_le.mpr
      constructor <;> dsimp [M] <;> linarith [hm.1.1,hm.1.2,le_abs_self E,neg_le_abs E,abs_nonneg L,abs_nonneg R]
    · apply abs_le.mpr
      constructor <;> dsimp [M] <;> linarith [hm.2.1,hm.2.2,le_abs_self R,neg_le_abs L,abs_nonneg E,abs_nonneg L,abs_nonneg R]
  exact source_mixed_retained_pair_mean_bound_of_normalization (n+2) (by omega) μ h.overlap_range.1
    _ cut K (g/2) C ε η E G _ _ (by positivity) hn.2.1 (hp K hK hmarks) (hn.2.2 K hK hsub).1

end
end SlowEquilibration.PairConditionalDeterminantMoments
