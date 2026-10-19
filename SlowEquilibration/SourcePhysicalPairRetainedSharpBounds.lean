-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairRetainedPairBounds
public import SlowEquilibration.SourcePairRetainedErrorRates

/-! The printed sharp source11.9 rate with the true retained a_N. The
exponential filter loss is absorbed into the actual central/annular error
without a supplied retained mean or desired decay premise. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourcePrintedPairError (α:ℝ) (n:ℕ):ℝ:=
  ((n+3:ℕ):ℝ)^(1-4*α)+1/Real.sqrt (n+3:ℕ)+Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4)

lemma sourcePrintedPairError_nonneg (α:ℝ) (n:ℕ) :0 ≤ sourcePrintedPairError α n:=by
  unfold sourcePrintedPairError
  positivity

theorem sourcePrintedPairError_tendsto {α:ℝ} (hα:1/4<α) (hHalf:α<1/2) :
    Tendsto (sourcePrintedPairError α) atTop (𝓝 0):=by
  have H:=source_pair_count_error_tendsto 1 hα hHalf
  simp only [one_mul] at H
  convert H using 1
  funext n
  rfl

theorem sourceRetainedPairCoefficient_printed_bound (μ:FiniteMixture) {Q G g α C₂ Cpair:ℝ}
    (hQ:0<Q) (hG:0<G) (hg:0<g) (hα:1/4<α) (hHalf:α<1/2)
    (hC₂:0<C₂) (hCpair:0 ≤ Cpair) (grid:ℕ) :
    ∀ᶠ n:ℕ in atTop,sourceRetainedPairCoefficient μ Q G g C₂ grid Cpair α n ≤
      1+(9*Cpair+8)*sourcePrintedPairError α n:=by
  have hP:=sourcePrintedPairError_tendsto hα hHalf
  have hT:=(sourceSelectionWeightError_tendsto C₂ μ hQ hG hg grid).comp (tendsto_add_atTop_nat 1)
  filter_upwards [hP.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    hT.eventually (gt_mem_nhds (show (0:ℝ)<1/2 by norm_num)),
    sourceSelectionWeightError_shifted_le_inverse_sqrt_eventually C₂ hC₂ μ hQ hG hg grid]
    with n hp ht hs
  apply retained_normalization_absorption hCpair
    ⟨sourcePrintedPairError_nonneg α n,hp.le⟩
    ⟨sourceSelectionWeightError_nonneg _ _ _ _ _ _ _,ht.le⟩
  apply hs.trans
  unfold sourcePrintedPairError
  have hpow:0 ≤ ((n+3:ℕ):ℝ)^(1-4*α):=by positivity
  have hexp:0 ≤ Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4):=(Real.exp_pos _).le
  linarith

/-- All near-ground Borel windows share the actual mean comparison and
the printed integrated retained-pair error. Constants precede every
dimension and every fixed microscopic window. -/
theorem source_mixed_actual_retained_sharp_pair_bounds (μ:FiniteMixture)
    {β x Q ε η δMax α:ℝ} (h:Certificate μ β x Q)
    (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree)
    (hε:0<ε) (hη:0<η) (hεη:ε<1-η) (hδMax:0<δMax)
    (hα:1/4<α) (hHalf:α<1/2) :
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ L R δ C C₂ cut D:ℝ,L < markK μ β Q ∧ markK μ β Q<R ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+g<L ∧ 0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ 0<C ∧ 0<C₂ ∧
      0<cut ∧ cut ≤ 1 ∧ cut ≤ pairRadius μ h.overlap_range.1 hd ∧ 0<D ∧
      ∃ grid:ℕ,1 ≤ grid ∧ Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
      ∀ᶠ n:ℕ in atTop,0 ≤ sourceSelectionWeightError C₂ μ Q G g grid (n+1) ∧
        sourceSelectionWeightError C₂ μ Q G g grid (n+1)<1 ∧
        ∀ (K:Set (EuclideanSpace ℝ (Fin 2))),MeasurableSet K →
          K ⊆ {z|z 0 ∈ Icc (E-δ) (E+δ) ∧ z 1 ∈ Icc L R} →
          (1-sourceSelectionWeightError C₂ μ Q G g grid (n+1))*sourceUnfilteredScoreWindowMean (n+2) μ Q K ≤
              sourceRetainedScoreWindowMean (n+2) μ Q K (g/2) C ε η E G ∧
            sourceRetainedScoreWindowMean (n+2) μ Q K (g/2) C ε η E G ≤
              sourceUnfilteredScoreWindowMean (n+2) μ Q K ∧
            sourceRetainedMixedPairMean (n+2) μ Q (pairRadius μ h.overlap_range.1 hd) cut K
              (g/2) C ε η E G ≤ (1+D*sourcePrintedPairError α n)*
                (sourceRetainedScoreWindowMean (n+2) μ Q K (g/2) C ε η E G)^2:=by
  dsimp only
  let E:=markE μ β x Q
  let G:=gap μ Q (markY β Q) (markZ x Q) ε η
  let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge:0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q):=by
    simpa only [markB] using h.edge_margin.2.2
  have hg:0<g:=div_pos hedge (by norm_num)
  have hG:0<G:=(source_trial_gap μ h hnp hε hη hεη).1
  obtain ⟨L,R,δ,C,C₂,hL,hR,hgapL,hδ,hδG,hδMax',hC,hC₂,grid,hgrid,hError,hnorm⟩:=
    source_mixed_actual_retained_normalization μ h hnp hε hη hεη hδMax
  let M:=|E|+δ+|L|+|R|+1
  have hM:0 ≤ M:=by dsimp [M];positivity
  obtain ⟨cut,Cpair,hcut,hcutOne,hcutRad,hCpair,hpair⟩:=
    source_mixed_actual_subcritical_pair_count_bound μ h.overlap_range.1 hnp hd hM hg hα
  refine ⟨L,R,δ,C,C₂,cut,9*Cpair+8,hL,hR,hgapL,hδ,hδG,hδMax',hC,hC₂,hcut,hcutOne,hcutRad,
    by positivity,grid,hgrid,hError,?_⟩
  have hnorm':∀ᶠ n:ℕ in atTop,_:=(tendsto_add_atTop_nat 1).eventually hnorm
  filter_upwards [hnorm',hpair,sourceRetainedPairCoefficient_printed_bound μ h.overlap_range.1 hG hg
    hα hHalf hC₂ hCpair.le grid] with n hn hp hsharp
  refine ⟨hn.1,hn.2.1,?_⟩
  intro K hK hsub
  have hmarks:∀ z∈K,|z 0| ≤ M ∧ |z 1| ≤ M ∧ 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1:=by
    intro z hz
    have hm:=hsub hz
    refine ⟨?_,?_,hgapL.le.trans hm.2.1⟩
    · apply abs_le.mpr
      constructor <;> dsimp [M] <;> linarith [hm.1.1,hm.1.2,le_abs_self E,neg_le_abs E,abs_nonneg L,abs_nonneg R]
    · apply abs_le.mpr
      constructor <;> dsimp [M] <;> linarith [hm.2.1,hm.2.2,le_abs_self R,neg_le_abs L,abs_nonneg E,abs_nonneg L,abs_nonneg R]
  have hN:=hn.2.2 K hK hsub
  have hP:=source_mixed_retained_pair_mean_bound_of_normalization (n+2) (by omega) μ h.overlap_range.1
    _ cut K (g/2) C ε η E G _ _ (by positivity) hn.2.1 (hp K hK hmarks) hN.1
  refine ⟨hN.1,hN.2,?_⟩
  exact hP.trans (mul_le_mul_of_nonneg_right hsharp (sq_nonneg _))

end
end SlowEquilibration.PairConditionalDeterminantMoments
