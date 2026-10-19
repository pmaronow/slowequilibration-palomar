-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSelectionFailureRates
public import SlowEquilibration.ConditionedDeterminantMoments
public import SlowEquilibration.SourcePhysicalPairDeterminantSelectionHolder

/-! Actual determinant-weighted selection loss. The own ordinary
determinant moment and the literal raw-posterior failure are proved
inputs, giving a vanishing relative loss uniformly in compact marks. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity ConditionedDeterminantMoments
open GOEMaximumDeterminant
open scoped ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

/-- The literal actual mixed posterior loses a vanishing fraction of its
own determinant mean. No desired filter-loss estimate is a hypothesis. -/
theorem source_mixed_physical_posterior_determinant_selection_loss (μ:FiniteMixture)
    {β x Q ε η δMax:ℝ} (h:Certificate μ β x Q)
    (hnp:μ.minDegree<μ.maxDegree) (hε:0<ε) (hη:0<η) (hεη:ε<1-η)
    (hδMax:0<δMax) :
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ L R δ C C₂:ℝ,L < markK μ β Q ∧ markK μ β Q<R ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+g<L ∧ 0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ 0<C ∧ 0<C₂ ∧
      ∃ grid:ℕ,1 ≤ grid ∧
      Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
      ∀ᶠ n:ℕ in atTop,sourceSelectionWeightError C₂ μ Q G g grid n<1 ∧
      ∀ (u:Vector (n+2)) (hu:‖u‖^2=(n+2:ℕ)),
        ∀ h₀ ∈ Icc (E-δ) (E+δ),∀ k₀ ∈ Icc L R,
        let c:=centerCoefficients (mixtureCoefficients μ) Q
        let ν:=mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])
        ENNReal.ofReal (1-sourceSelectionWeightError C₂ μ Q G g grid n)*
          (∫⁻ J,ENNReal.ofReal (intrinsicDet μ Q u J) ∂ν) ≤
          ∫⁻ J,ENNReal.ofReal (intrinsicDet μ Q u J) *
            sourceSelectionMark c (g/2) C ε η E G J u ∂ν:=by
  dsimp only
  let E:=markE μ β x Q
  let G:=gap μ Q (markY β Q) (markZ x Q) ε η
  let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge:0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q):=by
    simpa only [markB] using h.edge_margin.2.2
  have hg:0<g:=div_pos hedge (by norm_num)
  have hG:0<G:=(source_trial_gap μ h hnp hε hη hεη).1
  obtain ⟨L,R,δ,C,hL,hR,hgapL,hδ,hδG,hδMax',hC,grid,hgrid,hprob⟩:=
    source_mixed_physical_posterior_selection_failure μ h hnp hε hη hεη hδMax
  obtain ⟨C₂,hC₂,hmom⟩:=mixed_conditioned_determinant_moments μ h.overlap_range.1 hnp
    (g:=g) (Z:=R) (r:=2) hg (by norm_num)
  have herror:=sourceSelectionWeightError_tendsto C₂ μ h.overlap_range.1 hG hg grid
  refine ⟨L,R,δ,C,C₂,hL,hR,hgapL,hδ,hδG,hδMax',hC,hC₂,grid,hgrid,herror,?_⟩
  filter_upwards [hprob,herror.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))] with n hn herr
  refine ⟨herr,?_⟩
  intro u hu h₀ hh k₀ hk
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let ν:=mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])
  let :IsProbabilityMeasure ν:=by unfold ν mixedConditionedLaw;infer_instance
  obtain ⟨hD,_hmean,hm,hM,hMC⟩:=hmom n u hu (WithLp.toLp 2 ![h₀,k₀])
    (hgapL.le.trans hk.1) hk.2
  let B:={J:Disorder (n+2) μ.maxDegree|sourceSelectionEvent (N:=n+2) (P:=μ.maxDegree) c (g/2) C ε η E G J u}
  have hpair:Measurable (fun J:Disorder (n+2) μ.maxDegree=>(J,u)):=
    measurable_id.prodMk measurable_const
  have hjoint:=sourceSelectionEvent_measurable (N:=n+2) (P:=μ.maxDegree) c (g/2) C ε η E G
  have hB:=hjoint.preimage hpair
  have H:=sourceDeterminant_retained_weight_lower ν (intrinsicDet μ Q u) B hB hD
    (.of_forall (fun _=>abs_nonneg _)) hm hM hMC (hn u hu h₀ hh k₀ hk) herr.le
  convert H using 1
  · rfl
  · apply lintegral_congr
    intro J
    simp only [B,Set.indicator_apply,Set.mem_ofPred_eq,sourceSelectionMark]
    rfl

end
end SlowEquilibration.PairConditionalDeterminantMoments
