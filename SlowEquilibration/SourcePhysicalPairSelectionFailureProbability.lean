-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairBandFailureProbability
public import SlowEquilibration.SourcePhysicalPairHessianMarginProbability
public import SlowEquilibration.SourcePhysicalPairPosteriorSphereRegularity

/-! The original near-ground selection event has exponentially small
failure under its literal mixed critical posterior. Every component is
proved from the raw one-step certificate and the actual Gaussian laws. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity
open scoped RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def sourceSelectionFailureRate (μ:FiniteMixture) (Q G g:ℝ) (grid n:ℕ):ℝ:=
  2*(Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+2:ℕ)/2)+
    Real.exp (-(n+1:ℝ)*((g/2)/Real.sqrt (Q^2*μ.xi2 Q))^2/(16*Real.pi^2))+
    (grid+1:ℕ)*Real.exp (-(n+2:ℕ)*(G/8)^2/(2*μ.xi Q))

lemma sourceSelectionEvent_failure_subset {N P:ℕ} (c:Degree P→ℝ)
    (κ C ε η E G:ℝ) (u:Vector N) :
    {J:Disorder N P|¬sourceSelectionEvent c κ C ε η E G J u} ⊆
      {J|¬sourceHessianMargin c κ J u} ∪ {J|C<sourceSphereRegularity c J} ∪
      {J|¬sourceOverlapBandHeight c ε η ((N:ℝ)*(E-G/2)) J u}:=by
  intro J hJ
  by_cases hH:sourceHessianMargin c κ J u
  · by_cases hD:sourceSphereRegularity c J ≤ C
    · exact Or.inr (fun hB=>hJ ⟨hH,hD,hB⟩)
    · exact Or.inl (Or.inr (lt_of_not_ge hD))
  · exact Or.inl (Or.inl hH)

theorem sourceSelectionEvent_failure_probability {N P:ℕ} (c:Degree P→ℝ)
    (κ C ε η E G A B D:ℝ) (u:Vector N) (ν:Measure (Disorder N P)) [IsFiniteMeasure ν]
    (hH:ν.real {J|¬sourceHessianMargin c κ J u} ≤ A)
    (hD:ν.real {J|C<sourceSphereRegularity c J} ≤ B)
    (hB:ν.real {J|¬sourceOverlapBandHeight c ε η ((N:ℝ)*(E-G/2)) J u} ≤ D) :
    ν.real {J|¬sourceSelectionEvent c κ C ε η E G J u} ≤ A+B+D:=by
  refine (measureReal_mono (sourceSelectionEvent_failure_subset c κ C ε η E G u)).trans ?_
  exact (measureReal_union_le _ _).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add hH hD)) hB)

/-- Constants and the compact mark box are chosen before the dimension.
The spectral margin is derived from contact curvature; the full band,
derivative, and Hessian failures are genuine posterior estimates. -/
theorem source_mixed_physical_posterior_selection_failure (μ:FiniteMixture)
    {β x Q ε η δMax:ℝ} (h:Certificate μ β x Q)
    (hnp:μ.minDegree<μ.maxDegree) (hε:0<ε) (hη:0<η) (hεη:ε<1-η)
    (hδMax:0<δMax) :
    let E:=markE μ β x Q
    let G:=gap μ Q (markY β Q) (markZ x Q) ε η
    let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ L R δ C:ℝ,L < markK μ β Q ∧ markK μ β Q<R ∧
      2*Real.sqrt (Q^2*μ.xi2 Q)+g<L ∧ 0<δ ∧ δ<G/4 ∧ δ ≤ δMax ∧ 0<C ∧
      ∃ grid:ℕ,1 ≤ grid ∧ ∀ᶠ n:ℕ in atTop,
      ∀ (u:Vector (n+2)) (hu:‖u‖^2=(n+2:ℕ)),
        ∀ h₀ ∈ Icc (E-δ) (E+δ),∀ k₀ ∈ Icc L R,
        let c:=centerCoefficients (mixtureCoefficients μ) Q
        (mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])).real
          {J|¬sourceSelectionEvent c (g/2) C ε η E G J u} ≤
          sourceSelectionFailureRate μ Q G g grid n:=by
  dsimp only
  let E:=markE μ β x Q
  let G:=gap μ Q (markY β Q) (markZ x Q) ε η
  let g:=(markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge:0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q):=by
    simpa only [markB] using h.edge_margin.2.2
  have hg:0<g:=div_pos hedge (by norm_num)
  have ha:2*Real.sqrt (Q^2*μ.xi2 Q)+g < markK μ β Q:=by dsimp [g];linarith
  obtain ⟨L,R,δ,hL,hR,hsub,hδ,hδG,hδMax',K,hK,grid,hgrid,hband⟩:=
    source_mixed_physical_posterior_band_failure μ h hnp hε hη hεη ha
      (show markK μ β Q < markK μ β Q+1 by linarith) hδMax
  have hgapL:2*Real.sqrt (Q^2*μ.xi2 Q)+g<L:=
    (hsub (show L ∈ Icc L R from ⟨le_rfl,hL.le.trans hR.le⟩)).1
  let M:=|E|+δ+|L|+|R|+1
  have hM:0 ≤ M:=by dsimp [M];positivity
  obtain ⟨C,hC,hreg⟩:=source_mixed_physical_posterior_sphere_regularity μ h.overlap_range.1 hnp hM
  refine ⟨L,R,δ,C,hL,hR,hgapL,hδ,hδG,hδMax',hC,grid,hgrid,?_⟩
  have hband':∀ᶠ n:ℕ in atTop,_:=(tendsto_add_atTop_nat 1).eventually hband
  filter_upwards [hband',source_mixed_physical_posterior_hessian_margin μ h.overlap_range.1 hnp hg]
    with n hbandN hhess
  intro u hu h₀ hh k₀ hk
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let ν:=mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])
  let :IsProbabilityMeasure ν:=by unfold ν mixedConditionedLaw;infer_instance
  have hhM:|h₀| ≤ M:=by
    apply abs_le.mpr
    constructor <;> dsimp [M] <;> linarith [hh.1,hh.2,le_abs_self E,neg_le_abs E,abs_nonneg L,abs_nonneg R]
  have hkM:|k₀| ≤ M:=by
    apply abs_le.mpr
    constructor <;> dsimp [M] <;> linarith [hk.1,hk.2,le_abs_self R,neg_le_abs L,abs_nonneg E,abs_nonneg L,abs_nonneg R]
  have H:=sourceSelectionEvent_failure_probability c (g/2) C ε η E G _ _ _ u ν
    (hhess u hu h₀ k₀ (hgapL.le.trans hk.1)) (hreg (n+1) u hu h₀ k₀ hhM hkM)
    (hbandN u hu h₀ hh k₀ hk)
  refine H.trans_eq ?_
  change _ = sourceSelectionFailureRate μ Q G g grid n
  unfold sourceBandFailureRate sourceSelectionFailureRate
  dsimp only [G]
  push_cast
  ring

end
end SlowEquilibration.PairConditionalDeterminantMoments
