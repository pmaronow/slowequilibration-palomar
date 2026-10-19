-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairFixedSelectionFailure
public import SlowEquilibration.SourcePhysicalPairDeterminantSelectionLoss

/-! The original posterior determinant selection-loss argument with a
regularity constant fixed from a mark box before overlap parameters. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity ConditionedDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_mixed_physical_posterior_determinant_selection_loss_fixed_regularity
    (μ : FiniteMixture) {β x Q ε η δMax M C : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η) (hδMax : 0 < δMax)
    (hC : 0 < C)
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
    let G := gap μ Q (markY β Q) (markZ x Q) ε η
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
    let b₀ := markK μ β Q+1
    ∃ L R δ C₂ : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
      Icc L R ⊆ Ioo a₀ b₀ ∧ a₀ < L ∧ 0 < δ ∧ δ < G/4 ∧
      δ ≤ δMax ∧ 0 < C₂ ∧ ∃ grid : ℕ, 1 ≤ grid ∧
      Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, sourceSelectionWeightError C₂ μ Q G g grid n < 1 ∧
        ∀ (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)),
        ∀ h₀ ∈ Icc (E-δ) (E+δ), ∀ k₀ ∈ Icc L R,
          let c := centerCoefficients (mixtureCoefficients μ) Q
          let ν := mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])
          ENNReal.ofReal (1-sourceSelectionWeightError C₂ μ Q G g grid n)*
            (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) ∂ν) ≤
            ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
              sourceSelectionMark c (g/2) C ε η E G J u ∂ν := by
  dsimp only
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  have hG : 0 < G := (source_trial_gap μ h hnp hε hη hεη).1
  obtain ⟨L,R,δ,hL,hR,hsub,hδ,hδG,hδMax',grid,hgrid,hprob⟩ :=
    source_mixed_physical_posterior_selection_failure_fixed_regularity
      μ h hnp hε hη hεη hδMax hC hMbound hreg
  have hgapL : 2*Real.sqrt (Q^2*μ.xi2 Q)+g < L :=
    (hsub (show L ∈ Icc L R from ⟨le_rfl,hL.le.trans hR.le⟩)).1
  obtain ⟨C₂,hC₂,hmom⟩ := mixed_conditioned_determinant_moments
    μ h.overlap_range.1 hnp (g:=g) (Z:=R) (r:=2) hg (by norm_num)
  have herror := sourceSelectionWeightError_tendsto C₂ μ h.overlap_range.1 hG hg grid
  refine ⟨L,R,δ,C₂,hL,hR,hsub,hgapL,hδ,hδG,hδMax',hC₂,grid,hgrid,herror,?_⟩
  filter_upwards [hprob,herror.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with n hn herr
  refine ⟨herr,?_⟩
  intro u hu h₀ hh k₀ hk
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let ν := mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])
  let : IsProbabilityMeasure ν := by unfold ν mixedConditionedLaw; infer_instance
  obtain ⟨hD,_hmean,hm,hM,hMC⟩ := hmom n u hu (WithLp.toLp 2 ![h₀,k₀])
    (hgapL.le.trans hk.1) hk.2
  let B := {J : Disorder (n+2) μ.maxDegree |
    sourceSelectionEvent (N:=n+2) (P:=μ.maxDegree) c (g/2) C ε η E G J u}
  have hpair : Measurable (fun J : Disorder (n+2) μ.maxDegree => (J,u)) :=
    measurable_id.prodMk measurable_const
  have hjoint := sourceSelectionEvent_measurable (N:=n+2) (P:=μ.maxDegree)
    c (g/2) C ε η E G
  have hB := hjoint.preimage hpair
  have H := sourceDeterminant_retained_weight_lower ν (intrinsicDet μ Q u) B hB hD
    (.of_forall (fun _ => abs_nonneg _)) hm hM hMC (hn u hu h₀ hh k₀ hk) herr.le
  convert H using 1
  · rfl
  · apply lintegral_congr
    intro J
    simp only [B,sourceSelectionMark]
    rfl

end
end SlowEquilibration.PairConditionalDeterminantMoments
