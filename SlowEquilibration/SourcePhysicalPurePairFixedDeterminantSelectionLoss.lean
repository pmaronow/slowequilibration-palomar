-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPurePairFixedSelectionFailure
public import SlowEquilibration.SourcePhysicalPurePairDeterminantSelectionLoss

/-! Own-determinant selection loss for the proper-pure value posterior,
with its regularity constant fixed before ε and η. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity ConditionedDeterminantMoments
open scoped ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Classical.propDecidable

theorem source_pure_physical_posterior_determinant_selection_loss_fixed_regularity
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q ε η δMax M C : ℝ}
    (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η)
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
    let G := gap μ Q (markY β Q) (markZ x Q) ε η
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ δ C₂ : ℝ, 0 < δ ∧ δ < G/4 ∧ δ ≤ δMax ∧ 0 < C₂ ∧
      ∃ grid : ℕ, 1 ≤ grid ∧
        Tendsto (sourceSelectionWeightError C₂ μ Q G g grid) atTop (𝓝 0) ∧
        ∀ᶠ n : ℕ in atTop,
          sourceSelectionWeightError C₂ μ Q G g grid n < 1 ∧
          ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
          ∀ h₀ ∈ Icc (E-δ) (E+δ),
            let c := centerCoefficients (mixtureCoefficients μ) Q
            let ν := valueConditionedLaw c u hu h₀
            ENNReal.ofReal (1-sourceSelectionWeightError C₂ μ Q G g grid n)*
              (∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) ∂ν) ≤
              ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J)*
                sourceSelectionMark c (g/2) C ε η E G J u ∂ν := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  have hG : 0 < G := (pure_source_trial_gap p hp a ha h hε hη hεη).1
  have hpR : (0:ℝ) < p := by exact_mod_cast (show 0<p by omega)
  let δBound := min δMax (g/(2*(p:ℝ)))
  have hδBound : 0 < δBound := lt_min hδMax (div_pos hg (by positivity))
  obtain ⟨δ,hδ,hδG,hδB,grid,hgrid,hprob⟩ :=
    source_pure_physical_posterior_selection_failure_fixed_regularity
      p hp a ha h hε hη hεη hδBound hC
      (by linarith [min_le_left δMax (g/(2*(p:ℝ)))]) hreg
  have hδMax' : δ ≤ δMax := hδB.trans (min_le_left _ _)
  have hδedge : δ ≤
      (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/(4*(p:ℝ)) := by
    have H := hδB.trans (min_le_right _ _)
    convert H using 1
    dsimp only [g]
    ring
  obtain ⟨C₂,hC₂,hmom⟩ :=
    pure_conditioned_determinant_moments p hp a ha h.overlap_range.1
      (g:=g) (Z:=(p:ℝ)*(E+δ)) (r:=2) hg (by norm_num)
  have herror :=
    sourceSelectionWeightError_tendsto C₂ μ h.overlap_range.1 hG hg grid
  refine ⟨δ,C₂,hδ,hδG,hδMax',hC₂,grid,hgrid,herror,?_⟩
  filter_upwards [hprob,
    herror.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num))]
    with n hn herr
  refine ⟨herr,?_⟩
  intro u hu h₀ hh
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let ν := valueConditionedLaw c u hu h₀
  let : IsProbabilityMeasure ν := by unfold ν valueConditionedLaw; infer_instance
  have hshift := source_pure_value_box_edge_margin
    p hp a ha h hδedge h₀ hh
  obtain ⟨hD,_hmean,hm,hM,hMC⟩ := hmom n u hu h₀ hshift
    (mul_le_mul_of_nonneg_left hh.2 hpR.le)
  let B := {J : Disorder (n+2) μ.maxDegree |
    sourceSelectionEvent (N:=n+2) (P:=μ.maxDegree) c (g/2) C ε η E G J u}
  have hpair : Measurable (fun J : Disorder (n+2) μ.maxDegree => (J,u)) :=
    measurable_id.prodMk measurable_const
  have hjoint := sourceSelectionEvent_measurable (N:=n+2) (P:=μ.maxDegree)
    c (g/2) C ε η E G
  have hB := hjoint.preimage hpair
  have H := sourceDeterminant_retained_weight_lower ν
    (intrinsicDet μ Q u) B hB hD
    (.of_forall (fun _ => abs_nonneg _)) hm hM hMC
    (hn u hu h₀ hh) herr.le
  convert H using 1
  · rfl
  · apply lintegral_congr
    intro J
    simp only [B,sourceSelectionMark]
    rfl

end
end SlowEquilibration.PairConditionalDeterminantMoments
