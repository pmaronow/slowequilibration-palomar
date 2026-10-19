-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairFixedMarkBox
public import SlowEquilibration.SourcePhysicalPairSelectionFailureProbability

/-! Reuse a posterior sphere-regularity constant fixed from a common mark
box before the overlap separation and band widths.  The Hessian and band
failure inputs remain the original physical posterior estimates. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity
open scoped ENNReal RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem source_mixed_physical_posterior_selection_failure_fixed_regularity
    (μ : FiniteMixture) {β x Q ε η δMax M C : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hε : 0 < ε) (hη : 0 < η) (hεη : ε < 1-η) (hδMax : 0 < δMax)
    (_hC : 0 < C)
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
    ∃ L R δ : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
      Icc L R ⊆ Ioo a₀ b₀ ∧ 0 < δ ∧ δ < G/4 ∧ δ ≤ δMax ∧
      ∃ grid : ℕ, 1 ≤ grid ∧ ∀ᶠ n : ℕ in atTop,
        ∀ (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)),
        ∀ h₀ ∈ Icc (E-δ) (E+δ), ∀ k₀ ∈ Icc L R,
          let c := centerCoefficients (mixtureCoefficients μ) Q
          (mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])).real
            {J | ¬sourceSelectionEvent c (g/2) C ε η E G J u} ≤
            sourceSelectionFailureRate μ Q G g grid n := by
  dsimp only
  let E := markE μ β x Q
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let a₀ := 2*Real.sqrt (Q^2*μ.xi2 Q)+g
  let b₀ := markK μ β Q+1
  change |E|+δMax+|a₀|+|b₀|+1 ≤ M at hMbound
  have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [markB] using h.edge_margin.2.2
  have hg : 0 < g := div_pos hedge (by norm_num)
  have ha : a₀ < markK μ β Q := by dsimp [a₀,g]; linarith
  have hb : markK μ β Q < b₀ := by dsimp [b₀]; linarith
  obtain ⟨L,R,δ,hL,hR,hsub,hδ,hδG,hδMax',K,_hK,grid,hgrid,hband⟩ :=
    source_mixed_physical_posterior_band_failure μ h hnp hε hη hεη ha hb hδMax
  refine ⟨L,R,δ,hL,hR,hsub,hδ,hδG,hδMax',grid,hgrid,?_⟩
  have hband' : ∀ᶠ n : ℕ in atTop, _ :=
    (tendsto_add_atTop_nat 1).eventually hband
  filter_upwards [hband',source_mixed_physical_posterior_hessian_margin
    μ h.overlap_range.1 hnp hg] with n hbandN hhess
  intro u hu h₀ hh k₀ hk
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let ν := mixedConditionedLaw c u hu (WithLp.toLp 2 ![h₀,k₀])
  let : IsProbabilityMeasure ν := by unfold ν mixedConditionedLaw; infer_instance
  have hhM : |h₀| ≤ M := by
    apply abs_le.mpr
    constructor <;> linarith [hh.1,hh.2,hδMax',hMbound,
      le_abs_self E,neg_le_abs E,abs_nonneg a₀,abs_nonneg b₀]
  have hk' := hsub hk
  have hkM : |k₀| ≤ M := by
    apply abs_le.mpr
    constructor <;> linarith [hk'.1,hk'.2,hMbound,
      le_abs_self b₀,neg_le_abs a₀,abs_nonneg E,abs_nonneg a₀,abs_nonneg b₀]
  have H := sourceSelectionEvent_failure_probability c (g/2) C ε η E G _ _ _ u ν
    (hhess u hu h₀ k₀ hk'.1.le)
    (hreg (n+1) u hu h₀ k₀ hhM hkM)
    (hbandN u hu h₀ hh k₀ hk)
  refine H.trans_eq ?_
  change _ = sourceSelectionFailureRate μ Q G g grid n
  unfold sourceBandFailureRate sourceSelectionFailureRate
  dsimp only [G]
  push_cast
  ring

end
end SlowEquilibration.PairConditionalDeterminantMoments
