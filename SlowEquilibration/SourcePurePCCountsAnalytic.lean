-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureAnalyticBadHessian

/-! Source `prop:pc-counts` in the original proper-pure field: one fixed
radial interval, the manuscript's explicit analytic center, bounded expected
critical counts, joint ground-state existence, and high critical maxima. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalPosteriorMaps SphericalForm SphereHessian NegativeDefiniteOperators
open TwoAtomStationarity SphericalTAPCertificate ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem sourcePure_prop_pc_counts_analytic
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (U : Set ℝ) (hU : MeasurableSet U)
    (hcontact : markK (FiniteMixture.pure p hp a ha) β Q ∈ interior U) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let K n R := physicalEnergyWindow (n+3)
      (Icc (sourcePureAnalyticCenter (n+3) E (β*x)-R)
        (sourcePureAnalyticCenter (n+3) E (β*x)+R)) U
    (∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ n : ℕ,
      (∫⁻ J, actualScoreWindowCount (n+2) c (K n R)
        (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
      (∫⁻ J, actualScoreWindowCount (n+2) c (K n R)
        (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal ≤ B) ∧
    (∀ z : ℝ, 0 < z → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R ≥ R₀,
      1-z ≤ Filter.liminf (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | actualScoreWindowCount (n+2) c (K n R)
          (fun _ _ => 1) J ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J <
            sourcePureAnalyticCenter (n+3) E (β*x)+R}) atTop) ∧
    ∀ R : ℝ, 0 < R →
      Tendsto (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
          surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ K n R ∧
          ¬ NegativeDefinite (intrinsicHessian (field c J) y)})
        atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K (n : ℕ) (R : ℝ) := physicalEnergyWindow (n+3)
    (Icc (sourcePureAnalyticCenter (n+3) E (β*x)-R)
      (sourcePureAnalyticCenter (n+3) E (β*x)+R)) U
  obtain ⟨m,M,C,cut,η,ε,δ,D,Usel,hM,hδ,hUsel,hOpen,hMark,hClosure,
    hcenter,hUnit,hLeft,hpδ,hUnfiltered,hMean,hMoments,hInputs,hRetEq,
    hCritMean,hCount,hTail,hJoint⟩ :=
    source_pure_actual_raw_score_and_upper_tail_same_witness p hp a ha h
  have hc : ∀ᶠ j : ℕ in atTop,
      |m j-sourcePureAnalyticCenter (j+2) E (β*x)| ≤ M := by
    simpa only [sourcePureAnalyticCenter] using hcenter
  have hcontact' : (p : ℝ)*E ∈ interior U := by
    rw [← source_pure_markK_eq_degree_mul_markE p hp a ha h]
    exact hcontact
  have hCount' : ∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ n : ℕ,
      let V := {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-R) R ∧
        b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))}
      (∫⁻ J, actualScoreWindowCount (n+2) c V (fun _ _ => 1) J
        ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
      (∫⁻ J, actualScoreWindowCount (n+2) c V (fun _ _ => 1) J
        ∂disorderLaw (n+3) μ.maxDegree).toReal ≤ B := by
    simpa only [hUsel] using hCount
  have hJoint' : ∀ z : ℝ, 0 < z → ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀,
      let V n := {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-L) L ∧
        b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))}
      1-z ≤ Filter.liminf (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | actualScoreWindowCount (n+2) c (V n) (fun _ _ => 1) J ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) atTop := by
    intro z hz
    obtain ⟨L₀,hL₀,hforall⟩ := hJoint z hz
    refine ⟨L₀,hL₀,?_⟩
    intro L hL
    simpa only [hUsel] using (hforall L hL).2
  refine ⟨?_,?_,?_⟩
  · intro R hR
    exact sourcePure_analytic_center_actual_count_uniform_of_selected
      p hp a ha h hδ hM m hc hCount' U hU R hR
  · exact sourcePure_analytic_center_joint_ground_of_selected
      p hp a ha h hM m hc hJoint' U hcontact'
  · have hg : 0 < (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2 := by
      have hedge : 0 < markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q) := by
        simpa only [markB] using h.edge_margin.2.2
      exact div_pos hedge (by norm_num)
    intro R hR
    exact sourcePure_analytic_bad_hessian_probability_tendsto_zero
      p hp a ha h hδ hg hM hLeft m hUnit hUnfiltered U R hR

end SlowEquilibration.SphericalMarkedWindows
