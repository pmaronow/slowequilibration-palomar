-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureAnalyticGroundGeometry

/-! The selected-center joint-ground event implies the source §9 event at
the explicit analytic center and any fixed radial neighborhood of K₀. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 750000

theorem sourcePure_analytic_center_joint_ground_of_selected
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {δ M : ℝ} (hM : 0 < M) (m : ℕ → ℝ)
    (hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-sourcePureAnalyticCenter (j+2)
        (markE (FiniteMixture.pure p hp a ha) β x Q) (β*x)| ≤ M)
    (hjoint : ∀ z : ℝ, 0 < z → ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀,
      let μ := FiniteMixture.pure p hp a ha
      let E := markE μ β x Q
      let V n := sourcePureCenteredRawNormalizedWindow n m (-L) L
      let K n := {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ V n ∧ b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))}
      1-z ≤ Filter.liminf (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) (K n)
          (fun _ _ => 1) J ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) atTop)
    (U : Set ℝ)
    (hU : (p : ℝ)*markE (FiniteMixture.pure p hp a ha) β x Q ∈ interior U) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    ∀ z : ℝ, 0 < z → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R ≥ R₀,
      let V n := physicalEnergyWindow (n+3)
        (Icc (sourcePureAnalyticCenter (n+3) E (β*x)-R)
          (sourcePureAnalyticCenter (n+3) E (β*x)+R)) U
      1-z ≤ Filter.liminf (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) (V n)
          (fun _ _ => 1) J ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J <
            sourcePureAnalyticCenter (n+3) E (β*x)+R}) atTop := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hb : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  intro z hz
  obtain ⟨L₀,hL₀,hLimsup⟩ := hjoint z hz
  refine ⟨L₀+M,by linarith,?_⟩
  intro R hR
  let L := R-M
  have hLge : L₀ ≤ L := by dsimp [L]; linarith
  let K (n : ℕ) := {b : EuclideanSpace ℝ (Fin 2) |
    b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-L) L ∧
    b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))}
  let V (n : ℕ) := physicalEnergyWindow (n+3)
    (Icc (sourcePureAnalyticCenter (n+3) E (β*x)-R)
      (sourcePureAnalyticCenter (n+3) E (β*x)+R)) U
  let P (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | actualScoreWindowCount (n+2) c (K n) (fun _ _ => 1) J ≠ 0 ∧
      sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}
  let B (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | actualScoreWindowCount (n+2) c (V n) (fun _ _ => 1) J ≠ 0 ∧
      sourceSphereMaximum (n+1) μ Q J <
        sourcePureAnalyticCenter (n+3) E (β*x)+R}
  have hGeom := sourcePure_selected_window_eventually_in_analytic_window
    p hp hb hM.le m hcenter U hU (L := L) (δ := δ)
  have hshift := (tendsto_add_atTop_nat 1).eventually hcenter
  have hP : ∀ᶠ n : ℕ in atTop, P n ≤ B n := by
    filter_upwards [hGeom,hshift] with n hline hcenterN
    have hRsum : L+M=R := by dsimp [L]; ring
    have hline' : pureScoreWindow p (K n) ⊆ pureScoreWindow p (V n) := by
      simpa only [K,V,E,μ,hRsum,Nat.add_comm,sub_eq_add_neg,add_comm] using hline
    have hCount (J : Disorder (n+3) μ.maxDegree) :=
      pure_actualScoreWindowCount_mono_of_line (n+2) p hp a ha Q
        (K n) (V n) hline' J
    have hset : {J : Disorder (n+3) μ.maxDegree |
        actualScoreWindowCount (n+2) c (K n) (fun _ _ => 1) J ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J < m (n+1)+L} ⊆
      {J | actualScoreWindowCount (n+2) c (V n) (fun _ _ => 1) J ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J <
            sourcePureAnalyticCenter (n+3) E (β*x)+R} := by
      intro J hJ
      change actualScoreWindowCount (n+2) c (K n) (fun _ _ => 1) J ≠ 0 ∧
        sourceSphereMaximum (n+1) μ Q J < m (n+1)+L at hJ
      constructor
      · intro hzero
        have hh := hCount J
        rw [hzero] at hh
        exact hJ.1 (le_antisymm hh bot_le)
      · have hcenterN' := (abs_le.mp hcenterN).2
        simp only [sourcePureAnalyticCenter,show n+1+2=n+3 by omega] at hcenterN'
        dsimp [sourcePureAnalyticCenter] at ⊢
        linarith [hJ.2,hRsum]
    exact measureReal_mono hset (measure_ne_top _ _)
  have hLow : IsBoundedUnder (· ≥ ·) atTop P :=
    isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
  have hHigh : IsCoboundedUnder (· ≥ ·) atTop B :=
    (isBoundedUnder_of ⟨(1 : ℝ),fun n => measureReal_le_one⟩ :
      IsBoundedUnder (· ≤ ·) atTop B).isCoboundedUnder_ge
  have hbase : 1-z ≤ Filter.liminf P atTop := by
    simpa only [P,K,E,μ,c,L] using hLimsup L hLge
  exact hbase.trans (Filter.liminf_le_liminf hP hLow hHigh)

end SlowEquilibration.SphericalMarkedWindows
