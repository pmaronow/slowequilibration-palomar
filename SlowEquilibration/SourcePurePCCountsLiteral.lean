-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePurePCCountsN2
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Literal quantified form of manuscript `prop:pc-counts`: every N≥2,
the analytic center, an arbitrary Borel radial interval containing K₀ in
its interior, the outer M→∞ joint-ground limit, and high critical maxima. -/
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

theorem sourcePure_prop_pc_counts_literal
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (U : Set ℝ) (hU : MeasurableSet U)
    (hcontact : markK (FiniteMixture.pure p hp a ha) β Q ∈ interior U) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let K N R := physicalEnergyWindow N
      (Icc (sourcePureAnalyticCenter N E (β*x)-R)
        (sourcePureAnalyticCenter N E (β*x)+R)) U
    (∀ R : ℝ, 0 < R → ∃ B : ℝ, ∀ k : ℕ,
      (∫⁻ J, actualScoreWindowCount (k+1) c (K (k+2) R)
        (fun _ _ => 1) J ∂disorderLaw (k+2) μ.maxDegree) < ⊤ ∧
      (∫⁻ J, actualScoreWindowCount (k+1) c (K (k+2) R)
        (fun _ _ => 1) J ∂disorderLaw (k+2) μ.maxDegree).toReal ≤ B) ∧
    Tendsto (fun R : ℝ => Filter.liminf
      (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | actualScoreWindowCount (n+2) c (K (n+3) R)
          (fun _ _ => 1) J ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J ≤
            sourcePureAnalyticCenter (n+3) E (β*x)+R}) atTop)
      atTop (𝓝 (1 : ℝ)) ∧
    ∀ R : ℝ, 0 < R →
      Tendsto (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
          surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ K (n+3) R ∧
          ¬ NegativeDefinite (intrinsicHessian (field c J) y)})
        atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K (N : ℕ) (R : ℝ) := physicalEnergyWindow N
    (Icc (sourcePureAnalyticCenter N E (β*x)-R)
      (sourcePureAnalyticCenter N E (β*x)+R)) U
  obtain ⟨hCount,hGround,hBad⟩ :=
    sourcePure_prop_pc_counts_analytic p hp a ha h U hU hcontact
  refine ⟨?_,?_,hBad⟩
  · intro R hR
    obtain ⟨B,hB⟩ := hCount R hR
    let b₂ := (∫⁻ J, actualScoreWindowCount 1 c (K 2 R)
      (fun _ _ => 1) J ∂disorderLaw 2 μ.maxDegree).toReal
    have h₂ : (∫⁻ J, actualScoreWindowCount 1 c (K 2 R)
        (fun _ _ => 1) J ∂disorderLaw 2 μ.maxDegree) < ⊤ :=
      sourcePure_analytic_N2_critical_mean_finite p hp a ha h U hU R
    refine ⟨max B b₂,?_⟩
    intro k
    cases k with
    | zero =>
      exact ⟨h₂,le_max_right B b₂⟩
    | succ n =>
      obtain ⟨hf,hv⟩ := hB n
      constructor
      · simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using hf
      · have hv' : (∫⁻ J, actualScoreWindowCount (n+1+1) c
            (K (n+1+2) R) (fun _ _ => 1) J
            ∂disorderLaw (n+1+2) μ.maxDegree).toReal ≤ B := by
          simpa only [Nat.add_assoc] using hv
        exact hv'.trans (le_max_left B b₂)
  · let f (R : ℝ) := Filter.liminf
      (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | actualScoreWindowCount (n+2) c (K (n+3) R)
          (fun _ _ => 1) J ≠ 0 ∧
          sourceSphereMaximum (n+1) μ Q J ≤
            sourcePureAnalyticCenter (n+3) E (β*x)+R}) atTop
    have hUpper (R : ℝ) : f R ≤ 1 := by
      have hLow : IsBoundedUnder (· ≥ ·) atTop
          (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
            {J | actualScoreWindowCount (n+2) c (K (n+3) R)
              (fun _ _ => 1) J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J ≤
                sourcePureAnalyticCenter (n+3) E (β*x)+R}) :=
        isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
      have hTop : IsCoboundedUnder (· ≥ ·) atTop (fun _ : ℕ => (1 : ℝ)) :=
        (isBoundedUnder_of ⟨(1 : ℝ),fun n => le_refl (1 : ℝ)⟩ :
          IsBoundedUnder (· ≤ ·) atTop (fun _ : ℕ => (1 : ℝ))).isCoboundedUnder_ge
      have hh := Filter.liminf_le_liminf
        (Filter.Eventually.of_forall fun n : ℕ => (measureReal_le_one :
          (disorderLaw (n+3) μ.maxDegree).real
            {J | actualScoreWindowCount (n+2) c (K (n+3) R)
              (fun _ _ => 1) J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J ≤
                sourcePureAnalyticCenter (n+3) E (β*x)+R} ≤ 1)) hLow hTop
      simpa only [f,liminf_const] using hh
    have hLower : ∀ z : ℝ, 0 < z → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R ≥ R₀,
        1-z ≤ f R := by
      intro z hz
      obtain ⟨R₀,hR₀,hR⟩ := hGround z hz
      refine ⟨R₀,hR₀,?_⟩
      intro R hRR
      have hlt := hR R hRR
      have hpoint (n : ℕ) :
          (disorderLaw (n+3) μ.maxDegree).real
            {J | actualScoreWindowCount (n+2) c (K (n+3) R)
              (fun _ _ => 1) J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J <
                sourcePureAnalyticCenter (n+3) E (β*x)+R} ≤
          (disorderLaw (n+3) μ.maxDegree).real
            {J | actualScoreWindowCount (n+2) c (K (n+3) R)
              (fun _ _ => 1) J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J ≤
                sourcePureAnalyticCenter (n+3) E (β*x)+R} := by
        apply measureReal_mono
        · rintro J ⟨hcJ,hmJ⟩
          exact ⟨hcJ,hmJ.le⟩
        · exact measure_ne_top _ _
      have hLow : IsBoundedUnder (· ≥ ·) atTop
          (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
            {J | actualScoreWindowCount (n+2) c (K (n+3) R)
              (fun _ _ => 1) J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J <
                sourcePureAnalyticCenter (n+3) E (β*x)+R}) :=
        isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
      have hHigh : IsCoboundedUnder (· ≥ ·) atTop
          (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
            {J | actualScoreWindowCount (n+2) c (K (n+3) R)
              (fun _ _ => 1) J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J ≤
                sourcePureAnalyticCenter (n+3) E (β*x)+R}) :=
        (isBoundedUnder_of ⟨(1 : ℝ),fun n => measureReal_le_one⟩ :
          IsBoundedUnder (· ≤ ·) atTop _).isCoboundedUnder_ge
      exact hlt.trans (Filter.liminf_le_liminf
        (Filter.Eventually.of_forall hpoint) hLow hHigh)
    change Tendsto f atTop (𝓝 (1 : ℝ))
    apply tendsto_order.2
    constructor
    · intro r hr
      let z := (1-r)/2
      have hz : 0 < z := by dsimp [z]; linarith
      obtain ⟨R₀,hR₀,hR⟩ := hLower z hz
      filter_upwards [eventually_ge_atTop R₀] with R hRR
      have hh := hR R hRR
      have hzr : r < 1-z := by dsimp [z]; linarith
      exact hzr.trans_le hh
    · intro r hr
      filter_upwards [] with R
      exact (hUpper R).trans_lt hr

end SlowEquilibration.SphericalMarkedWindows
