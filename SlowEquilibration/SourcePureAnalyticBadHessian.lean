-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureAnalyticGroundTransfer

/-! Source `prop:pc-counts` high-critical assertion at its literal analytic
logarithmic center: every critical point in any fixed raw energy/radial
window is a strictly negative-Hessian maximum with probability tending to one. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open SphericalPosteriorMaps SphericalForm SphereHessian NegativeDefiniteOperators
open TwoAtomStationarity SphericalTAPCertificate ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem sourcePure_analytic_bad_hessian_probability_tendsto_zero
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {δ g M : ℝ} (hδ : 0 < δ) (hg : 0 < g) (hM : 0 < M)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤
      (p : ℝ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
    (m : ℕ → ℝ)
    (hunit : ∀ᶠ n : ℕ in atTop,
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
        ((n+2 : ℕ)*(markE (FiniteMixture.pure p hp a ha) β x Q+δ))) (m n)=1 ∧
      |m n-((n+2 : ℕ)*markE (FiniteMixture.pure p hp a ha) β x Q-
        Real.log (n+2 : ℕ)/(2*(β*x)))| ≤ M)
    (hcrit : ∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
      sourceUnfilteredValueWindowMean (n+2) (FiniteMixture.pure p hp a ha) Q
        (sourcePureCenteredNormalizedWindow n m
          (markE (FiniteMixture.pure p hp a ha) β x Q) δ L R))
      atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R))))
    (U : Set ℝ) (L : ℝ) (hL : 0 < L) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let K n := physicalEnergyWindow (n+3)
      (Icc (sourcePureAnalyticCenter (n+3) E (β*x)-L)
        (sourcePureAnalyticCenter (n+3) E (β*x)+L)) U
    Tendsto (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
      {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
        surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ K n ∧
        ¬ NegativeDefinite (intrinsicHessian (field c J) y)})
      atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K (n : ℕ) := physicalEnergyWindow (n+3)
    (Icc (sourcePureAnalyticCenter (n+3) E (β*x)-L)
      (sourcePureAnalyticCenter (n+3) E (β*x)+L)) U
  let V (n : ℕ) := physicalEnergyWindow (n+3)
    (Icc (m (n+1)-(L+M)) (m (n+1)+(L+M))) univ
  let P (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
      surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ K n ∧
      ¬ NegativeDefinite (intrinsicHessian (field c J) y)}
  let B (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
      surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ V n ∧
      ¬ NegativeDefinite (intrinsicHessian (field c J) y)}
  have hb : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-sourcePureAnalyticCenter (j+2) E (β*x)| ≤ M := by
    simpa only [sourcePureAnalyticCenter] using hunit.mono (fun j hj => hj.2)
  have hGeom := sourcePure_analytic_window_eventually_in_selected_box
    (L := L) hb hM.le hδ m hcenter
  have hBad : Tendsto B atTop (𝓝 (0 : ℝ)) :=
    sourcePure_bad_hessian_raw_window_probability_tendsto_zero
      p hp a ha h hδ hg hLeft m hM hunit hcrit univ (L+M) (by linarith)
  have hSub : ∀ᶠ n : ℕ in atTop,
      {J : Disorder (n+3) μ.maxDegree | ∃ y : Vector (n+3),
        ‖y‖^2=(n+3 : ℕ) ∧ surfaceGradient (field c J) y=0 ∧
        actualScore c J y ∈ K n ∧
        ¬ NegativeDefinite (intrinsicHessian (field c J) y)} ⊆
      {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
        surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ V n ∧
        ¬ NegativeDefinite (intrinsicHessian (field c J) y)} := by
    filter_upwards [hGeom] with n hn
    rintro J ⟨y,hy,hcrit,hK,hbad⟩
    refine ⟨y,hy,hcrit,?_,hbad⟩
    change ((n+3 : ℕ) : ℝ)*(actualScore c J y) 0 ∈
        Icc (sourcePureAnalyticCenter (n+3) E (β*x)-L)
          (sourcePureAnalyticCenter (n+3) E (β*x)+L) ∧
      (actualScore c J y) 1 ∈ U at hK
    change ((n+3 : ℕ) : ℝ)*(actualScore c J y) 0 ∈
        Icc (m (n+1)-(L+M)) (m (n+1)+(L+M)) ∧
      (actualScore c J y) 1 ∈ univ
    exact ⟨(hn hK.1).1,Set.mem_univ _⟩
  apply tendsto_order.2
  constructor
  · intro r hr
    filter_upwards [] with n
    exact hr.trans_le measureReal_nonneg
  · intro r hr
    filter_upwards [hSub,hBad.eventually (gt_mem_nhds hr)] with n hsub hn
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans_lt hn

end SlowEquilibration.SphericalMarkedWindows
