-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureBadHessianSameCenter

/-! The exterior clipping is eventually automatic in a fixed physical
window, so every radial subwindow has no nonnegative-Hessian critical point
with probability tending to one. -/
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

theorem sourcePure_bad_hessian_raw_window_probability_tendsto_zero
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    {δ g : ℝ} (hδ : 0 < δ) (hg : 0 < g)
    (hLeft : 2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+g ≤
      (p : ℝ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
    (m : ℕ → ℝ) {M : ℝ} (hM : 0 < M)
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
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let K n := physicalEnergyWindow (n+3)
      (Icc (m (n+1)-L) (m (n+1)+L)) U
    Tendsto (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
      {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
        surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ K n ∧
        ¬ NegativeDefinite (intrinsicHessian (field c J) y)})
      atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let I (n : ℕ) := Icc (m (n+1)-L) (m (n+1)+L) ∩
    Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ))
  let K (n : ℕ) := physicalEnergyWindow (n+3) (I n) univ
  let V (n : ℕ) := physicalEnergyWindow (n+3)
    (Icc (m (n+1)-L) (m (n+1)+L)) U
  let P (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
      surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ V n ∧
      ¬ NegativeDefinite (intrinsicHessian (field c J) y)}
  let B (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
      surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ K n ∧
      ¬ NegativeDefinite (intrinsicHessian (field c J) y)}
  have hb : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-((j+2 : ℕ)*E-Real.log (j+2 : ℕ)/(2*(β*x)))| ≤ M := by
    filter_upwards [hunit] with j hj
    exact hj.2
  have hOff := (tendsto_add_atTop_nat 1).eventually
    (source_logarithmic_center_offset_bounds hb hM.le
      (half_pos hδ) m hcenter (-L) L)
  have hSub : ∀ᶠ n : ℕ in atTop,
      {J : Disorder (n+3) μ.maxDegree | ∃ y : Vector (n+3),
        ‖y‖^2=(n+3 : ℕ) ∧ surfaceGradient (field c J) y=0 ∧
        actualScore c J y ∈ V n ∧
        ¬ NegativeDefinite (intrinsicHessian (field c J) y)} ⊆
      {J | ∃ y : Vector (n+3), ‖y‖^2=(n+3 : ℕ) ∧
        surfaceGradient (field c J) y=0 ∧ actualScore c J y ∈ K n ∧
        ¬ NegativeDefinite (intrinsicHessian (field c J) y)} := by
    filter_upwards [hOff] with n hn
    rintro J ⟨y,hy,hcrit,hV,hbad⟩
    refine ⟨y,hy,hcrit,?_,hbad⟩
    change ((n+3 : ℕ) : ℝ)*(actualScore c J y) 0 ∈
        Icc (m (n+1)-L) (m (n+1)+L) ∧ (actualScore c J y) 1 ∈ U at hV
    change ((n+3 : ℕ) : ℝ)*(actualScore c J y) 0 ∈ I n ∧
      (actualScore c J y) 1 ∈ univ
    refine ⟨⟨hV.1,?_⟩,Set.mem_univ _⟩
    have hδh : 0 < δ/2 := half_pos hδ
    constructor
    · have hh : ((n+3 : ℕ) : ℝ)*(E-δ) < ((n+3 : ℕ) : ℝ)*(E-δ/2) := by
        have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
        nlinarith
      exact hh.trans_le (hn.1.trans hV.1.1)
    · have hh : ((n+3 : ℕ) : ℝ)*(E+δ/2) < ((n+3 : ℕ) : ℝ)*(E+δ) := by
        have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
        nlinarith
      exact (hV.1.2.trans hn.2).trans_lt hh
  have hBad : Tendsto B atTop (𝓝 (0 : ℝ)) :=
    sourcePure_bad_hessian_probability_tendsto_zero_of_center
      p hp a ha h hδ hg hLeft m hM hunit hcrit L hL
  apply tendsto_order.2
  constructor
  · intro r hr
    filter_upwards [] with n
    exact hr.trans_le measureReal_nonneg
  · intro r hr
    filter_upwards [hSub,hBad.eventually (gt_mem_nhds hr)] with n hsub hn
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans_lt hn

end SlowEquilibration.SphericalMarkedWindows
