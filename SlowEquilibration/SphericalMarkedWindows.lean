-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWindowGeometry
public import SlowEquilibration.PureConditionedHessian

/-! The actual global marked score-window Kac--Rice formulas. -/

@[expose] public section

namespace SlowEquilibration.SphericalMarkedWindows

open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.GaussianRegression
open SlowEquilibration.SphericalSequentialRegression SlowEquilibration.SphericalForm
open SlowEquilibration.SphereHessian SlowEquilibration.SphereChartVolume
open SlowEquilibration.SphericalKacRiceGluing SlowEquilibration.SphericalMorse
open SlowEquilibration.SphericalIntrinsicChartKacRice SlowEquilibration.SphericalIntrinsicKacRice
open SlowEquilibration.ValueTangentConditioning SlowEquilibration.PureConditionedHessian
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

lemma lintegral_window_of_ae_score {Ω B : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (q : Ω → B) (b : B) (hq : ∀ᵐ z ∂ν, q z = b)
    (K : Set B) (f g : Ω → ℝ≥0∞) :
    (∫⁻ z, f z * (if q z ∈ K then g z else 0) ∂ν) =
      if b ∈ K then ∫⁻ z, f z * g z ∂ν else 0 := by
  by_cases hb : b ∈ K
  · rw [ite_eq_left hb]
    apply lintegral_congr_ae
    filter_upwards [hq] with z hz
    simp only [hz, ite_eq_left hb]
  · rw [ite_eq_right hb]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hq] with z hz
    simp only [hz, ite_eq_right hb, mul_zero, Pi.zero_apply]

/-- The actual canonical full-disorder mixed conditioned law at `(N h,N k,0)`. -/
def mixedConditionedLaw {n P : ℕ} (c : Degree P → ℝ) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) (b : EuclideanSpace ℝ (Fin 2)) : Measure (Disorder (n+1) P) :=
  coefficientKernel (jointCLM c x (tangentFrame x hx))
    (jointScoreTarget n (((n+1 : ℕ) : ℝ) • b))

theorem mixedConditioned_score_ae {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) (b : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂mixedConditionedLaw c x hx b, actualScore c J x = b := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have h := coefficientKernel_observation_ae (jointCLM c x (tangentFrame x hx))
    (center_joint_surjective (by omega) μ hQ hnp x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx))
    (jointScoreTarget n (((n+1 : ℕ) : ℝ) • b))
  filter_upwards [h] with J hJ
  have hs : scoreCLM c x (euclideanDisorder J) = ((n+1 : ℕ) : ℝ) • b := by
    apply PiLp.ext
    intro i
    exact congrArg (fun v => v (Sum.inl i)) hJ
  unfold actualScore
  rw [hs, smul_smul, inv_mul_cancel₀ (show ((n+1 : ℕ) : ℝ) ≠ 0 by positivity), one_smul]

set_option backward.isDefEq.respectTransparency true in
/-- The true window indicator becomes the fixed mark indicator under the
canonical full-field posterior, for every score target. -/
theorem intrinsic_zero_score_window {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| *
      (if actualScore c J x ∈ K then psi J x else 0)
      ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ b in K, physicalScorePdf (n+1) μ Q b *
        ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
          ∂mixedConditionedLaw c x hx b := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hpsi_x : Measurable (fun J => psi J x) :=
    hpsi.comp (measurable_id.prodMk (measurable_const (a := x)))
  have hs_x : Measurable (fun J => actualScore c J x) := by
    simpa only [Function.comp_def, id_eq] using
      (actualScore_jointContinuous (N := n+1) c).measurable.comp
        (measurable_id.prodMk (measurable_const (a := x)))
  have hm : Measurable (fun J => ENNReal.ofReal |(intrinsicHessian (field c J) x).det| *
      (if actualScore c J x ∈ K then psi J x else 0)) := by
    apply Measurable.mul
    · exact intrinsicDet_measurable c x hx
    · exact Measurable.ite (hK.preimage hs_x) hpsi_x measurable_const
  dsimp only
  refine (intrinsic_zero_physical_score_disintegration μ hQ hnp x hx _ hm).trans ?_
  change (∫⁻ b, physicalScorePdf (n+1) μ Q b *
    ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| *
      (if actualScore c J x ∈ K then psi J x else 0) ∂mixedConditionedLaw c x hx b) = _
  calc
    _ = ∫⁻ b, K.indicator (fun b => physicalScorePdf (n+1) μ Q b *
        ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
          ∂mixedConditionedLaw c x hx b) b := by
      apply lintegral_congr
      intro b
      have he := lintegral_window_of_ae_score (mixedConditionedLaw c x hx b)
        (fun J => actualScore c J x) b (mixedConditioned_score_ae μ hQ hnp x hx b) K
        (fun J => ENNReal.ofReal |(intrinsicHessian (field c J) x).det|) (fun J => psi J x)
      calc
        _ = physicalScorePdf (n+1) μ Q b * (if b ∈ K then
            ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
              ∂mixedConditionedLaw c x hx b else 0) :=
          congrArg (fun t : ℝ≥0∞ => physicalScorePdf (n+1) μ Q b * t) he
        _ = _ := by
          by_cases hb : b ∈ K
          · simp only [Set.indicator_of_mem hb, ite_eq_left hb]
          · simp only [Set.indicator_of_notMem hb, ite_eq_right hb, mul_zero]
    _ = _ := lintegral_indicator hK _

/-- The source's iterated mixed score-window intensity on the actual sphere,
extended by zero outside that sphere in the ambient integral. -/
def mixedWindowIntensity (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞) (x : Vector (n+1)) : ℝ≥0∞ :=
  if hx : ‖x‖ ^ 2 = (n+1 : ℕ) then
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∫⁻ b in K, physicalScorePdf (n+1) μ Q b *
      ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
        ∂mixedConditionedLaw c x hx b
  else 0

/-- Actual nonpure score-window marked Kac--Rice, with arbitrary nonnegative
Borel whole-field marks, physical score density and uniform sphere law. -/
theorem actual_mixed_score_window_kacRice (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualScoreWindowCount n c K psi) (disorderLaw (n+1) μ.maxDegree) ∧
    (∫⁻ J, actualScoreWindowCount n c K psi J ∂disorderLaw (n+1) μ.maxDegree) =
      sphereKRPrefactor n μ Q * ∫⁻ x, mixedWindowIntensity n μ Q K psi x ∂sphereLaw (n+1) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm := scoreWindowMark_measurable c K hK psi hpsi
  have he := funext fun J => actualScoreWindowCount_eq_indicator n c K psi J
  constructor
  · rw [he]
    exact (actual_sphere_marked_kacRice n hn μ hQ _ hm).1
  · rw [he, actual_sphere_marked_kacRice_uniform n hn μ hQ _ hm]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [sphereLaw_support (show 1 ≤ n+1 by omega)] with x hx
    rw [mixedWindowIntensity, dite_eq_left hx]
    exact intrinsic_zero_score_window μ hQ hnp x hx K hK psi hpsi

end
end SlowEquilibration.SphericalMarkedWindows
