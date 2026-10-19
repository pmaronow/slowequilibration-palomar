-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalMarkedWindows

/-! Proper scalar-value and pure-model score-window marked Kac--Rice. -/

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

def actualValue {N P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) : ℝ :=
  field c J x / N

theorem actualValue_jointContinuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (fun p : Disorder N P × Vector N => actualValue c p.1 p.2) :=
  (field_jointContinuous c).div_const N

def actualValueWindowCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (I : Set ℝ)
    (psi : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞) (J : Disorder (n+1) P) : ℝ≥0∞ :=
  ∑' x : {x : Vector (n+1) | ‖x‖ ^ 2 = (n+1 : ℕ) ∧
    surfaceGradient (field c J) x = 0 ∧ actualValue c J x ∈ I}, psi J x

theorem actualValueWindowCount_eq_indicator {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (I : Set ℝ) (psi : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞) (J : Disorder (n+1) P) :
    actualValueWindowCount n c I psi J =
      actualSphereCount n c (fun J x => if actualValue c J x ∈ I then psi J x else 0) J := by
  classical
  unfold actualValueWindowCount actualSphereCount
  dsimp only
  rw [tsum_subtype]
  rw [tsum_subtype (f := fun x : Vector (n+1) =>
    if actualValue c J x ∈ I then psi J x else 0)]
  apply tsum_congr
  intro x
  by_cases hx : ‖x‖ ^ 2 = (n+1 : ℕ) <;>
    by_cases hg : surfaceGradient (field c J) x = 0 <;>
    by_cases hi : actualValue c J x ∈ I <;>
    simp only [Nat.cast_add, Nat.cast_one] at hx <;> simp [hx, hg, hi]

theorem valueWindowMark_measurable {N P : ℕ} (c : Degree P → ℝ)
    (I : Set ℝ) (hI : MeasurableSet I) (psi : Disorder N P → Vector N → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder N P × Vector N => psi p.1 p.2) :
    Measurable (fun p : Disorder N P × Vector N =>
      if actualValue c p.1 p.2 ∈ I then psi p.1 p.2 else 0) :=
  Measurable.ite (hI.preimage (actualValue_jointContinuous c).measurable) hpsi measurable_const

/-- The proper full-disorder law at the scalar-value target `(N h,0)`. -/
def valueConditionedLaw {n P : ℕ} (c : Degree P → ℝ) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) (b : ℝ) : Measure (Disorder (n+1) P) :=
  coefficientKernel (valueTangentCLM c x (tangentFrame x hx)) (jointValueTarget n ((n+1 : ℕ) * b))

theorem valueConditioned_value_ae {n : ℕ} (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ)) (b : ℝ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂valueConditionedLaw c x hx b, actualValue c J x = b := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have h := coefficientKernel_observation_ae (valueTangentCLM c x (tangentFrame x hx))
    (center_valueTangent_surjective (by omega) μ hQ x hx _
      (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx))
    (jointValueTarget n ((n+1 : ℕ) * b))
  filter_upwards [h] with J hJ
  have hv : field c J x = (n+1 : ℕ) * b := by
    have hi := congrArg (fun v => v (Sum.inl 0)) hJ
    simpa only [actualObservation, valueTangentCLM_apply_value, unpack_euclideanDisorder,
      jet, iteratedFDeriv_zero_apply, jointValueTarget, WithLp.toLp_ofLp, Sum.elim_inl] using hi
  rw [actualValue, hv]
  exact mul_div_cancel_left₀ b (show ((n+1 : ℕ) : ℝ) ≠ 0 by positivity)

theorem intrinsic_zero_value_window {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (I : Set ℝ) (hI : MeasurableSet I)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| *
      (if actualValue c J x ∈ I then psi J x else 0)
      ∂coefficientKernel (intrinsicGamma c x) 0) =
      ∫⁻ b in I, physicalValuePdf (n+1) μ Q b *
        ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
          ∂valueConditionedLaw c x hx b := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hpsi_x : Measurable (fun J => psi J x) :=
    hpsi.comp (measurable_id.prodMk (measurable_const (a := x)))
  have hs_x : Measurable (fun J => actualValue c J x) := by
    simpa only [Function.comp_def, id_eq] using
      (actualValue_jointContinuous (N := n+1) c).measurable.comp
        (measurable_id.prodMk (measurable_const (a := x)))
  have hm : Measurable (fun J => ENNReal.ofReal |(intrinsicHessian (field c J) x).det| *
      (if actualValue c J x ∈ I then psi J x else 0)) := by
    apply Measurable.mul
    · exact intrinsicDet_measurable c x hx
    · exact Measurable.ite (hI.preimage hs_x) hpsi_x measurable_const
  dsimp only
  refine (intrinsic_zero_physical_value_disintegration μ hQ x hx _ hm).trans ?_
  change (∫⁻ b, physicalValuePdf (n+1) μ Q b *
    ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| *
      (if actualValue c J x ∈ I then psi J x else 0) ∂valueConditionedLaw c x hx b) = _
  calc
    _ = ∫⁻ b, I.indicator (fun b => physicalValuePdf (n+1) μ Q b *
        ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
          ∂valueConditionedLaw c x hx b) b := by
      apply lintegral_congr
      intro b
      have he := lintegral_window_of_ae_score (valueConditionedLaw c x hx b)
        (fun J => actualValue c J x) b (valueConditioned_value_ae μ hQ x hx b) I
        (fun J => ENNReal.ofReal |(intrinsicHessian (field c J) x).det|) (fun J => psi J x)
      calc
        _ = physicalValuePdf (n+1) μ Q b * (if b ∈ I then
            ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
              ∂valueConditionedLaw c x hx b else 0) :=
          congrArg (fun t : ℝ≥0∞ => physicalValuePdf (n+1) μ Q b * t) he
        _ = _ := by
          by_cases hb : b ∈ I
          · simp only [Set.indicator_of_mem hb, ite_eq_left hb]
          · simp only [Set.indicator_of_notMem hb, ite_eq_right hb, mul_zero]
    _ = _ := lintegral_indicator hI _

def valueWindowIntensity (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (I : Set ℝ)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞) (x : Vector (n+1)) : ℝ≥0∞ :=
  if hx : ‖x‖ ^ 2 = (n+1 : ℕ) then
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∫⁻ b in I, physicalValuePdf (n+1) μ Q b *
      ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * psi J x
        ∂valueConditionedLaw c x hx b
  else 0

/-- Genuine scalar-value window formula; no nonpure hypothesis is needed. -/
theorem actual_value_window_kacRice (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (I : Set ℝ) (hI : MeasurableSet I)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × Vector (n+1) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualValueWindowCount n c I psi) (disorderLaw (n+1) μ.maxDegree) ∧
    (∫⁻ J, actualValueWindowCount n c I psi J ∂disorderLaw (n+1) μ.maxDegree) =
      sphereKRPrefactor n μ Q * ∫⁻ x, valueWindowIntensity n μ Q I psi x ∂sphereLaw (n+1) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hm := valueWindowMark_measurable c I hI psi hpsi
  have he := funext fun J => actualValueWindowCount_eq_indicator n c I psi J
  constructor
  · rw [he]
    exact (actual_sphere_marked_kacRice n hn μ hQ _ hm).1
  · rw [he, actual_sphere_marked_kacRice_uniform n hn μ hQ _ hm]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [sphereLaw_support (show 1 ≤ n+1 by omega)] with x hx
    rw [valueWindowIntensity, dite_eq_left hx]
    exact intrinsic_zero_value_window μ hQ x hx I hI psi hpsi

/-- The actual pure-model score lies on `(h,p h)`. -/
def pureScoreLine (p : ℕ) (h : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![h, (p : ℝ) * h]

def pureScoreWindow (p : ℕ) (K : Set (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  pureScoreLine p ⁻¹' K

theorem pureScoreWindow_measurable (p : ℕ) (K : Set (EuclideanSpace ℝ (Fin 2)))
    (hK : MeasurableSet K) : MeasurableSet (pureScoreWindow p K) := by
  apply hK.preimage
  have hc : Continuous (pureScoreLine p) := by
    change Continuous ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm ∘
      (fun h : ℝ => ![h, (p : ℝ) * h]))
    apply Continuous.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuous
    fun_prop
  exact hc.measurable

theorem actualScore_pure {N : ℕ} (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q : ℝ) (J : Disorder N (FiniteMixture.pure p hp alpha halpha).maxDegree) (x : Vector N) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q
    actualScore c J x = pureScoreLine p (actualValue c J x) := by
  let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q
  apply PiLp.ext
  intro i
  fin_cases i
  · change (N : ℝ)⁻¹ * scoreCLM c x (euclideanDisorder J) 0 = field c J x / N
    rw [scoreCLM_apply_zero, unpack_euclideanDisorder]
    change (N : ℝ)⁻¹ * field c J x = _
    ring
  · change (N : ℝ)⁻¹ * scoreCLM c x (euclideanDisorder J) 1 =
      (p : ℝ) * (field c J x / N)
    rw [scoreCLM_apply_one, unpack_euclideanDisorder, pure_radial_jet p hp alpha halpha Q J x]
    change (N : ℝ)⁻¹ * ((p : ℝ) * field c J x) = _
    ring

theorem actual_pure_scoreWindowCount_eq_valueWindowCount (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) (Q : ℝ) (K : Set (EuclideanSpace ℝ (Fin 2)))
    (psi : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree → Vector (n+1) → ℝ≥0∞)
    (J : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) Q
    actualScoreWindowCount n c K psi J = actualValueWindowCount n c (pureScoreWindow p K) psi J := by
  dsimp only
  rw [actualScoreWindowCount_eq_indicator, actualValueWindowCount_eq_indicator]
  congr 1
  funext J x
  rw [actualScore_pure p hp alpha halpha Q J x]
  rfl

/-- Actual pure score-window marked Kac--Rice, with the scalar Gaussian
density and the literal window `K_p={h | (h,p h)∈K}`. -/
theorem actual_pure_score_window_kacRice (n : ℕ) (hn : 1 ≤ n)
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (n+1) (FiniteMixture.pure p hp alpha halpha).maxDegree ×
      Vector (n+1) => psi z.1 z.2) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualScoreWindowCount n c K psi) (disorderLaw (n+1) μ.maxDegree) ∧
    (∫⁻ J, actualScoreWindowCount n c K psi J ∂disorderLaw (n+1) μ.maxDegree) =
      sphereKRPrefactor n μ Q *
        ∫⁻ x, valueWindowIntensity n μ Q (pureScoreWindow p K) psi x ∂sphereLaw (n+1) := by
  dsimp only
  have he := funext fun J => actual_pure_scoreWindowCount_eq_valueWindowCount n p hp alpha halpha Q K psi J
  rw [he]
  exact actual_value_window_kacRice n hn (FiniteMixture.pure p hp alpha halpha) hQ
    (pureScoreWindow p K) (pureScoreWindow_measurable p K hK) psi hpsi

end
end SlowEquilibration.SphericalMarkedWindows
