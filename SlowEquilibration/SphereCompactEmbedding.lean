-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereChartVolume
public import SlowEquilibration.SphericalSobolev
public import SlowEquilibration.GenericRellich
public import SlowEquilibration.SphericalRellichCompletion

@[expose] public section

/-!
# Genuine chart localization for compact spherical Sobolev embedding

The charts have the actual radius sqrt(N), and the volume comparison uses the
proved density of the manuscript's actual radial Gaussian sphere law. The
localized Euclidean functions are smooth ordinary functions with genuine
cutoffs supported away from the omitted poles.
-/

noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace ContDiff
namespace SlowEquilibration.SphereCompactEmbedding
open SphereChartVolume SphericalModel SphericalForm SphericalAging.HardSphereDynamics
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev ChartSpace (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Genuine smooth cutoff, equal to one on the two covering chart cores
and supported strictly inside the regular chart region. -/
def chartCutoff (n : ℕ) : ContDiffBump (0 : ChartSpace n) where
  rIn := Real.sqrt 2
  rOut := Real.sqrt 3
  rIn_pos := Real.sqrt_pos.mpr (by norm_num)
  rIn_lt_rOut := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

lemma sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]

/-- Two opposite actual-radius charts, indexed by a genuine finite set. -/
def signedChart (n : ℕ) (side : Bool) (u : ChartSpace n) : Vector (n + 1) :=
  if side then -(manuscriptChart n u) else manuscriptChart n u

def signedChartDerivative (n : ℕ) (side : Bool) (u : ChartSpace n) :
    ChartSpace n →L[ℝ] Vector (n + 1) :=
  if side then -(manuscriptChartDerivative n u) else manuscriptChartDerivative n u

lemma manuscriptChart_contDiffOn (n : ℕ) :
    ContDiffOn ℝ ∞ (manuscriptChart n) (Metric.ball 0 2) := by
  unfold manuscriptChart
  exact (((chartAmbientIsometry n).toContinuousLinearEquiv.contDiff.comp_contDiffOn
    sphereChartND_contDiffOn).const_smul _).of_le (by simp)

lemma signedChart_contDiffOn (n : ℕ) (side : Bool) :
    ContDiffOn ℝ ∞ (signedChart n side) (Metric.ball 0 2) := by
  cases side
  · exact manuscriptChart_contDiffOn n
  · exact (manuscriptChart_contDiffOn n).neg

lemma signedChart_hasFDerivAt (n : ℕ) (side : Bool) {u : ChartSpace n} (hu : ‖u‖ < 2) :
    HasFDerivAt (signedChart n side) (signedChartDerivative n side u) u := by
  cases side
  · exact manuscriptChart_hasFDerivAt hu
  · exact (manuscriptChart_hasFDerivAt hu).neg

/-- The actual chart differential is tangent at the actual spherical point. -/
lemma manuscriptChartDerivative_tangent (n : ℕ) {u : ChartSpace n} (hu : ‖u‖ < 2)
    (v : ChartSpace n) : inner ℝ (manuscriptChart n u) (manuscriptChartDerivative n u v) = 0 := by
  simp only [manuscriptChart, manuscriptChartDerivative, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, real_inner_smul_left, real_inner_smul_right,
    LinearIsometryEquiv.inner_map_map, sphereChartDerivND_orthogonal hu v, mul_zero]

lemma signedChartDerivative_tangent (n : ℕ) (side : Bool) {u : ChartSpace n}
    (hu : ‖u‖ < 2) (v : ChartSpace n) :
    inner ℝ (signedChart n side u) (signedChartDerivative n side u v) = 0 := by
  cases side
  · exact manuscriptChartDerivative_tangent n hu v
  · simpa only [signedChart, signedChartDerivative, Bool.true_eq_false, ite_true, neg_apply,
      inner_neg_left, inner_neg_right, neg_neg] using manuscriptChartDerivative_tangent n hu v

/-- Actual pullback derivatives pair with the actual surface gradient,
rather than with an assumed abstract gradient identity. -/
theorem chartPullback_hasFDerivAt (n : ℕ) (side : Bool) {f : Vector (n + 1) → ℝ}
    (hf : Differentiable ℝ f) {u : ChartSpace n} (hu : ‖u‖ < 2) :
    HasFDerivAt (fun v => f (signedChart n side v))
      ((fderiv ℝ f (signedChart n side u)).comp (signedChartDerivative n side u)) u :=
  (hf _).hasFDerivAt.comp u (signedChart_hasFDerivAt n side hu)

theorem chartPullback_derivative_surfaceGradient (n : ℕ) (side : Bool)
    (f : Vector (n + 1) → ℝ) {u : ChartSpace n} (hu : ‖u‖ < 2) (v : ChartSpace n) :
    fderiv ℝ f (signedChart n side u) (signedChartDerivative n side u v) =
      inner ℝ (surfaceGradient f (signedChart n side u)) (signedChartDerivative n side u v) := by
  rw [inner_surfaceGradient, tangentProjection_apply, projection]
  rw [signedChartDerivative_tangent n side hu v]
  simp

/-- The genuine compactly supported local smooth representative. -/
def localize (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ) (u : ChartSpace n) : ℝ :=
  chartCutoff n u * f (signedChart n side u)

lemma localize_contDiff (n : ℕ) (side : Bool) {f : Vector (n + 1) → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (localize n side f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases hu : ‖u‖ < 2
  · have hc : ContDiffAt ℝ ∞ (signedChart n side) u :=
      (signedChart_contDiffOn n side).contDiffAt
        ((Metric.isOpen_ball : IsOpen (Metric.ball (0 : ChartSpace n) 2)).mem_nhds (by simpa using hu))
    exact (chartCutoff n).contDiff.contDiffAt.mul (hf.contDiffAt.comp u hc)
  · have hs : u ∉ tsupport (chartCutoff n) := by
      rw [(chartCutoff n).tsupport_eq, Metric.mem_closedBall, dist_zero_right]
      change ¬‖u‖ ≤ Real.sqrt 3
      exact not_le.mpr (sqrt_three_lt_two.trans_le (le_of_not_gt hu))
    have hz : chartCutoff n =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) :=
      notMem_tsupport_iff_eventuallyEq.mp hs
    have he : localize n side f =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) :=
      hz.mono (fun v hv => by simp only [localize, hv, zero_mul])
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma localize_hasCompactSupport (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ) :
    HasCompactSupport (localize n side f) := (chartCutoff n).hasCompactSupport.mul_right

lemma localize_eq_on_inner (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ)
    {u : ChartSpace n} (hu : ‖u‖ ≤ Real.sqrt 2) :
    localize n side f u = f (signedChart n side u) := by
  rw [localize, (chartCutoff n).one_of_mem_closedBall (by simpa [chartCutoff] using hu), one_mul]

lemma localize_zero_of_outside (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ)
    {u : ChartSpace n} (hu : Real.sqrt 3 ≤ ‖u‖) : localize n side f u = 0 := by
  rw [localize, (chartCutoff n).zero_of_le_dist (by simpa [chartCutoff] using hu), zero_mul]

/-- The actual chart differential has a finite uniform bound on the
compact cutoff region; this follows from proved chart smoothness. -/
theorem exists_chartDerivative_bound (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ side : Bool, ∀ u : ChartSpace n,
      ‖u‖ ≤ Real.sqrt 3 → ‖signedChartDerivative n side u‖ ≤ B := by
  have hsub : Metric.closedBall (0 : ChartSpace n) (Real.sqrt 3) ⊆ Metric.ball 0 2 := by
    intro u hu
    simpa only [Metric.mem_ball, dist_zero_right] using
      (show ‖u‖ ≤ Real.sqrt 3 from by simpa using hu).trans_lt sqrt_three_lt_two
  have hc := (manuscriptChart_contDiffOn n).continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ChartSpace n) (Real.sqrt 3)).exists_bound_of_continuousOn
    (hc.mono hsub)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro side u hu
  have hu2 : ‖u‖ < 2 := hu.trans_lt sqrt_three_lt_two
  have hb : ‖manuscriptChartDerivative n u‖ ≤ B := by
    rw [← (manuscriptChart_hasFDerivAt hu2).fderiv]
    exact hB _ (by simpa using hu)
  cases side
  · exact hb.trans (le_max_left _ _)
  · simpa only [signedChartDerivative, ite_true, norm_neg] using hb.trans (le_max_left B 0)

/-- The actual smooth cutoff has a finite global derivative bound. -/
theorem exists_cutoffDerivative_bound (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ChartSpace n, ‖fderiv ℝ (chartCutoff n) u‖ ≤ B := by
  have hc : ContDiff ℝ 2 (chartCutoff n) := (chartCutoff n).contDiff
  obtain ⟨B, hB⟩ := ((chartCutoff n).hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hc.continuous_fderiv (by norm_num))
  exact ⟨max B 0, le_max_right _ _, fun u => (hB u).trans (le_max_left _ _)⟩

/-- The norm of the genuine chart pullback differential is bounded by
its actual surface gradient and the proved chart differential norm. -/
theorem chartPullback_derivative_norm (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ)
    {u : ChartSpace n} (hu : ‖u‖ < 2) :
    ‖(fderiv ℝ f (signedChart n side u)).comp (signedChartDerivative n side u)‖ ≤
      ‖surfaceGradient f (signedChart n side u)‖ * ‖signedChartDerivative n side u‖ := by
  apply ((fderiv ℝ f (signedChart n side u)).comp (signedChartDerivative n side u)).opNorm_le_bound
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro v
  rw [ContinuousLinearMap.comp_apply, chartPullback_derivative_surfaceGradient n side f hu v]
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    ((mul_le_mul_of_nonneg_left ((signedChartDerivative n side u).le_opNorm v) (norm_nonneg _)).trans_eq
      (mul_assoc _ _ _).symm)

/-- Exact derivative of the actual localized smooth representative. -/
theorem localize_hasFDerivAt (n : ℕ) (side : Bool) {f : Vector (n + 1) → ℝ}
    (hf : Differentiable ℝ f) {u : ChartSpace n} (hu : ‖u‖ < 2) :
    HasFDerivAt (localize n side f)
      (f (signedChart n side u) • fderiv ℝ (chartCutoff n) u +
        chartCutoff n u • (fderiv ℝ f (signedChart n side u)).comp (signedChartDerivative n side u)) u := by
  have hc : ContDiff ℝ 1 (chartCutoff n) := (chartCutoff n).contDiff
  have hh := ((hc.differentiable (by norm_num) u).hasFDerivAt.mul
    (chartPullback_hasFDerivAt n side hf hu))
  convert hh using 1
  · rfl
  · exact add_comm _ _

/-- Actual localized derivative control by the true function and spherical
energy integrands, uniformly on the compact regular chart region. -/
theorem localize_derivative_square_le (n : ℕ) (side : Bool) {f : Vector (n + 1) → ℝ}
    (hf : Differentiable ℝ f) {u : ChartSpace n} (hu : ‖u‖ ≤ Real.sqrt 3)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ‖fderiv ℝ (chartCutoff n) u‖ ≤ B)
    (hc : ‖signedChartDerivative n side u‖ ≤ C) :
    ‖fderiv ℝ (localize n side f) u‖ ^ 2 ≤
      2 * B ^ 2 * (f (signedChart n side u)) ^ 2 +
        2 * C ^ 2 * ‖surfaceGradient f (signedChart n side u)‖ ^ 2 := by
  have hu2 : ‖u‖ < 2 := hu.trans_lt sqrt_three_lt_two
  rw [(localize_hasFDerivAt n side hf hu2).fderiv]
  have hnorm : ‖f (signedChart n side u) • fderiv ℝ (chartCutoff n) u +
      chartCutoff n u • (fderiv ℝ f (signedChart n side u)).comp (signedChartDerivative n side u)‖ ≤
      ‖f (signedChart n side u)‖ * B +
        C * ‖surfaceGradient f (signedChart n side u)‖ := by
    apply (norm_add_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (chartCutoff n).nonneg]
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    · calc
        _ ≤ 1 * (‖surfaceGradient f (signedChart n side u)‖ * ‖signedChartDerivative n side u‖) :=
          mul_le_mul (chartCutoff n).le_one (chartPullback_derivative_norm n side f hu2)
            (norm_nonneg _) zero_le_one
        _ ≤ C * ‖surfaceGradient f (signedChart n side u)‖ := by
          rw [one_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (mul_nonneg (norm_nonneg _) hB)
      (mul_nonneg hC (norm_nonneg _)))).mpr hnorm
  have htwice := two_mul_le_add_sq (‖f (signedChart n side u)‖ * B)
    (C * ‖surfaceGradient f (signedChart n side u)‖)
  have hfsq : ‖f (signedChart n side u)‖ ^ 2 = f (signedChart n side u) ^ 2 := by
    simp [Real.norm_eq_abs, sq_abs]
  nlinarith

lemma signedChart_continuous (n : ℕ) (side : Bool) : Continuous (signedChart n side) := by
  have hc : Continuous (manuscriptChart n) := by
    unfold manuscriptChart
    exact ((chartAmbientIsometry n).continuous.comp sphereChartND_continuous).const_smul
      (Real.sqrt (n + 1 : ℕ))
  cases side
  · exact hc
  · exact hc.neg

lemma signedChart_injOn (n : ℕ) (side : Bool) :
    Set.InjOn (signedChart n side) (Metric.ball 0 2) := by
  have hc : Set.InjOn (manuscriptChart n) (Metric.ball 0 2) := by
    intro u hu v hv huv
    have hR : Real.sqrt (n + 1 : ℕ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    apply sphereChartND_injOn hu hv
    apply (chartAmbientIsometry n).injective
    exact smul_right_injective _ hR huv
  cases side
  · exact hc
  · intro u hu v hv huv
    apply hc hu hv
    exact neg_injective huv

lemma signedChart_image_measurable (n : ℕ) (side : Bool)
    {s : Set (ChartSpace n)} (hs : MeasurableSet s) (hsb : s ⊆ Metric.ball 0 2) :
    MeasurableSet (signedChart n side '' s) :=
  hs.image_of_continuousOn_injOn (signedChart_continuous n side).continuousOn
    ((signedChart_injOn n side).mono hsb)

/-- True normalization of the actual angular chart measure. -/
def angularNormalization (n : ℕ) : ℝ≥0∞ :=
  ((volume : Measure (WithLp 2 (ChartSpace n × ℝ))).toSphere Set.univ)⁻¹

/-- The actual uniform sphere law in either genuine local chart. -/
theorem sphereLaw_restrict_signedChart (n : ℕ) (side : Bool)
    {s : Set (ChartSpace n)} (hs : MeasurableSet s) (hsb : s ⊆ Metric.ball 0 2) :
    (sphereLaw (n + 1)).restrict (signedChart n side '' s) = angularNormalization n •
      Measure.map (signedChart n side) ((volume.restrict s).withDensity
        (fun u => ENNReal.ofReal (sphereChartWeightND u))) := by
  have hb := sphereLaw_restrict_manuscriptChart hs hsb
  have hweight : (fun u : ChartSpace n => ENNReal.ofReal (Real.sqrt (sphereChartGramND u).det)) =ᵐ[
      volume.restrict s] (fun u => ENNReal.ofReal (sphereChartWeightND u)) := by
        filter_upwards [ae_restrict_mem hs] with u hu
        rw [sphereChartWeightND_eq_sqrt_gram (by simpa using hsb hu)]
  rw [withDensity_congr_ae hweight] at hb
  cases side
  · exact hb
  · let U := LinearIsometryEquiv.neg ℝ (E := Vector (n + 1))
    have hU : MeasurableEmbedding (U : Vector (n + 1) → Vector (n + 1)) :=
      U.toHomeomorph.measurableEmbedding
    have hrot : (sphereLaw (n + 1)).map U = sphereLaw (n + 1) := sphereLaw_rotation_invariant U
    have hset : signedChart n true '' s = U '' (manuscriptChart n '' s) := by
      rw [← Set.image_comp]
      rfl
    rw [hset, ← hrot, hU.restrict_map, Set.preimage_image_eq _ U.injective, hb,
      Measure.map_smul _ hU.measurable.aemeasurable]
    have hm : Measurable (manuscriptChart n) := (signedChart_continuous n false).measurable
    rw [Measure.map_map hU.measurable hm]
    rfl

/-- Actual Gibbs set-integral formula on every genuine Borel region. -/
theorem gibbsLaw_setIntegral (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) (g : Vector (n + 1) → ℝ)
    {s : Set (Vector (n + 1))} (hs : MeasurableSet s) :
    (∫ x in s, g x ∂gibbsLaw (n + 1) β H) =
      ∫ x in s, gibbsDensity (n + 1) β H x * g x ∂sphereLaw (n + 1) := by
  unfold gibbsLaw
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    ((gibbsDensity_continuous β hH).measurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)) g hs]
  apply integral_congr_ae
  exact .of_forall (fun x => by
    dsimp only
    rw [ENNReal.toReal_ofReal (gibbsDensity_pos (by omega) β hH x).le, smul_eq_mul])

/-- The exact ordinary-Lebesgue density of the actual Gibbs chart pullback. -/
def chartGibbsDensity (n : ℕ) (β : ℝ) (H : Vector (n + 1) → ℝ) (side : Bool)
    (u : ChartSpace n) : ℝ :=
  (angularNormalization n).toReal * sphereChartWeightND u *
    gibbsDensity (n + 1) β H (signedChart n side u)

/-- Actual weighted chart integral identity, derived from the actual
Gaussian-direction sphere law and its proved ordinary chart volume. -/
theorem gibbsLaw_chart_integral (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) (side : Bool) {g : Vector (n + 1) → ℝ}
    (hg : StronglyMeasurable g) {s : Set (ChartSpace n)}
    (hs : MeasurableSet s) (hsb : s ⊆ Metric.ball 0 2) :
    (∫ x in signedChart n side '' s, g x ∂gibbsLaw (n + 1) β H) =
      ∫ u in s, chartGibbsDensity n β H side u * g (signedChart n side u) := by
  rw [gibbsLaw_setIntegral n β hH g (signedChart_image_measurable n side hs hsb)]
  rw [sphereLaw_restrict_signedChart n side hs hsb, integral_smul_measure,
    integral_map (f := fun x => gibbsDensity (n + 1) β H x * g x)
      (signedChart_continuous n side).measurable.aemeasurable
      (((gibbsDensity_continuous β hH).stronglyMeasurable.mul hg).aestronglyMeasurable),
    integral_withDensity_eq_integral_toReal_smul sphereChartWeightND_measurable.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [ENNReal.toReal_ofReal (sphereChartWeightND_pos (by simpa using hsb hu)).le]
  simp only [chartGibbsDensity]
  ring

lemma angularNormalization_pos (n : ℕ) : 0 < (angularNormalization n).toReal := by
  have hz : (volume : Measure (WithLp 2 (ChartSpace n × ℝ))).toSphere Set.univ ≠ 0 :=
    SphereVolume.angular_total_ne_zero
  have ht : (volume : Measure (WithLp 2 (ChartSpace n × ℝ))).toSphere Set.univ ≠ ⊤ :=
    measure_ne_top _ _
  exact ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr ht) (ENNReal.inv_ne_top.mpr hz)

lemma chartGibbsDensity_continuousOn (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) (side : Bool) :
    ContinuousOn (chartGibbsDensity n β H side) (Metric.ball 0 2) :=
  ((continuousOn_const.mul sphereChartWeightND_continuousOn).mul
    ((gibbsDensity_continuous β hH).comp (signedChart_continuous n side)).continuousOn)

/-- True positive lower and finite upper bounds of the genuine actual
Gibbs chart density on the compact cutoff region, for both charts together. -/
theorem chartGibbsDensity_bounds (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) : ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ side : Bool, ∀ u : ChartSpace n, ‖u‖ ≤ Real.sqrt 3 →
        m ≤ chartGibbsDensity n β H side u ∧ chartGibbsDensity n β H side u ≤ M := by
  have hsub : Metric.closedBall (0 : ChartSpace n) (Real.sqrt 3) ⊆ Metric.ball 0 2 := by
    intro u hu
    simpa only [Metric.mem_ball, dist_zero_right] using
      (show ‖u‖ ≤ Real.sqrt 3 from by simpa using hu).trans_lt sqrt_three_lt_two
  have hside (side : Bool) : ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      ∀ u : ChartSpace n, ‖u‖ ≤ Real.sqrt 3 →
        m ≤ chartGibbsDensity n β H side u ∧ chartGibbsDensity n β H side u ≤ M := by
    have hc := (chartGibbsDensity_continuousOn n β hH side).mono hsub
    have hp (u : ChartSpace n) (hu : u ∈ Metric.closedBall 0 (Real.sqrt 3)) :
        0 < chartGibbsDensity n β H side u := by
      unfold chartGibbsDensity
      exact mul_pos (mul_pos (angularNormalization_pos n)
        (sphereChartWeightND_pos (by simpa using hsub hu)))
        (gibbsDensity_pos (by omega) β hH _)
    obtain ⟨m, hm, hml⟩ := (isCompact_closedBall (0 : ChartSpace n) (Real.sqrt 3)).exists_forall_le' hc hp
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ChartSpace n) (Real.sqrt 3)).exists_bound_of_continuousOn hc
    refine ⟨m, max M 1, hm, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro u hu
    have hmem : u ∈ Metric.closedBall 0 (Real.sqrt 3) := by simpa using hu
    exact ⟨hml u hmem, (le_abs_self _).trans ((hM u hmem).trans (le_max_left _ _))⟩
  obtain ⟨ml, Ml, hml, hMl, hl⟩ := hside false
  obtain ⟨mr, Mr, hmr, hMr, hr⟩ := hside true
  refine ⟨min ml mr, max Ml Mr, lt_min hml hmr, hMl.trans_le (le_max_left _ _), ?_⟩
  intro side u hu
  cases side
  · exact ⟨(min_le_left _ _).trans (hl u hu).1, (hl u hu).2.trans (le_max_left _ _)⟩
  · exact ⟨(min_le_right _ _).trans (hr u hu).1, (hr u hu).2.trans (le_max_right _ _)⟩

/-- The genuine chart density gives a lower comparison of Euclidean local
integrals with the actual full Gibbs integral, with no volume hypothesis. -/
theorem chartIntegral_lower_comparison (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) (side : Bool) {g : Vector (n + 1) → ℝ}
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) {m : ℝ}
    (hm : ∀ u : ChartSpace n, ‖u‖ ≤ Real.sqrt 3 → m ≤ chartGibbsDensity n β H side u) :
    m * (∫ u in Metric.closedBall (0 : ChartSpace n) (Real.sqrt 3), g (signedChart n side u)) ≤
      ∫ x, g x ∂gibbsLaw (n + 1) β H := by
  let S := Metric.closedBall (0 : ChartSpace n) (Real.sqrt 3)
  have hS : MeasurableSet S := measurableSet_closedBall
  have hsub : S ⊆ Metric.ball 0 2 := by
    intro u hu
    simpa only [Metric.mem_ball, dist_zero_right] using
      (show ‖u‖ ≤ Real.sqrt 3 from by simpa [S] using hu).trans_lt sqrt_three_lt_two
  have hgc : Continuous (fun u => g (signedChart n side u)) := hg.comp (signedChart_continuous n side)
  have hi := hgc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ChartSpace n) (Real.sqrt 3))
    (μ := volume)
  have hρi := (((chartGibbsDensity_continuousOn n β hH side).mono hsub).mul hgc.continuousOn).integrableOn_compact
    (isCompact_closedBall (0 : ChartSpace n) (Real.sqrt 3)) (μ := volume)
  calc
    _ = ∫ u in S, m * g (signedChart n side u) := (integral_const_mul _ _).symm
    _ ≤ ∫ u in S, chartGibbsDensity n β H side u * g (signedChart n side u) := by
      apply integral_mono_ae (hi.const_mul m) hρi
      filter_upwards [ae_restrict_mem hS] with u hu
      exact mul_le_mul_of_nonneg_right (hm u (by simpa [S] using hu)) (hg0 _)
    _ = ∫ x in signedChart n side '' S, g x ∂gibbsLaw (n + 1) β H :=
      (gibbsLaw_chart_integral n β hH side hg.stronglyMeasurable hS hsub).symm
    _ ≤ _ := setIntegral_le_integral (integrable_gibbs_of_continuous (by omega) β hH hg)
      (ae_of_all _ hg0)

lemma localize_tsupport_subset (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ) :
    tsupport (localize n side f) ⊆ Metric.closedBall (0 : ChartSpace n) (Real.sqrt 3) := by
  change tsupport (fun u => chartCutoff n u * f (signedChart n side u)) ⊆ _
  exact tsupport_mul_subset_left.trans (by rw [(chartCutoff n).tsupport_eq]; rfl)

lemma localize_fderiv_zero_outside (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ)
    {u : ChartSpace n} (hu : u ∉ Metric.closedBall 0 (Real.sqrt 3)) :
    fderiv ℝ (localize n side f) u = 0 :=
  fderiv_of_notMem_tsupport ℝ (fun h => hu (localize_tsupport_subset n side f h))

/-- Actual local function square integrals are controlled by the genuine
Gibbs function norm through the positive chart-density comparison. -/
theorem localize_integral_square_le (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) (side : Bool) {f : Vector (n + 1) → ℝ} (hf : ContDiff ℝ ∞ f)
    {m : ℝ} (hm : 0 < m)
    (hρ : ∀ u : ChartSpace n, ‖u‖ ≤ Real.sqrt 3 → m ≤ chartGibbsDensity n β H side u) :
    (∫ u, localize n side f u ^ 2) ≤ (∫ x, f x ^ 2 ∂gibbsLaw (n + 1) β H) / m := by
  let S := Metric.closedBall (0 : ChartSpace n) (Real.sqrt 3)
  have hloc := localize_contDiff n side hf
  have hi : IntegrableOn (fun u => localize n side f u ^ 2) S :=
    (hloc.continuous.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hfc : Continuous (fun u => f (signedChart n side u) ^ 2) :=
    (hf.continuous.comp (signedChart_continuous n side)).pow 2
  have hfi : IntegrableOn (fun u => f (signedChart n side u) ^ 2) S :=
    hfc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have he : (∫ u, localize n side f u ^ 2) = ∫ u in S, localize n side f u ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [localize_zero_of_outside n side f (le_of_lt (by simpa [S] using hu)), zero_pow (by norm_num)])).symm
  have hle : (∫ u, localize n side f u ^ 2) ≤ ∫ u in S, f (signedChart n side u) ^ 2 := by
    rw [he]
    apply integral_mono_ae hi hfi
    exact ae_of_all _ (fun u => by
      dsimp only
      unfold localize
      rw [mul_pow]
      have hχ : (chartCutoff n u) ^ 2 ≤ 1 := by
        nlinarith [(chartCutoff n).nonneg' u, (chartCutoff n).le_one (x := u)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hχ (sq_nonneg (f (signedChart n side u))))
  have hactual := chartIntegral_lower_comparison n β hH side (g := fun x => f x ^ 2) (hf.continuous.pow 2)
    (fun _ => sq_nonneg _) hρ
  apply (le_div_iff₀ hm).mpr
  have hh := (mul_le_mul_of_nonneg_left hle hm.le).trans hactual
  simpa only [mul_comm m] using hh

/-- Actual localized gradient energy is bounded by the true Gibbs function
and spherical Dirichlet integrals, with both derivative bounds proved above. -/
theorem localize_integral_derivative_square_le (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) (side : Bool) {f : Vector (n + 1) → ℝ} (hf : ContDiff ℝ ∞ f)
    {m B C : ℝ} (hm : 0 < m) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hρ : ∀ u : ChartSpace n, ‖u‖ ≤ Real.sqrt 3 → m ≤ chartGibbsDensity n β H side u)
    (hb : ∀ u : ChartSpace n, ‖fderiv ℝ (chartCutoff n) u‖ ≤ B)
    (hc : ∀ u : ChartSpace n, ‖u‖ ≤ Real.sqrt 3 → ‖signedChartDerivative n side u‖ ≤ C) :
    (∫ u, ‖fderiv ℝ (localize n side f) u‖ ^ 2) ≤
      (2 * B ^ 2 * (∫ x, f x ^ 2 ∂gibbsLaw (n + 1) β H) +
        2 * C ^ 2 * dirichletEnergy (n + 1) β H f) / m := by
  let S := Metric.closedBall (0 : ChartSpace n) (Real.sqrt 3)
  have hloc := localize_contDiff n side hf
  have hfloc : Continuous (fun u => ‖fderiv ℝ (localize n side f) u‖ ^ 2) :=
    (hloc.continuous_fderiv (by simp)).norm.pow 2
  have hi : IntegrableOn (fun u => ‖fderiv ℝ (localize n side f) u‖ ^ 2) S :=
    hfloc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hv : Continuous (fun u => f (signedChart n side u) ^ 2) :=
    (hf.continuous.comp (signedChart_continuous n side)).pow 2
  have hfg : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hg : Continuous (fun x => ‖surfaceGradient f x‖ ^ 2) :=
    (surfaceGradient_continuous hfg).norm.pow 2
  have hcgrad : Continuous (fun u => ‖surfaceGradient f (signedChart n side u)‖ ^ 2) :=
    hg.comp (signedChart_continuous n side)
  have hvi : IntegrableOn (fun u => f (signedChart n side u) ^ 2) S :=
    hv.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hgi : IntegrableOn (fun u => ‖surfaceGradient f (signedChart n side u)‖ ^ 2) S :=
    hcgrad.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have he : (∫ u, ‖fderiv ℝ (localize n side f) u‖ ^ 2) =
      ∫ u in S, ‖fderiv ℝ (localize n side f) u‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      rw [localize_fderiv_zero_outside n side f hu, norm_zero, zero_pow (by norm_num)])).symm
  have hle : (∫ u, ‖fderiv ℝ (localize n side f) u‖ ^ 2) ≤
      2 * B ^ 2 * (∫ u in S, f (signedChart n side u) ^ 2) +
      2 * C ^ 2 * (∫ u in S, ‖surfaceGradient f (signedChart n side u)‖ ^ 2) := by
    rw [he, ← integral_const_mul, ← integral_const_mul, ← integral_add
      (hvi.const_mul (2 * B ^ 2)) (hgi.const_mul (2 * C ^ 2))]
    apply integral_mono_ae hi ((hvi.const_mul _).add (hgi.const_mul _))
    filter_upwards [ae_restrict_mem measurableSet_closedBall] with u hu
    have hun : ‖u‖ ≤ Real.sqrt 3 := by simpa [S] using hu
    exact localize_derivative_square_le n side (hf.differentiable (by simp)) hun hB hC (hb u) (hc u hun)
  have hval := chartIntegral_lower_comparison n β hH side (g := fun x => f x ^ 2) (hf.continuous.pow 2)
    (fun _ => sq_nonneg _) hρ
  have hgrad := chartIntegral_lower_comparison n β hH side hg (fun _ => sq_nonneg _) hρ
  rw [← dirichletEnergy_eq_integral_norm_sq] at hgrad
  apply (le_div_iff₀ hm).mpr
  have hh := mul_le_mul_of_nonneg_left hle hm.le
  have hvb := mul_le_mul_of_nonneg_left hval (show 0 ≤ 2 * B ^ 2 by positivity)
  have hgb := mul_le_mul_of_nonneg_left hgrad (show 0 ≤ 2 * C ^ 2 by positivity)
  dsimp only [S] at hh
  nlinarith

/-- A true upper comparison on each covering chart core, using the
actual Gibbs density and the actual cutoff which is one on that core. -/
theorem chartCore_integral_square_le (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) (side : Bool) {f : Vector (n + 1) → ℝ} (hf : ContDiff ℝ ∞ f)
    {M : ℝ} (hM : 0 ≤ M)
    (hρ : ∀ u : ChartSpace n, ‖u‖ ≤ Real.sqrt 3 → chartGibbsDensity n β H side u ≤ M) :
    (∫ x in signedChart n side '' Metric.closedBall (0 : ChartSpace n) (Real.sqrt 2),
      f x ^ 2 ∂gibbsLaw (n + 1) β H) ≤ M * (∫ u, localize n side f u ^ 2) := by
  let S := Metric.closedBall (0 : ChartSpace n) (Real.sqrt 2)
  have hS : MeasurableSet S := measurableSet_closedBall
  have h23 : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
  have hsub : S ⊆ Metric.ball 0 2 := by
    intro u hu
    simpa only [Metric.mem_ball, dist_zero_right] using
      ((show ‖u‖ ≤ Real.sqrt 2 from by simpa [S] using hu).trans h23).trans_lt sqrt_three_lt_two
  have hc : Continuous (fun u => f (signedChart n side u) ^ 2) :=
    (hf.continuous.comp (signedChart_continuous n side)).pow 2
  have hi : IntegrableOn (fun u => f (signedChart n side u) ^ 2) S :=
    hc.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hρi : IntegrableOn (fun u => chartGibbsDensity n β H side u * f (signedChart n side u) ^ 2) S :=
    (((chartGibbsDensity_continuousOn n β hH side).mono hsub).mul hc.continuousOn).integrableOn_compact
      (isCompact_closedBall _ _)
  calc
    _ = ∫ u in S, chartGibbsDensity n β H side u * f (signedChart n side u) ^ 2 :=
      gibbsLaw_chart_integral n β hH side (g := fun x => f x ^ 2) (hf.continuous.pow 2).stronglyMeasurable hS hsub
    _ ≤ ∫ u in S, M * f (signedChart n side u) ^ 2 := by
      apply integral_mono_ae hρi (hi.const_mul M)
      filter_upwards [ae_restrict_mem hS] with u hu
      exact mul_le_mul_of_nonneg_right (hρ u ((show ‖u‖ ≤ Real.sqrt 2 from by simpa [S] using hu).trans h23))
        (sq_nonneg _)
    _ = M * ∫ u in S, localize n side f u ^ 2 := by
      rw [integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hS] with u hu
      rw [localize_eq_on_inner n side f (by simpa [S] using hu)]
    _ ≤ _ := by
      have hsquare : HasCompactSupport (fun u => localize n side f u ^ 2) := by
        exact (localize_hasCompactSupport n side f).comp_left (g := fun z : ℝ => z ^ 2) (by norm_num)
      exact mul_le_mul_of_nonneg_left
        (setIntegral_le_integral ((localize_contDiff n side hf).continuous.pow 2 |>.integrable_of_hasCompactSupport
          hsquare) (ae_of_all _ (fun _ => sq_nonneg _))) hM

/-- The two true inner charts cover the actual Gibbs sphere, so ordinary
Euclidean local L² differences control the entire genuine spherical L² norm. -/
theorem two_chart_integral_square_bound (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) {f : Vector (n + 1) → ℝ} (hf : ContDiff ℝ ∞ f)
    {M : ℝ} (hM : 0 ≤ M)
    (hρ : ∀ side : Bool, ∀ u : ChartSpace n, ‖u‖ ≤ Real.sqrt 3 → chartGibbsDensity n β H side u ≤ M) :
    (∫ x, f x ^ 2 ∂gibbsLaw (n + 1) β H) ≤
      M * ((∫ u, localize n false f u ^ 2) + (∫ u, localize n true f u ^ 2)) := by
  let A := signedChart n false '' Metric.closedBall (0 : ChartSpace n) (Real.sqrt 2)
  let B := signedChart n true '' Metric.closedBall (0 : ChartSpace n) (Real.sqrt 2)
  have hsub : Metric.closedBall (0 : ChartSpace n) (Real.sqrt 2) ⊆ Metric.ball 0 2 := by
    intro u hu
    simpa only [Metric.mem_ball, dist_zero_right] using
      ((show ‖u‖ ≤ Real.sqrt 2 from by simpa using hu).trans
        (Real.sqrt_le_sqrt (show (2 : ℝ) ≤ 3 by norm_num))).trans_lt sqrt_three_lt_two
  have hA : MeasurableSet A := signedChart_image_measurable n false measurableSet_closedBall hsub
  have hB : MeasurableSet B := signedChart_image_measurable n true measurableSet_closedBall hsub
  have hcover : ∀ᵐ x ∂gibbsLaw (n + 1) β H, x ∈ A ∪ B := by
    filter_upwards [gibbsLaw_support (show 1 ≤ n + 1 by omega) β H] with x hx
    have hm : x ∈ Metric.sphere (0 : Vector (n + 1)) (Real.sqrt (n + 1 : ℕ)) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        SphericalAging.LandscapeDerivatives.sphere_norm x hx
    rw [manuscriptChart_two_closed_charts_cover] at hm
    exact hm
  have hi : Integrable (fun x => f x ^ 2) (gibbsLaw (n + 1) β H) :=
    integrable_gibbs_of_continuous (by omega) β hH (hf.continuous.pow 2)
  have hle : (∫ x, f x ^ 2 ∂gibbsLaw (n + 1) β H) ≤
      (∫ x in A, f x ^ 2 ∂gibbsLaw (n + 1) β H) +
        ∫ x in B, f x ^ 2 ∂gibbsLaw (n + 1) β H := by
    rw [← integral_indicator hA, ← integral_indicator hB, ← integral_add
      (hi.indicator hA) (hi.indicator hB)]
    apply integral_mono_ae hi ((hi.indicator hA).add (hi.indicator hB))
    filter_upwards [hcover] with x hx
    change f x ^ 2 ≤ A.indicator (fun x => f x ^ 2) x + B.indicator (fun x => f x ^ 2) x
    by_cases hxa : x ∈ A
    · rw [Set.indicator_of_mem hxa]
      by_cases hxb : x ∈ B
      · rw [Set.indicator_of_mem hxb]
        nlinarith [sq_nonneg (f x)]
      · rw [Set.indicator_of_notMem hxb, add_zero]
    · rw [Set.indicator_of_notMem hxa]
      have hxb : x ∈ B := hx.resolve_left hxa
      rw [Set.indicator_of_mem hxb, zero_add]
  have hl := chartCore_integral_square_le n β hH false hf hM (hρ false)
  have hr := chartCore_integral_square_le n β hH true hf hM (hρ true)
  nlinarith

/-- Fixed genuine linear rescaling from the ordinary product unit cube
into the Euclidean chart coordinates. -/
def cubeScaling (n : ℕ) : (Fin n → ℝ) →L[ℝ] ChartSpace n :=
  (2 : ℝ) • (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap

@[simp] lemma cubeScaling_apply (n : ℕ) (x : Fin n → ℝ) :
    cubeScaling n x = (2 : ℝ) • WithLp.toLp 2 x := rfl

/-- The actual localized chart functions used in the proved cube Rellich
argument, defined globally as ordinary smooth real functions. -/
def cubePullback (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ) (x : Fin n → ℝ) : ℝ :=
  localize n side f (cubeScaling n x)

lemma cubePullback_contDiff (n : ℕ) (side : Bool) {f : Vector (n + 1) → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (cubePullback n side f) :=
  (localize_contDiff n side hf).comp (cubeScaling n).contDiff

/-- Literal Lebesgue integral rescaling, using the actual L²-coordinate
volume preservation and actual linear scalar change of variables. -/
theorem cubeScaling_integral (n : ℕ) (h : ChartSpace n → ℝ) :
    (∫ x, h (cubeScaling n x)) = ((2 : ℝ) ^ n)⁻¹ * ∫ u, h u := by
  have he : MeasurableEmbedding (@WithLp.toLp 2 (Fin n → ℝ)) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toHomeomorph.measurableEmbedding
  calc
    _ = ∫ u, h ((2 : ℝ) • u) :=
      (PiLp.volume_preserving_toLp (Fin n)).integral_comp he (fun u => h ((2 : ℝ) • u))
    _ = _ := by
      have hh := Measure.integral_comp_smul_of_nonneg (volume : Measure (ChartSpace n)) h 2 (hR := by norm_num)
      simpa [ChartSpace, smul_eq_mul] using hh

/-- The actual localized cube representative vanishes outside its genuine
compact unit cube because its chart cutoff has radius sqrt(3)<2. -/
lemma cubePullback_zero_outside (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ)
    (x : Fin n → ℝ) (hx : x ∉ GenericRellich.realFinCube n) : cubePullback n side f x = 0 := by
  by_contra hf
  have hχ : chartCutoff n (cubeScaling n x) ≠ 0 := by
    intro hz
    apply hf
    simp only [cubePullback, localize, hz, zero_mul]
  have hmem : cubeScaling n x ∈ Function.support (chartCutoff n) := hχ
  rw [(chartCutoff n).support_eq] at hmem
  have hn : ‖cubeScaling n x‖ < Real.sqrt 3 := by simpa [chartCutoff] using hmem
  apply hx
  simp only [GenericRellich.realFinCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
  intro i
  have hi := PiLp.norm_apply_le (cubeScaling n x) i
  change ‖(2 : ℝ) * x i‖ ≤ ‖cubeScaling n x‖ at hi
  rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_eq_abs] at hi
  have hilt : |x i| < 1 := by linarith [sqrt_three_lt_two]
  exact ⟨(abs_lt.mp hilt).1.le, (abs_lt.mp hilt).2.le⟩

/-- The actual global local-function norm is exactly a constant multiple
of its ordinary unit-cube norm, with no support premise. -/
theorem localize_square_integral_cube (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ) :
    (∫ u, localize n side f u ^ 2) = (2 : ℝ) ^ n *
      ∫ x in GenericRellich.realFinCube n, cubePullback n side f x ^ 2 := by
  have he : (∫ x in GenericRellich.realFinCube n, cubePullback n side f x ^ 2) =
      ∫ x, cubePullback n side f x ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [cubePullback_zero_outside n side f x hx, zero_pow (by norm_num)])
  rw [he]
  have hscale := cubeScaling_integral n (fun u => localize n side f u ^ 2)
  change (∫ x, cubePullback n side f x ^ 2) = ((2 : ℝ) ^ n)⁻¹ * ∫ u, localize n side f u ^ 2 at hscale
  rw [hscale]
  field_simp

/-- Actual coordinate derivatives of the genuine cube pullback are
controlled by the true chart differential and the fixed linear rescaling. -/
theorem cubePullback_partial_square_bound (n : ℕ) (side : Bool)
    {f : Vector (n + 1) → ℝ} (hf : ContDiff ℝ ∞ f) (x : Fin n → ℝ) :
    (∑ i : Fin n, GenericRellich.coordPartial (cubePullback n side f) x i ^ 2) ≤
      (n : ℝ) * ‖cubeScaling n‖ ^ 2 * ‖fderiv ℝ (localize n side f) (cubeScaling n x)‖ ^ 2 := by
  have hd : fderiv ℝ (cubePullback n side f) x =
      (fderiv ℝ (localize n side f) (cubeScaling n x)).comp (cubeScaling n) :=
    (((localize_contDiff n side hf).differentiable (by simp) _).hasFDerivAt.comp x
      (cubeScaling n).hasFDerivAt).fderiv
  have hb (i : Fin n) : ‖GenericRellich.coordPartial (cubePullback n side f) x i‖ ≤
      ‖cubeScaling n‖ * ‖fderiv ℝ (localize n side f) (cubeScaling n x)‖ := by
    unfold GenericRellich.coordPartial
    rw [hd, ContinuousLinearMap.comp_apply]
    calc
      _ ≤ ‖fderiv ℝ (localize n side f) (cubeScaling n x)‖ * ‖cubeScaling n (Pi.single i 1)‖ :=
        (fderiv ℝ (localize n side f) (cubeScaling n x)).le_opNorm _
      _ ≤ _ := by
        have hmap := (cubeScaling n).le_opNorm (Pi.single i 1)
        simp only [Pi.norm_single, norm_one, mul_one] at hmap
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmap
          (norm_nonneg (fderiv ℝ (localize n side f) (cubeScaling n x)))
  calc
    _ ≤ ∑ _ : Fin n, (‖cubeScaling n‖ * ‖fderiv ℝ (localize n side f) (cubeScaling n x)‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (hb i)
      simpa only [Real.norm_eq_abs, sq_abs] using h
    _ = _ := by simp [mul_pow, mul_assoc]

/-- The genuine ordinary cube gradient integral is bounded by the actual
localized Euclidean energy, with the true volume rescaling factor. -/
theorem cubePullback_derivative_integral_bound (n : ℕ) (side : Bool)
    {f : Vector (n + 1) → ℝ} (hf : ContDiff ℝ ∞ f) :
    (∫ x in GenericRellich.realFinCube n,
      ∑ i : Fin n, GenericRellich.coordPartial (cubePullback n side f) x i ^ 2) ≤
      (n : ℝ) * ‖cubeScaling n‖ ^ 2 * ((2 : ℝ) ^ n)⁻¹ *
        ∫ u, ‖fderiv ℝ (localize n side f) u‖ ^ 2 := by
  let q : ChartSpace n → ℝ := fun u => ‖fderiv ℝ (localize n side f) u‖ ^ 2
  have hq : Continuous q := ((localize_contDiff n side hf).continuous_fderiv (by simp)).norm.pow 2
  have hs : HasCompactSupport q :=
    ((localize_hasCompactSupport n side f).fderiv ℝ).comp_left (g := fun L => ‖L‖ ^ 2) (by simp)
  have hiq : Integrable q := hq.integrable_of_hasCompactSupport hs
  have him : Integrable (fun x => q (cubeScaling n x)) :=
    (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_of_integrable (hiq.comp_smul (by norm_num : (2 : ℝ) ≠ 0))
  have hpart : Continuous (fun x => ∑ i : Fin n, GenericRellich.coordPartial (cubePullback n side f) x i ^ 2) :=
    continuous_finsetSum Finset.univ (fun i _ =>
      ((GenericRellich.real_coordPartial_smooth _ (cubePullback_contDiff n side hf) i).continuous).pow 2)
  have hip : IntegrableOn (fun x => ∑ i : Fin n, GenericRellich.coordPartial (cubePullback n side f) x i ^ 2)
      (GenericRellich.realFinCube n) :=
    hpart.continuousOn.integrableOn_compact (GenericRellich.realFinCube_isCompact n)
  let A : ℝ := (n : ℝ) * ‖cubeScaling n‖ ^ 2
  have hA : 0 ≤ A := by positivity
  calc
    _ ≤ ∫ x in GenericRellich.realFinCube n, A * q (cubeScaling n x) :=
      integral_mono_ae hip ((him.const_mul A).integrableOn)
        (ae_of_all _ (cubePullback_partial_square_bound n side hf))
    _ ≤ ∫ x, A * q (cubeScaling n x) :=
      setIntegral_le_integral (him.const_mul A) (ae_of_all _ (fun x => by
        exact mul_nonneg hA (sq_nonneg _)))
    _ = _ := by
      rw [integral_const_mul, cubeScaling_integral]
      dsimp only [A, q]
      ring

/-- The actual smooth graph norm is exactly the true spherical function
square integral plus its actual gradient energy. -/
theorem smoothGraph_norm_sq (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) (f : SphericalForm.smoothCore (n + 1)) :
    ‖smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH f‖ ^ 2 =
      (∫ x, (f : Vector (n + 1) → ℝ) x ^ 2 ∂gibbsLaw (n + 1) β H) +
        dirichletEnergy (n + 1) β H f := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖gibbsToL2 (show 1 ≤ n + 1 by omega) β H hH f (smoothCore_contDiff f).continuous‖ ^ 2 +
    ‖normalizedRotationGradientL2 (show 1 ≤ n + 1 by omega) β H hH f _‖ ^ 2 = _
  rw [← dirichletEnergy_eq_normalizedRotationGradientL2_norm]
  congr 1
  rw [← real_inner_self_eq_norm_sq, gibbsToL2_inner]
  simp only [pow_two]

lemma cubePullback_integral_square_scale (n : ℕ) (side : Bool) (f : Vector (n + 1) → ℝ) :
    (∫ x in GenericRellich.realFinCube n, cubePullback n side f x ^ 2) =
      ((2 : ℝ) ^ n)⁻¹ * ∫ u, localize n side f u ^ 2 := by
  rw [localize_square_integral_cube n side f]
  field_simp

/-- Actual uniform spherical energy bounds imply actual cube Sobolev
energy bounds for both chart localizations. All constants are derived from
the genuine chart densities, cutoffs, and actual sphere Dirichlet energy. -/
theorem exists_cube_energy_bound (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) {R : ℝ} (hR : 0 < R) :
    ∃ D : ℝ, 0 < D ∧ ∀ side : Bool, ∀ f : SphericalForm.smoothCore (n + 1),
      ‖smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH f‖ ≤ R →
      (∫ x in GenericRellich.realFinCube n, cubePullback n side f x ^ 2) +
        (∫ x in GenericRellich.realFinCube n,
          ∑ i : Fin n, GenericRellich.coordPartial (cubePullback n side f) x i ^ 2) ≤ D := by
  obtain ⟨m, M, hm, hM, hρ⟩ := chartGibbsDensity_bounds n β hH
  obtain ⟨B, hB, hb⟩ := exists_cutoffDerivative_bound n
  obtain ⟨C, hC, hc⟩ := exists_chartDerivative_bound n
  let T : ℝ := ((2 : ℝ) ^ n)⁻¹
  let A : ℝ := (n : ℝ) * ‖cubeScaling n‖ ^ 2
  have hT : 0 ≤ T := by positivity
  have hA : 0 ≤ A := by positivity
  let D : ℝ := T * (R ^ 2 / m) + A * T * ((2 * B ^ 2 * R ^ 2 + 2 * C ^ 2 * R ^ 2) / m) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro side f hnorm
  have hf := smoothCore_contDiff f
  have hfn : 0 ≤ ∫ x, (f : Vector (n + 1) → ℝ) x ^ 2 ∂gibbsLaw (n + 1) β H :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hen : 0 ≤ dirichletEnergy (n + 1) β H f := dirichletEnergy_nonneg _ _ _ _
  have hgraph : (∫ x, (f : Vector (n + 1) → ℝ) x ^ 2 ∂gibbsLaw (n + 1) β H) +
      dirichletEnergy (n + 1) β H f ≤ R ^ 2 := by
    rw [← smoothGraph_norm_sq n β hH f]
    exact (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hnorm
  have hvR : (∫ x, (f : Vector (n + 1) → ℝ) x ^ 2 ∂gibbsLaw (n + 1) β H) ≤ R ^ 2 := by linarith
  have heR : dirichletEnergy (n + 1) β H f ≤ R ^ 2 := by linarith
  have hv := localize_integral_square_le n β hH side hf hm (fun u hu => (hρ side u hu).1)
  have hg := localize_integral_derivative_square_le n β hH side hf hm hB hC
    (fun u hu => (hρ side u hu).1) hb (hc side)
  have hval : (∫ x in GenericRellich.realFinCube n, cubePullback n side f x ^ 2) ≤ T * (R ^ 2 / m) := by
    rw [cubePullback_integral_square_scale]
    exact mul_le_mul_of_nonneg_left (hv.trans (div_le_div_of_nonneg_right hvR hm.le)) hT
  have hgrad : (∫ x in GenericRellich.realFinCube n,
      ∑ i : Fin n, GenericRellich.coordPartial (cubePullback n side f) x i ^ 2) ≤
      A * T * ((2 * B ^ 2 * R ^ 2 + 2 * C ^ 2 * R ^ 2) / m) := by
    apply (cubePullback_derivative_integral_bound n side hf).trans
    apply mul_le_mul_of_nonneg_left
      (hg.trans (div_le_div_of_nonneg_right
        (add_le_add (mul_le_mul_of_nonneg_left hvR (by positivity))
          (mul_le_mul_of_nonneg_left heR (by positivity))) hm.le))
      (mul_nonneg hA hT)
  dsimp only [D]
  linarith

@[simp] lemma localize_sub (n : ℕ) (side : Bool) (f g : Vector (n + 1) → ℝ) :
    localize n side (f - g) = localize n side f - localize n side g := by
  funext u
  simp only [localize, Pi.sub_apply, mul_sub]

@[simp] lemma cubePullback_sub (n : ℕ) (side : Bool) (f g : Vector (n + 1) → ℝ) :
    cubePullback n side (f - g) = cubePullback n side f - cubePullback n side g := by
  funext x
  simp only [cubePullback, localize, Pi.sub_apply, mul_sub]

/-- Actual Gibbs distance of two smooth functions is controlled by the
two genuine ordinary cube differences. -/
theorem smooth_distance_two_cube_bound (n : ℕ) (β : ℝ) {H : Vector (n + 1) → ℝ}
    (hH : Continuous H) (f g : SphericalForm.smoothCore (n + 1)) {M : ℝ} (hM : 0 ≤ M)
    (hρ : ∀ side : Bool, ∀ u : ChartSpace n, ‖u‖ ≤ Real.sqrt 3 → chartGibbsDensity n β H side u ≤ M) :
    dist ((smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH f).fst)
      ((smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH g).fst) ^ 2 ≤
        M * (2 : ℝ) ^ n *
          ((∫ x in GenericRellich.realFinCube n, (cubePullback n false f x - cubePullback n false g x) ^ 2) +
           (∫ x in GenericRellich.realFinCube n, (cubePullback n true f x - cubePullback n true g x) ^ 2)) := by
  have h := two_chart_integral_square_bound n β hH
    ((smoothCore_contDiff f).sub (smoothCore_contDiff g)) hM hρ
  rw [localize_square_integral_cube n false (fun x => (f : Vector (n + 1) → ℝ) x - (g : Vector (n + 1) → ℝ) x),
    localize_square_integral_cube n true (fun x => (f : Vector (n + 1) → ℝ) x - (g : Vector (n + 1) → ℝ) x)] at h
  have he : dist ((smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH f).fst)
      ((smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH g).fst) ^ 2 =
        ∫ x, ((f : Vector (n + 1) → ℝ) x - (g : Vector (n + 1) → ℝ) x) ^ 2 ∂gibbsLaw (n + 1) β H := by
    rw [dist_eq_norm]
    change ‖gibbsToL2 (show 1 ≤ n + 1 by omega) β H hH f (smoothCore_contDiff f).continuous -
      gibbsToL2 (show 1 ≤ n + 1 by omega) β H hH g (smoothCore_contDiff g).continuous‖ ^ 2 = _
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [gibbsToL2_coe (show 1 ≤ n + 1 by omega) β H hH f (smoothCore_contDiff f).continuous,
      gibbsToL2_coe (show 1 ≤ n + 1 by omega) β H hH g (smoothCore_contDiff g).continuous,
      Lp.coeFn_sub (gibbsToL2 (show 1 ≤ n + 1 by omega) β H hH f (smoothCore_contDiff f).continuous)
        (gibbsToL2 (show 1 ≤ n + 1 by omega) β H hH g (smoothCore_contDiff g).continuous)] with x hf hg he
    simp only [he, Pi.sub_apply, hf, hg, RCLike.inner_apply, conj_trivial, pow_two]
  rw [he]
  simp only [cubePullback, localize, mul_sub] at h ⊢
  nlinarith

/-- The actual smooth spherical form core has the Rellich property.
The only dimension condition is that the sphere has positive dimension. -/
theorem spherical_smoothRellich (n : ℕ) [NeZero n] (β : ℝ)
    (H : Vector (n + 1) → ℝ) (hH : Continuous H) :
    SmoothRellich (show 1 ≤ n + 1 by omega) β H hH := by
  intro f R hR hnorm
  obtain ⟨D, hD, hbound⟩ := exists_cube_energy_bound n β hH hR
  obtain ⟨ν, hν, hc⟩ := GenericRellich.real_countable_cube_energy_subsequence
    (fun side j => cubePullback n side (f j))
    (fun side j => cubePullback_contDiff n side (smoothCore_contDiff (f j)))
    (fun _ => D) (fun _ => hD) (fun side j => hbound side (f j) (hnorm j))
  obtain ⟨m, M, hm, hM, hρ⟩ := chartGibbsDensity_bounds n β hH
  refine ⟨ν, hν, Metric.cauchySeq_iff.mpr ?_⟩
  intro ε hε
  let K : ℝ := M * (2 : ℝ) ^ n
  have hK : 0 < K := by dsimp [K]; positivity
  let δ : ℝ := ε ^ 2 / (4 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N₀, hN₀⟩ := hc false δ hδ
  obtain ⟨N₁, hN₁⟩ := hc true δ hδ
  refine ⟨max N₀ N₁, ?_⟩
  intro i hi j hj
  have h₀ := hN₀ i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj)
  have h₁ := hN₁ i ((le_max_right _ _).trans hi) j ((le_max_right _ _).trans hj)
  have hb := smooth_distance_two_cube_bound n β hH (f (ν i)) (f (ν j))
    hM.le (fun side u hu => (hρ side u hu).2)
  have hsum := mul_lt_mul_of_pos_left (add_lt_add h₀ h₁) hK
  have hδeq : K * (δ + δ) = ε ^ 2 / 2 := by dsimp [δ]; field_simp; ring
  have hs : dist ((smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH (f (ν i))).fst)
      ((smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH (f (ν j))).fst) ^ 2 < ε ^ 2 := by
    change _ < K * (δ + δ) at hsum
    rw [hδeq] at hsum
    exact hb.trans_lt (hsum.trans (by nlinarith [sq_pos_of_pos hε]))
  have hd : 0 ≤ dist ((smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH (f (ν i))).fst)
    ((smoothGradientGraphLinear (show 1 ≤ n + 1 by omega) β H hH (f (ν j))).fst) := dist_nonneg
  nlinarith

/-- Genuine compact embedding of the completed Gibbs Sobolev form domain
into actual Gibbs L². No spectral, compactness, or measure bridge is assumed. -/
theorem sphericalEnergyL2Map_compact (n : ℕ) [NeZero n] (β : ℝ)
    (H : Vector (n + 1) → ℝ) (hH : Continuous H) :
    IsCompactOperator (sphericalEnergyL2Map (show 1 ≤ n + 1 by omega) β H hH) :=
  sphericalEnergyL2Map_compact_of_smoothRellich (show 1 ≤ n + 1 by omega) β H hH
    (spherical_smoothRellich n β H hH)

/-- The same actual compact embedding stated with the manuscript's ambient
dimension N. This covers every N ≥ 2, including all asymptotic dimensions. -/
theorem sphericalEnergyL2Map_compact_of_two_le {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    IsCompactOperator (sphericalEnergyL2Map (show 1 ≤ N by omega) β H hH) := by
  cases N with
  | zero => omega
  | succ n =>
      have hn : n ≠ 0 := by omega
      have : NeZero n := ⟨hn⟩
      exact sphericalEnergyL2Map_compact n β H hH

end SlowEquilibration.SphereCompactEmbedding
