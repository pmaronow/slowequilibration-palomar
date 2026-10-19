module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.BumpDifferential
public import SlowEquilibration.SphericalInfiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section

/-! # Actual radial smoothing kernels on the constructed sphere law -/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped InnerProductSpace Topology ContDiff

/-- The manuscript radial cutoff reused at a fixed width ε. -/
def sphereSmoothingKernel {N : ℕ} (ε : ℝ) (x y : Vector N) : ℝ :=
  translatedBump Real.smoothTransition 2 ε x y

lemma sphereSmoothingKernel_nonneg {N : ℕ} (ε : ℝ) (x y : Vector N) :
    0 ≤ sphereSmoothingKernel ε x y := Real.smoothTransition.nonneg _

lemma sphereSmoothingKernel_le_one {N : ℕ} (ε : ℝ) (x y : Vector N) :
    sphereSmoothingKernel ε x y ≤ 1 := Real.smoothTransition.le_one _

lemma sphereSmoothingKernel_symm {N : ℕ} (ε : ℝ) (x y : Vector N) :
    sphereSmoothingKernel ε x y = sphereSmoothingKernel ε y x := by
  simp only [sphereSmoothingKernel, translatedBump, norm_sub_rev]

lemma sphereSmoothingKernel_diagonal {N : ℕ} (ε : ℝ) (x : Vector N) :
    sphereSmoothingKernel ε x x = 1 := by
  simp only [sphereSmoothingKernel, translatedBump, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_div, sub_zero, mul_one]
  exact Real.smoothTransition.one_of_one_le (by norm_num)

lemma sphereSmoothingKernel_zero_of_dist {N : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x y : Vector N) (hxy : ε ≤ dist x y) : sphereSmoothingKernel ε x y = 0 := by
  apply le_antisymm _ (sphereSmoothingKernel_nonneg ε x y)
  by_contra hn
  have hs := translatedBump_support Real.smoothTransition 2 ε x y (by norm_num) hε
    (fun t ht => Real.smoothTransition.zero_of_nonpos ht) (lt_of_not_ge hn)
  exact (not_lt_of_ge hxy) (by simpa only [dist_eq_norm] using hs)

lemma sphereSmoothingKernel_contDiff {N : ℕ} (ε : ℝ) :
    ContDiff ℝ ∞ (fun z : Vector N × Vector N => sphereSmoothingKernel ε z.1 z.2) := by
  unfold sphereSmoothingKernel translatedBump
  have hsq : ContDiff ℝ ∞ (fun z : Vector N × Vector N => ‖z.1 - z.2‖ ^ 2) :=
    (contDiff_fst.sub contDiff_snd).norm_sq ℝ
  have ha : ContDiff ℝ ∞ (fun z : Vector N × Vector N => 2 * (1 - ‖z.1 - z.2‖ ^ 2 / ε ^ 2)) :=
    contDiff_const.mul (contDiff_const.sub (hsq.div_const (ε ^ 2)))
  exact Real.smoothTransition.contDiff.comp ha

lemma sphereSmoothingKernel_left_contDiff {N : ℕ} (ε : ℝ) (y : Vector N) :
    ContDiff ℝ ∞ (fun x : Vector N => sphereSmoothingKernel ε x y) := by
  unfold sphereSmoothingKernel translatedBump
  have hsq : ContDiff ℝ ∞ (fun x : Vector N => ‖x - y‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have ha : ContDiff ℝ ∞ (fun x : Vector N => 2 * (1 - ‖x - y‖ ^ 2 / ε ^ 2)) :=
    contDiff_const.mul (contDiff_const.sub (hsq.div_const (ε ^ 2)))
  exact Real.smoothTransition.contDiff.comp ha

lemma sphereSmoothingKernel_right_contDiff {N : ℕ} (ε : ℝ) (x : Vector N) :
    ContDiff ℝ ∞ (sphereSmoothingKernel ε x) := by
  unfold sphereSmoothingKernel translatedBump
  have hsq : ContDiff ℝ ∞ (fun y : Vector N => ‖x - y‖ ^ 2) :=
    (contDiff_const.sub contDiff_id).norm_sq ℝ
  have ha : ContDiff ℝ ∞ (fun y : Vector N => 2 * (1 - ‖x - y‖ ^ 2 / ε ^ 2)) :=
    contDiff_const.mul (contDiff_const.sub (hsq.div_const (ε ^ 2)))
  exact Real.smoothTransition.contDiff.comp ha

lemma sphereSmoothingKernel_isometry {N : ℕ} (ε : ℝ) (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (x y : Vector N) : sphereSmoothingKernel ε (U x) (U y) = sphereSmoothingKernel ε x y := by
  simp only [sphereSmoothingKernel, translatedBump, ← map_sub, LinearIsometryEquiv.norm_map]

lemma sphereSmoothingKernel_integrable {N : ℕ} (ε : ℝ) (x : Vector N) :
    Integrable (sphereSmoothingKernel ε x) (sphereLaw N) := by
  apply (integrable_const (1 : ℝ)).mono'
    (sphereSmoothingKernel_right_contDiff ε x).continuous.aestronglyMeasurable
  exact ae_of_all _ (fun y => by
    rw [Real.norm_of_nonneg (sphereSmoothingKernel_nonneg ε x y)]
    exact sphereSmoothingKernel_le_one ε x y)

/-- True constant radial row mass under the actual Gaussian-direction law. -/
theorem sphereSmoothingKernel_row_integral_eq {N : ℕ} (ε : ℝ) (x y : Vector N)
    (hxy : ‖x‖ = ‖y‖) :
    (∫ z, sphereSmoothingKernel ε x z ∂sphereLaw N) =
      ∫ z, sphereSmoothingKernel ε y z ∂sphereLaw N := by
  let U : Vector N ≃ₗᵢ[ℝ] Vector N := (ℝ ∙ (x - y))ᗮ.reflection
  have hU : U x = y := Submodule.reflection_sub hxy
  have hmp : MeasurePreserving U (sphereLaw N) (sphereLaw N) :=
    ⟨U.continuous.measurable, sphereLaw_rotation_invariant U⟩
  have hi := hmp.integral_comp U.toHomeomorph.measurableEmbedding (sphereSmoothingKernel ε y)
  have he : (fun z => sphereSmoothingKernel ε y (U z)) = sphereSmoothingKernel ε x := by
    funext z
    rw [← hU, sphereSmoothingKernel_isometry]
  rw [he] at hi
  exact hi

lemma continuous_eq_zero_onSphere_of_sphere_ae {N : ℕ} (hN : 1 ≤ N)
    {f : Vector N → ℝ} (hf : Continuous f) (hae : f =ᵐ[sphereLaw N] 0)
    (x : Vector N) (hx : OnSphere x) : f x = 0 :=
  continuous_eq_zero_onSphere_of_gibbs_ae hN 0 (H := fun _ => 0) continuous_const hf
    (hae.filter_mono (gibbsLaw_absolutelyContinuous 0 (fun _ => 0)).ae_le) x hx

/-- Every true spherical radial row has strictly positive mass. -/
theorem sphereSmoothingKernel_row_integral_pos {N : ℕ} (hN : 1 ≤ N) (ε : ℝ)
    (x : Vector N) (hx : OnSphere x) :
    0 < ∫ y, sphereSmoothingKernel ε x y ∂sphereLaw N := by
  have hi := sphereSmoothingKernel_integrable ε x
  have hn : 0 ≤ ∫ y, sphereSmoothingKernel ε x y ∂sphereLaw N :=
    integral_nonneg (fun y => sphereSmoothingKernel_nonneg ε x y)
  by_contra hp
  have hz : (∫ y, sphereSmoothingKernel ε x y ∂sphereLaw N) = 0 := le_antisymm (le_of_not_gt hp) hn
  have hae := (integral_eq_zero_iff_of_nonneg (sphereSmoothingKernel_nonneg ε x) hi).mp hz
  have he := continuous_eq_zero_onSphere_of_sphere_ae hN
    (sphereSmoothingKernel_right_contDiff ε x).continuous hae x hx
  rw [sphereSmoothingKernel_diagonal] at he
  norm_num at he

/-- The actual radial base bump. -/
def sphereRadialBump {N : ℕ} (ε : ℝ) (z : Vector N) : ℝ := sphereSmoothingKernel ε z 0

lemma sphereRadialBump_contDiff {N : ℕ} (ε : ℝ) :
    ContDiff ℝ ∞ (sphereRadialBump (N := N) ε) := sphereSmoothingKernel_left_contDiff ε 0

lemma sphereSmoothingKernel_eq_radial {N : ℕ} (ε : ℝ) (x y : Vector N) :
    sphereSmoothingKernel ε x y = sphereRadialBump ε (x - y) := by
  simp [sphereSmoothingKernel, sphereRadialBump, translatedBump]

lemma sphereRadialBump_hasCompactSupport {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (sphereRadialBump (N := N) ε) := by
  apply (isCompact_closedBall (0 : Vector N) ε).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  by_contra hn
  have hs : sphereRadialBump ε z = 0 := sphereSmoothingKernel_zero_of_dist hε z 0 (by simpa using (lt_of_not_ge hn).le)
  exact hz hs

/-- The actual base bump has a finite uniform differential bound. -/
theorem sphereRadialBump_derivative_bound {N : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : Vector N, ‖fderiv ℝ (sphereRadialBump ε) z‖ ≤ B := by
  obtain ⟨B, hB⟩ := ((sphereRadialBump_hasCompactSupport hε).fderiv ℝ).exists_bound_of_continuous
    ((sphereRadialBump_contDiff ε).continuous_fderiv (by simp))
  exact ⟨max B 0, le_max_right _ _, fun z => (hB z).trans (le_max_left _ _)⟩

/-- Actual spherical smoothing applied to any integrable signed weight.
The measure is arbitrary here; later it is the true Gibbs law and the weight
is the actual L² value divided by its actual Gibbs density. -/
def sphereSmoothingMoment {N : ℕ} (μ : Measure (Vector N)) (ε : ℝ)
    (w : Vector N → ℝ) (x : Vector N) : ℝ :=
  ∫ y, w y * sphereSmoothingKernel ε x y ∂μ

lemma sphereSmoothingKernel_hasFDerivAt_left {N : ℕ} (ε : ℝ) (x y : Vector N) :
    HasFDerivAt (fun z => sphereSmoothingKernel ε z y)
      (fderiv ℝ (sphereRadialBump ε) (x - y)) x := by
  have hsub : HasFDerivAt (fun z : Vector N => z - y) (ContinuousLinearMap.id ℝ (Vector N)) x :=
    (hasFDerivAt_id x).sub_const y
  have hr : HasFDerivAt (sphereRadialBump (N := N) ε)
      (fderiv ℝ (sphereRadialBump ε) (x - y)) (x - y) :=
    ((sphereRadialBump_contDiff (N := N) ε).differentiable (by simp) (x - y)).hasFDerivAt
  have hd := hr.comp x hsub
  simpa only [Function.comp_def, ← sphereSmoothingKernel_eq_radial,
    ContinuousLinearMap.comp_id] using hd

lemma sphereSmoothingMoment_integrable {N : ℕ} {μ : Measure (Vector N)} {w : Vector N → ℝ}
    (hw : Integrable w μ) (ε : ℝ) (x : Vector N) :
    Integrable (fun y => w y * sphereSmoothingKernel ε x y) μ := by
  apply hw.norm.mono'
    (hw.aestronglyMeasurable.mul (sphereSmoothingKernel_right_contDiff ε x).continuous.aestronglyMeasurable)
  exact ae_of_all _ (fun y => by
    change ‖w y * sphereSmoothingKernel ε x y‖ ≤ ‖w y‖
    rw [norm_mul, Real.norm_of_nonneg (sphereSmoothingKernel_nonneg ε x y)]
    exact (mul_le_mul_of_nonneg_left (sphereSmoothingKernel_le_one ε x y) (norm_nonneg _)).trans_eq (mul_one _))

/-- True C¹ regularity of smoothing an integrable signed weight, with the
actual derivative obtained by dominated Bochner differentiation. -/
theorem sphereSmoothingMoment_contDiff_one {N : ℕ} {μ : Measure (Vector N)}
    {w : Vector N → ℝ} (hw : Integrable w μ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 1 (sphereSmoothingMoment μ ε w) := by
  obtain ⟨B, hB, hb⟩ := sphereRadialBump_derivative_bound (N := N) hε
  let D : Vector N → Vector N → (Vector N →L[ℝ] ℝ) :=
    fun x y => w y • fderiv ℝ (sphereRadialBump ε) (x - y)
  have hcont : Continuous (fderiv ℝ (sphereRadialBump (N := N) ε)) :=
    (sphereRadialBump_contDiff ε).continuous_fderiv (by simp)
  have hmeas (x : Vector N) : AEStronglyMeasurable (D x) μ :=
    hw.aestronglyMeasurable.smul
      ((hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hbound (x y : Vector N) : ‖D x y‖ ≤ B * ‖w y‖ := by
    dsimp [D]
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hDc : Continuous (fun x => ∫ y, D x y ∂μ) := by
    apply continuous_of_dominated hmeas (fun x => ae_of_all _ (fun y => hbound x y))
      (hw.norm.const_mul B)
    exact ae_of_all _ (fun y => by
      change Continuous (fun x : Vector N => w y • fderiv ℝ (sphereRadialBump ε) (x - y))
      exact (hcont.comp (continuous_id.sub continuous_const)).const_smul (w y))
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨fun x => ∫ y, D x y ∂μ, hDc, ?_⟩
  intro x
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := fun y => B * ‖w y‖)
    (show Set.univ ∈ 𝓝 x from Filter.univ_mem)
    (Eventually.of_forall (fun z => hw.aestronglyMeasurable.mul
      (sphereSmoothingKernel_right_contDiff ε z).continuous.aestronglyMeasurable))
    (sphereSmoothingMoment_integrable hw ε x) (hmeas x)
    (ae_of_all _ (fun y z _ => hbound z y)) (hw.norm.const_mul B)
  exact ae_of_all _ (fun y z _ => (sphereSmoothingKernel_hasFDerivAt_left ε z y).const_mul (w y))

/-- The actual smoothing derivative is the integral of the actual radial
kernel derivatives. -/
theorem sphereSmoothingMoment_fderiv {N : ℕ} {μ : Measure (Vector N)}
    {w : Vector N → ℝ} (hw : Integrable w μ) {ε : ℝ} (hε : 0 < ε) (x : Vector N) :
    fderiv ℝ (sphereSmoothingMoment μ ε w) x =
      ∫ y, w y • fderiv ℝ (sphereRadialBump ε) (x - y) ∂μ := by
  obtain ⟨B, hB, hb⟩ := sphereRadialBump_derivative_bound (N := N) hε
  have hcont : Continuous (fderiv ℝ (sphereRadialBump (N := N) ε)) :=
    (sphereRadialBump_contDiff ε).continuous_fderiv (by simp)
  have hmeas : AEStronglyMeasurable
      (fun y => w y • fderiv ℝ (sphereRadialBump ε) (x - y)) μ :=
    hw.aestronglyMeasurable.smul
      ((hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hbound (z y : Vector N) :
      ‖w y • fderiv ℝ (sphereRadialBump ε) (z - y)‖ ≤ B * ‖w y‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)).trans_eq (mul_comm _ _)
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := fun y => B * ‖w y‖)
    (show Set.univ ∈ 𝓝 x from Filter.univ_mem)
    (Eventually.of_forall (fun z => hw.aestronglyMeasurable.mul
      (sphereSmoothingKernel_right_contDiff ε z).continuous.aestronglyMeasurable))
    (sphereSmoothingMoment_integrable hw ε x) hmeas
    (ae_of_all _ (fun y z _ => hbound z y)) (hw.norm.const_mul B)
    (ae_of_all _ (fun y z _ => (sphereSmoothingKernel_hasFDerivAt_left ε z y).const_mul (w y)))).fderiv

end
end SlowEquilibration.SphericalForm
