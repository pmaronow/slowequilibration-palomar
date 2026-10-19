-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorMeasurable
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! A Borel determinant representative agreeing with the genuine intrinsic
determinant at every actual spherical critical point. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorMaps
open MeasureTheory ProbabilityTheory Set Function Metric
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicGradientRegression
open SphericalMarkedWindows SphereHessian SphereChartVolume SphericalChartKacRice
open SphericalKacRiceGluing SphericalMorse SphericalForm GaussianLocalCoordinates
open scoped ENNReal Topology RealInnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma euclideanDisorder_measurable (N P : ℕ) :
    Measurable (euclideanDisorder (N := N) (P := P)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp
    (flatDisorder_measurable N P)

lemma manuscriptChartInverse_measurable (n : ℕ) : Measurable (manuscriptChartInverse n) := by
  have hc := (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).continuous.comp
    (radiusHomeomorph n).symm.continuous
  unfold manuscriptChartInverse sphereChartInvND
  exact (((measurable_const.add hc.snd.measurable).div_const 2).sqrt.inv).smul hc.fst.measurable

/-- Spatial derivative of the actual linear coefficient observation, in a
Borel form defined throughout coordinate space. -/
def coordinateHessian {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (fderiv ℝ (chartGamma n c) u).flip (euclideanDisorder J)

lemma coordinateHessian_measurable {P : ℕ} (n : ℕ) (c : Degree P → ℝ) :
    Measurable (fun p : Disorder (n+1) P × EuclideanSpace ℝ (Fin n) => coordinateHessian n c p.1 p.2) := by
  have hT : Measurable (fun p : Disorder (n+1) P × EuclideanSpace ℝ (Fin n) =>
      (fderiv ℝ (chartGamma n c) p.2).flip) := (ContinuousLinearMap.flipₗᵢ ℝ (EuclideanSpace ℝ (Fin n))
    (EuclideanDisorder (n+1) P) (EuclideanSpace ℝ (Fin n))).continuous.measurable.comp
      ((measurable_fderiv ℝ (chartGamma n c)).comp measurable_snd)
  have hz : Measurable (fun p : Disorder (n+1) P × EuclideanSpace ℝ (Fin n) =>
      euclideanDisorder p.1) := (euclideanDisorder_measurable (n+1) P).comp measurable_fst
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp (hT.prodMk hz)

lemma coordinateHessian_eq {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    coordinateHessian n c J u = actualChartHessian n c J u := by
  have hd := ((chartGamma_contDiffOn n c).contDiffAt
    (isOpen_ball.mem_nhds (by simpa using hu))).differentiableAt_one
  symm
  simpa only [coordinateHessian, actualChartHessian, spatialJacobian,
    ContinuousLinearMap.comp_zero, zero_add] using
      (hd.hasFDerivAt.clm_apply (hasFDerivAt_const (euclideanDisorder J) u)).fderiv

lemma manuscriptChartGram_measurable (n : ℕ) : Measurable (manuscriptChartGram n) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  exact (continuous_fst.inner continuous_snd).measurable.comp
    (((ContinuousLinearMap.measurable_apply (EuclideanSpace.basisFun (Fin n) ℝ i)).comp
      (measurable_fderiv ℝ (manuscriptChart n))).prodMk
        ((ContinuousLinearMap.measurable_apply (EuclideanSpace.basisFun (Fin n) ℝ j)).comp
          (measurable_fderiv ℝ (manuscriptChart n))))

/-- A Borel ambient representative for the true absolute intrinsic determinant
on actual critical fields, including the omitted chart pole. -/
def criticalDet {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (x : Vector (n+1)) : ℝ :=
  if x = southPole n then |(intrinsicHessian (field c J) (southPole n)).det|
  else |(coordinateHessian n c J (manuscriptChartInverse n x)).det| /
    |(manuscriptChartGram n (manuscriptChartInverse n x)).det|

lemma criticalDet_nonneg {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (x : Vector (n+1)) : 0 ≤ criticalDet n c J x := by
  unfold criticalDet
  split_ifs <;> positivity

lemma criticalDet_measurable {P : ℕ} (n : ℕ) (c : Degree P → ℝ) :
    Measurable (fun p : Disorder (n+1) P × Vector (n+1) => criticalDet n c p.1 p.2) := by
  have hp : Measurable (fun J : Disorder (n+1) P => |(intrinsicHessian (field c J) (southPole n)).det|) := by
    have h := (intrinsicDet_measurable c (southPole n) (southPole_norm_sq n)).ennreal_toReal
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h
  have hcoord := continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp
    (coordinateHessian_measurable n c))
  have hg := continuous_abs.measurable.comp
    (continuous_id.matrix_det.measurable.comp (manuscriptChartGram_measurable n))
  have hi : Measurable (fun p : Disorder (n+1) P × Vector (n+1) => manuscriptChartInverse n p.2) :=
    (manuscriptChartInverse_measurable n).comp measurable_snd
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
    (hp.comp measurable_fst) ((hcoord.comp (measurable_fst.prodMk hi)).div (hg.comp hi))

/-- This Borel representative equals the actual full intrinsic determinant
at every genuine spherical critical point, not just almost everywhere. -/
lemma criticalDet_eq {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = (n+1 : ℕ))
    (hcrit : surfaceGradient (field c J) x = 0) :
    criticalDet n c J x = |(intrinsicHessian (field c J) x).det| := by
  by_cases hp : x = southPole n
  · subst x
    simp only [criticalDet, ite_true]
  · have him : x ∈ manuscriptChart n '' ball 0 2 := by
      rw [manuscriptChart_image_ball_except_pole]
      exact ⟨hx, hp⟩
    obtain ⟨u, hu, rfl⟩ := him
    have hu' : ‖u‖ < 2 := by simpa using hu
    rw [criticalDet, ite_eq_right hp, manuscriptChartInverse_left_inv hu',
      coordinateHessian_eq n c J hu', actualChartHessian_det c J hu' hcrit, abs_mul]
    exact mul_div_cancel_left₀ _ (abs_ne_zero.mpr (manuscriptChartGram_det_pos hu').ne')

end
end SlowEquilibration.SphericalPosteriorMaps
