-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NegativeHessianLocalMaximum
public import SlowEquilibration.SphericalNegativeCountPrefactors

/-! Literal local maxima on the actual round sphere, identified with actual
negative-definite critical points under the proved almost-sure Morse property. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Filter Function Metric
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalPosteriorMaps NegativeDefiniteOperators SphericalMorse
open SphereChartVolume SphericalKacRiceGluing SphericalChartKacRice SphericalChartGeometry
open WholeFieldRegression GaussianLocalCoordinates
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped ENNReal Topology RealInnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma manuscriptChart_ne_pole {n : ℕ} {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖<2) :
    manuscriptChart n u ≠ southPole n := by
  have hm : manuscriptChart n u ∈ manuscriptChart n '' ball 0 2 :=
    mem_image_of_mem _ (by simpa using hu)
  rw [manuscriptChart_image_ball_except_pole] at hm
  exact hm.2

lemma manuscriptChartInverse_right_inv {n : ℕ} {x : Vector (n+1)}
    (hx : ‖x‖^2=(n+1 : ℕ)) (hp : x ≠ southPole n) :
    manuscriptChart n (manuscriptChartInverse n x) = x := by
  have hm : x ∈ manuscriptChart n '' ball 0 2 := by
    rw [manuscriptChart_image_ball_except_pole]
    exact ⟨hx,hp⟩
  obtain ⟨u,hu,rfl⟩ := hm
  rw [manuscriptChartInverse_left_inv (by simpa using hu)]

lemma chart_localMax_iff_sphere {n : ℕ} (f : Vector (n+1) → ℝ)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖<2) :
    IsLocalMax (fun v => f (manuscriptChart n v)) u ↔
      IsLocalMaxOn f {x | ‖x‖^2=(n+1 : ℕ)} (manuscriptChart n u) := by
  constructor
  · intro h
    have hh : IsLocalMax (fun x => f (manuscriptChart n (manuscriptChartInverse n x))) (manuscriptChart n u) := by
      change IsLocalMax ((fun v => f (manuscriptChart n v)) ∘ manuscriptChartInverse n) (manuscriptChart n u)
      apply IsLocalMax.comp_continuous (g := manuscriptChartInverse n)
      · rwa [manuscriptChartInverse_left_inv hu]
      · exact manuscriptChartInverse_continuousAt_chart hu
    have he : (fun x => f (manuscriptChart n (manuscriptChartInverse n x)))
        =ᶠ[𝓝[{x | ‖x‖^2=(n+1 : ℕ)}] (manuscriptChart n u)] f := by
      have hp : ∀ᶠ x in 𝓝 (manuscriptChart n u), x ≠ southPole n :=
        isOpen_compl_singleton.mem_nhds (manuscriptChart_ne_pole hu)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hp] with x hx hp
      rw [manuscriptChartInverse_right_inv hx hp]
    exact (hh.isLocalMaxOn _).congr he (manuscriptChart_norm_sq hu)
  · intro h
    have hh := h.comp_continuousOn (s := ball 0 2)
      (fun v hv => manuscriptChart_norm_sq (by simpa using hv))
      (manuscriptChart_contDiffOn n).continuousOn (by simpa using hu)
    exact hh.isLocalMax (isOpen_ball.mem_nhds (by simpa using hu))

lemma chart_gradient_neighborhood {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖<2) :
    ∀ᶠ v in 𝓝 u,
      HasFDerivAt (fun y => field c J (manuscriptChart n y))
        (innerSL ℝ (chartGamma n c v (euclideanDisorder J))) v ∧
      DifferentiableAt ℝ (fun y => chartGamma n c y (euclideanDisorder J)) v := by
  have hG : ContDiffOn ℝ 1 (fun y => chartGamma n c y (euclideanDisorder J)) (ball 0 2) :=
    (chartGamma_contDiffOn n c).clm_apply contDiffOn_const
  have hf := (field_contDiff c J).comp_contDiffOn (manuscriptChart_contDiffOn n)
  filter_upwards [isOpen_ball.mem_nhds (show u ∈ ball 0 2 by simpa using hu)] with v hv
  refine ⟨?_, (hG.contDiffAt (isOpen_ball.mem_nhds hv)).differentiableAt_one⟩
  have hd := ((hf.contDiffAt (isOpen_ball.mem_nhds hv)).differentiableAt (by simp)).hasFDerivAt
  have heq : fderiv ℝ (fun y => field c J (manuscriptChart n y)) v =
      innerSL ℝ (chartGamma n c v (euclideanDisorder J)) := by
    ext w
    have he := chartGamma_directional_derivative n c (show ‖v‖<2 by simpa using hv) (euclideanDisorder J) w
    simpa only [unpack_euclideanDisorder,innerSL_apply_apply,real_inner_comm] using he.symm
  rw [← heq]
  exact hd

lemma chart_hessian_continuousAt {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖<2) :
    ContinuousAt (fderiv ℝ (fun y => chartGamma n c y (euclideanDisorder J))) u := by
  have hG : ContDiffOn ℝ 1 (fun y => chartGamma n c y (euclideanDisorder J)) (ball 0 2) :=
    (chartGamma_contDiffOn n c).clm_apply contDiffOn_const
  exact ((hG.fderiv_of_isOpen isOpen_ball (m := 0) (by norm_num)).continuousOn).continuousAt
    (isOpen_ball.mem_nhds (by simpa using hu))

lemma sphere_localMax_critical_at_chart {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖<2)
    (hm : IsLocalMaxOn (field c J) {x | ‖x‖^2=(n+1 : ℕ)} (manuscriptChart n u)) :
    surfaceGradient (field c J) (manuscriptChart n u)=0 := by
  exact (actual_field_chart_critical_iff c J hu).mp ((chart_localMax_iff_sphere _ hu).mpr hm).fderiv_eq_zero

lemma sphere_localMax_of_negative_at_chart {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖<2)
    (hc : surfaceGradient (field c J) (manuscriptChart n u)=0)
    (hn : NegativeDefinite (intrinsicHessian (field c J) (manuscriptChart n u))) :
    IsLocalMaxOn (field c J) {x | ‖x‖^2=(n+1 : ℕ)} (manuscriptChart n u) := by
  apply (chart_localMax_iff_sphere _ hu).mp
  have hz : chartGamma n c u (euclideanDisorder J)=0 := by
    rw [chartGamma_zero_iff_derivative_zero n c hu,unpack_euclideanDisorder]
    exact (actual_field_chart_critical_iff c J hu).mpr hc
  have hh : NegativeDefinite (actualChartHessian n c J u) := by
    rw [actualChartHessian_eq_pullback c J hu hc,negativeDefinite_pullback_iff]
    exact hn
  exact isLocalMax_of_negative_gradient (chart_gradient_neighborhood c J hu)
    (chart_hessian_continuousAt c J hu) hz hh

lemma sphere_negative_of_localMax_at_chart {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+1) P)
    {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖<2)
    (hm : IsLocalMaxOn (field c J) {x | ‖x‖^2=(n+1 : ℕ)} (manuscriptChart n u))
    (hd : (intrinsicHessian (field c J) (manuscriptChart n u)).det ≠ 0) :
    NegativeDefinite (intrinsicHessian (field c J) (manuscriptChart n u)) := by
  have hc := sphere_localMax_critical_at_chart c J hu hm
  apply negativeDefinite_of_nonpos_of_det_ne_zero _
    (intrinsicHessian_field_symmetric (by omega) c J _ (by
      simpa only [SphericalAging.HardSphereDynamics.OnSphere,real_inner_self_eq_norm_sq] using manuscriptChart_norm_sq hu)) hd
  intro v
  let e := chartTangentEquiv u hu
  have hq := gradient_quadratic_nonpos_of_localMax (chart_gradient_neighborhood c J hu)
    ((chart_localMax_iff_sphere _ hu).mpr hm) (e.symm v)
  change inner ℝ (e.symm v) (actualChartHessian n c J u (e.symm v)) ≤ 0 at hq
  rw [actualChartHessian_eq_pullback c J hu hc] at hq
  have he : inner ℝ (e.symm v) (pullback e (intrinsicHessian (field c J) (manuscriptChart n u)) (e.symm v)) =
      inner ℝ v (intrinsicHessian (field c J) (manuscriptChart n u) v) := by
    change inner ℝ (e.symm v) ((e : _ →L[ℝ] _).adjoint ((intrinsicHessian (field c J) (manuscriptChart n u)) (e (e.symm v)))) = _
    rw [ContinuousLinearMap.adjoint_inner_right,e.apply_symm_apply]
    simp only [ContinuousLinearEquiv.coe_coe,e.apply_symm_apply]
  exact he ▸ hq

/-- Fermat's theorem on the actual sphere, including both chart poles.
The test curves are the actual orthogonal flows generated by tangent rotations. -/
theorem surfaceGradient_eq_zero_of_sphere_localMax {N : ℕ} (hN : N ≠ 0)
    (H : Vector N → ℝ) (x : Vector N) (hx : OnSphere x) (hH : DifferentiableAt ℝ H x)
    (hmax : IsLocalMaxOn H {y | OnSphere y} x) : surfaceGradient H x=0 := by
  have hdir (v : Vector N) (hv : inner ℝ x v=0) : fderiv ℝ H x v=0 := by
    let A := tangentRotation x v
    have hA : star A = -A := tangentRotation_skew x v
    have hAx : A x=v := tangentRotation_apply hN x v hx hv
    have hcurve := operatorFlow_apply_hasDerivAt A 0 x
    have hcomp := hH.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve
      (show x=operatorFlow A 0 x from (operatorFlow_zero A x).symm)
    have ht : Tendsto (fun t : ℝ => operatorFlow A t x) (𝓝 0) (𝓝[{y | OnSphere y}] x) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_,Filter.Eventually.of_forall (fun t => ?_)⟩
      · simpa only [ContinuousAt,operatorFlow_zero] using hcurve.continuousAt
      · rw [mem_ofPred_eq,onSphere_iff_norm_sq,operatorFlow_norm A hA t x]
        exact (onSphere_iff_norm_sq x).mp hx
    have hlocal : IsLocalMax (fun t => H (operatorFlow A t x)) 0 := by
      change ∀ᶠ t in 𝓝 (0:ℝ), H (operatorFlow A t x) ≤ H (operatorFlow A 0 x)
      rw [operatorFlow_zero]
      exact ht.eventually hmax
    simpa only [Function.comp_def,operatorFlow_zero,hAx] using hlocal.hasDerivAt_eq_zero hcomp
  apply ext_inner_right ℝ
  intro v
  rw [inner_surfaceGradient,inner_zero_left]
  apply hdir
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (tangentProjection_mem hN x v hx)

/-- Almost surely, literal local maxima of the actual spherical field are
exactly its intrinsic critical points with negative-definite intrinsic Hessian. -/
theorem actual_sphere_localMax_iff_negative_ae (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂disorderLaw (n+1) μ.maxDegree, ∀ x : Vector (n+1), ‖x‖^2=(n+1 : ℕ) →
      (IsLocalMaxOn (field c J) {y | ‖y‖^2=(n+1 : ℕ)} x ↔
        surfaceGradient (field c J) x=0 ∧ NegativeDefinite (intrinsicHessian (field c J) x)) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  filter_upwards [actual_sphere_morse_ae n hn μ hQ,
    SphericalIntrinsicKacRice.fixed_point_noncritical_ae n hn μ hQ (southPole n) (southPole_norm_sq n)] with J hM hpole
  intro x hx
  have hcrit (hm : IsLocalMaxOn (field c J) {y | ‖y‖^2=(n+1 : ℕ)} x) :
      surfaceGradient (field c J) x=0 := by
    apply surfaceGradient_eq_zero_of_sphere_localMax (by omega) _ x
      ((onSphere_iff_norm_sq x).mpr hx) ((field_contDiff c J).differentiable (by simp) x)
    simpa only [onSphere_iff_norm_sq] using hm
  have hchart (hc : surfaceGradient (field c J) x=0) :
      ∃ u : EuclideanSpace ℝ (Fin n), ‖u‖<2 ∧ manuscriptChart n u=x := by
    have hp : x ≠ southPole n := fun he => hpole (he ▸ hc)
    have hm : x ∈ manuscriptChart n '' ball 0 2 := by
      rw [manuscriptChart_image_ball_except_pole]
      exact ⟨hx,hp⟩
    obtain ⟨u,hu,he⟩ := hm
    exact ⟨u,by simpa using hu,he⟩
  constructor
  · intro hm
    have hc := hcrit hm
    have hd := hM x ⟨hx,hc⟩
    obtain ⟨u,hu,rfl⟩ := hchart hc
    exact ⟨hc,sphere_negative_of_localMax_at_chart c J hu hm hd⟩
  · rintro ⟨hc,hneg⟩
    obtain ⟨u,hu,rfl⟩ := hchart hc
    exact sphere_localMax_of_negative_at_chart c J hu hc hneg

end
end SlowEquilibration.SphericalMarkedWindows
