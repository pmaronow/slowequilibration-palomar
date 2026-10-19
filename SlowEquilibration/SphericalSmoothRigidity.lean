module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphereCompactEmbedding
public import SlowEquilibration.SphericalInfiniteDimensional
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! # True smooth rigidity on the actual connected sphere -/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
open Set MeasureTheory Filter
open SphericalModel SphericalAging.HardSphereDynamics
open SphereChartVolume SphereCompactEmbedding
open scoped InnerProductSpace Topology ContDiff

lemma signedChart_onSphere (n : ℕ) (side : Bool) {u : ChartSpace n} (hu : ‖u‖ < 2) :
    OnSphere (signedChart n side u) := by
  have hn : ‖manuscriptChart n u‖ ^ 2 = (n + 1 : ℕ) := by
    rw [manuscriptChart, norm_smul, LinearIsometryEquiv.norm_map,
      sphereChartND_norm hu.le, mul_one, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (Nat.cast_nonneg (n + 1))]
  rw [OnSphere, real_inner_self_eq_norm_sq]
  cases side
  · exact hn
  · simpa only [signedChart, ite_true, norm_neg] using hn

lemma chartPullback_constant_of_surfaceGradient_zero (n : ℕ) (side : Bool)
    {f : Vector (n + 1) → ℝ} (hf : ContDiff ℝ 1 f)
    (hgrad : ∀ x, OnSphere x → surfaceGradient f x = 0)
    {u v : ChartSpace n} (hu : ‖u‖ < 2) (hv : ‖v‖ < 2) :
    f (signedChart n side u) = f (signedChart n side v) := by
  let g : ChartSpace n → ℝ := fun w => f (signedChart n side w)
  have hd (w : ChartSpace n) (hw : w ∈ Metric.ball 0 2) : DifferentiableAt ℝ g w :=
    (chartPullback_hasFDerivAt n side (hf.differentiable (by norm_num)) (by simpa using hw)).differentiableAt
  have hz (w : ChartSpace n) (hw : w ∈ Metric.ball 0 2) : fderiv ℝ g w = 0 := by
    rw [(chartPullback_hasFDerivAt n side (hf.differentiable (by norm_num)) (by simpa using hw)).fderiv]
    ext a
    rw [ContinuousLinearMap.comp_apply,
      chartPullback_derivative_surfaceGradient n side f (by simpa using hw),
      hgrad _ (signedChart_onSphere n side (by simpa using hw)), inner_zero_left]
    rfl
  have hzw (w : ChartSpace n) (hw : w ∈ Metric.ball 0 2) :
      fderivWithin ℝ g (Metric.ball 0 2) w = 0 := by
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hw, hz w hw]
  exact (convex_ball (0 : ChartSpace n) 2).is_const_of_fderivWithin_eq_zero
    (fun w hw => (hd w hw).differentiableWithinAt) hzw (by simpa using hu) (by simpa using hv)

lemma manuscriptChart_equator_antipodal (n : ℕ) {u : ChartSpace n}
    (hu : ‖u‖ ^ 2 = 2) : manuscriptChart n u = -manuscriptChart n (-u) := by
  have hchart : sphereChartND u = -sphereChartND (-u) := by
    apply WithLp.ofLp_injective 2
    simp [sphereChartND, sphereChartScaleND, hu]
  rw [manuscriptChart, manuscriptChart, hchart, map_neg, smul_neg]

/-- Ambient C¹ functions with actual zero surface gradient are constant
on the actual sphere in all positive spherical dimensions. -/
theorem surfaceGradient_zero_implies_constant {N : ℕ} (hN : 2 ≤ N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 1 f)
    (hgrad : ∀ x, OnSphere x → surfaceGradient f x = 0) :
    ∃ c : ℝ, ∀ x, OnSphere x → f x = c := by
  cases N with
  | zero => omega
  | succ n =>
    have hn : 0 < n := by omega
    let i : Fin n := ⟨0, hn⟩
    let u : ChartSpace n := Real.sqrt 2 • basisVector i
    have hu : ‖u‖ ^ 2 = 2 := by
      simp only [u, norm_smul, basisVector, EuclideanSpace.norm_single, norm_one,
        mul_one, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hu2 : ‖u‖ < 2 := by nlinarith [norm_nonneg u]
    have hneg : ‖-u‖ < 2 := by simpa using hu2
    have hzero : ‖(0 : ChartSpace n)‖ < 2 := by simp
    have heq : f (signedChart n false 0) = f (signedChart n true 0) := by
      calc
        _ = f (signedChart n false u) :=
          chartPullback_constant_of_surfaceGradient_zero n false hf hgrad hzero hu2
        _ = f (signedChart n true (-u)) := by
          congr 1
          exact manuscriptChart_equator_antipodal n hu
        _ = _ := chartPullback_constant_of_surfaceGradient_zero n true hf hgrad hneg hzero
    refine ⟨f (signedChart n false 0), ?_⟩
    intro x hx
    have hs : x ∈ Metric.sphere (0 : Vector (n + 1)) (Real.sqrt (n + 1 : ℕ)) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        SphericalAging.LandscapeDerivatives.sphere_norm x (by simpa only [OnSphere, real_inner_self_eq_norm_sq] using hx)
    rw [manuscriptChart_two_closed_charts_cover] at hs
    have hinside {v : ChartSpace n} (hv : v ∈ Metric.closedBall 0 (Real.sqrt 2)) : ‖v‖ < 2 := by
      have hnorm : ‖v‖ ≤ Real.sqrt 2 := by simpa using hv
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    rcases hs with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
    · exact chartPullback_constant_of_surfaceGradient_zero n false hf hgrad (hinside hv) hzero
    · exact (chartPullback_constant_of_surfaceGradient_zero n true hf hgrad (hinside hv) hzero).trans heq.symm

/-- Actual zero Gibbs Dirichlet energy of a C¹ function forces its true
spherical restriction to be constant. -/
theorem dirichletEnergy_zero_implies_constant {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    {H f : Vector N → ℝ} (hH : Continuous H) (hf : ContDiff ℝ 1 f)
    (hE : dirichletEnergy N β H f = 0) :
    ∃ c : ℝ, ∀ x, OnSphere x → f x = c := by
  apply surfaceGradient_zero_implies_constant hN hf
  intro x hx
  have hc : Continuous (fun y => ‖surfaceGradient f y‖ ^ 2) :=
    (surfaceGradient_continuous hf).norm.pow 2
  have hi : Integrable (fun y => ‖surfaceGradient f y‖ ^ 2) (gibbsLaw N β H) :=
    integrable_gibbs_of_continuous (by omega) β hH hc
  have hae : (fun y => ‖surfaceGradient f y‖ ^ 2) =ᵐ[gibbsLaw N β H] 0 := by
    exact (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hi).mp
      ((dirichletEnergy_eq_integral_norm_sq N β H f).symm.trans hE)
  have hz := continuous_eq_zero_onSphere_of_gibbs_ae (show 1 ≤ N by omega) β hH hc hae x hx
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end
end SlowEquilibration.SphericalForm
