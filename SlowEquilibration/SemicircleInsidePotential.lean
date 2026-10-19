-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemicircleAngularPotential
public import SlowEquilibration.CircleLogMoment

/-! The actual semicircle logarithmic potential inside its spectral support.
The singular angular logarithm is split into two actual unit-circle poles;
the weighted boundary-log moment is proved by the Poisson formula and DCT. -/

@[expose] public section
namespace SlowEquilibration.SemicirclePotential

noncomputable section
open MeasureTheory Set Function Filter Real Complex Metric
open SemicircleAngularPotential CircleLogMoment
open scoped Topology Interval ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma unit_factor_norm {rho z : ℂ} (hρ : ‖rho‖=1) (hz : ‖z‖=1) :
    |2*rho.re-2*z.re|=‖z-rho‖*‖z-conj rho‖ := by
  have hp : (z-rho)*(z-conj rho)=z*((2*z.re-2*rho.re : ℝ):ℂ) := by
    apply Complex.ext
    · simp only [Complex.mul_re,Complex.sub_re,Complex.sub_im,Complex.conj_re,
        Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
      nlinarith [unit_re_im_sq hρ,unit_re_im_sq hz]
    · simp only [Complex.mul_im,Complex.sub_re,Complex.sub_im,Complex.conj_re,
        Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add]
      ring
  have hn := congrArg norm hp
  rw [norm_mul,norm_mul,hz,one_mul,Complex.norm_real,Real.norm_eq_abs] at hn
  simpa only [abs_sub_comm] using hn.symm

lemma unit_factor_log {rho z : ℂ} (hρ : ‖rho‖=1) (hz : ‖z‖=1)
    (hzρ : z≠rho) (hzc : z≠conj rho) :
    Real.log |2*rho.re-2*z.re|=Real.log ‖z-rho‖+Real.log ‖z-conj rho‖ := by
  rw [unit_factor_norm hρ hz,Real.log_mul]
  · exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzρ)
  · exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hzc)

lemma potential_eq_circleAverage (u : ℝ) :
    potential u=circleAverage (fun z : ℂ =>
      (1-(2*z.re^2-1))*Real.log |u-2*z.re|) 0 1 := by
  rw [potential_eq_circle_weighted_integral,circleAverage_def,smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro theta ht
  have hc : (circleMap 0 1 theta).re=Real.cos theta := by
    simp [circleMap,Complex.exp_mul_I,← Complex.ofReal_cos]
  change (1-Real.cos (2*theta))*Real.log |u-2*Real.cos theta| =
    (1-(2*(circleMap 0 1 theta).re^2-1))*Real.log |u-2*(circleMap 0 1 theta).re|
  rw [hc,Real.cos_two_mul]

lemma weighted_boundary_CircleIntegrable (rho : ℂ) :
    CircleIntegrable (fun z : ℂ => (1-(2*z.re^2-1))*Real.log ‖z-rho‖) 0 1 := by
  have h := (boundaryLog_circleIntegrable rho).continuousOn_smul
    (show ContinuousOn (fun z : ℂ => 1-(2*z.re^2-1)) (sphere (0:ℂ) |(1:ℝ)|) from by fun_prop)
  convert h using 1

lemma potential_unit_real_part {rho : ℂ} (hρ : ‖rho‖=1) :
    potential (2*rho.re)=rho.re^2-1/2 := by
  rw [potential_eq_circleAverage]
  have hc : circleAverage (fun z : ℂ =>
      (1-(2*z.re^2-1))*Real.log |2*rho.re-2*z.re|) 0 1=
      circleAverage (fun z : ℂ =>
        (1-(2*z.re^2-1))*Real.log ‖z-rho‖+
        (1-(2*z.re^2-1))*Real.log ‖z-conj rho‖) 0 1 := by
    apply circleAverage_congr_codiscreteWithin ?_ (by norm_num)
    filter_upwards [Filter.self_mem_codiscreteWithin (sphere (0:ℂ) |(1:ℝ)|),
      compl_singleton_mem_codiscreteWithin (s := sphere (0:ℂ) |(1:ℝ)|) rho,
      compl_singleton_mem_codiscreteWithin (s := sphere (0:ℂ) |(1:ℝ)|) (conj rho)] with z hz hzρ hzc
    have hz' : ‖z‖=1 := by simpa [mem_sphere_iff_norm] using hz
    have hzr : z≠rho := by simpa using hzρ
    have hzcr : z≠conj rho := by simpa using hzc
    rw [unit_factor_log hρ hz' hzr hzcr,mul_add]
  rw [hc,circleAverage_fun_add (weighted_boundary_CircleIntegrable rho)
    (weighted_boundary_CircleIntegrable (conj rho)),
    semicircle_weight_boundary_log_moment hρ,
    semicircle_weight_boundary_log_moment (by simpa using hρ : ‖conj rho‖=1),Complex.conj_re]
  ring

/-- The literal semicircle-density logarithmic integral on its entire closed
spectral support, including the two endpoints and every logarithmic singularity. -/
theorem potential_eq_inside (u : ℝ) (hu : |u|≤2) :
    potential u=u^2/4-1/2 := by
  let rho : ℂ := ⟨u/2,Real.sqrt (1-(u/2)^2)⟩
  have hs : 0≤1-(u/2)^2 := by
    have h := abs_le.mp hu
    nlinarith [sq_nonneg (u/2)]
  have hρ : ‖rho‖=1 := by
    rw [Complex.norm_def]
    have he : Complex.normSq rho=1 := by
      simp only [Complex.normSq_apply]
      change (u/2)*(u/2)+Real.sqrt (1-(u/2)^2)*Real.sqrt (1-(u/2)^2)=1
      nlinarith [Real.sq_sqrt hs]
    rw [he,Real.sqrt_one]
  have he := potential_unit_real_part hρ
  have hr : rho.re=u/2 := rfl
  rw [hr,show 2*(u/2)=u by ring] at he
  exact he.trans (by ring)

end
end SlowEquilibration.SemicirclePotential
