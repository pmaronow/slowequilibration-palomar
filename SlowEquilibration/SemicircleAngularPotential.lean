-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemicircleWholeLine
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Genuine angular transport of the actual semicircle logarithmic integral. -/

@[expose] public section
namespace SlowEquilibration.SemicircleAngularPotential

noncomputable section
open MeasureTheory Set Function Filter Real Complex Metric
open SemicirclePotential SemicircleWholeLine
open scoped Topology Interval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma density_two_cos {theta : ℝ} (ht : theta ∈ Icc (0:ℝ) Real.pi) :
    density (2*Real.cos theta)=Real.sin theta/Real.pi := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2
  have he : 4-(2*Real.cos theta)^2=(2*Real.sin theta)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq theta]
  rw [density,he,Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 2*Real.sin theta)]
  field_simp

/-- True scalar change of variables under the decreasing cosine chart,
valid despite the logarithmic singularity of the integrand. -/
theorem potential_eq_sine_integral (z : ℝ) :
    potential z=(2/Real.pi)*∫ theta in (0:ℝ)..Real.pi,
      Real.sin theta^2*Real.log |z-2*Real.cos theta| := by
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (a := (0:ℝ)) (b := Real.pi) (f := fun theta => 2*Real.cos theta)
    (f' := fun theta => -2*Real.sin theta) (g := fun t => density t*Real.log |z-t|)
    (by fun_prop) (fun theta ht => by
      convert (Real.hasDerivAt_cos theta).const_mul 2 using 1
      ring)
    (fun theta ht => by
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi
        (by simpa only [min_eq_left Real.pi_pos.le] using ht.1.le)
        (by simpa only [max_eq_right Real.pi_pos.le] using ht.2.le)
      linarith)
  have hin : (∫ theta in (0:ℝ)..Real.pi,
      ((fun t => density t*Real.log |z-t|) ∘ (fun theta => 2*Real.cos theta)) theta *
        (-2*Real.sin theta))=
      (-2/Real.pi)*∫ theta in (0:ℝ)..Real.pi,Real.sin theta^2*Real.log |z-2*Real.cos theta| := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro theta ht
    have ht' : theta ∈ Icc (0:ℝ) Real.pi := by
      have hmin : min (0:ℝ) Real.pi=0 := min_eq_left Real.pi_pos.le
      have hmax : max (0:ℝ) Real.pi=Real.pi := max_eq_right Real.pi_pos.le
      exact ⟨hmin ▸ ht.1,hmax ▸ ht.2⟩
    simp only [Function.comp_apply,density_two_cos ht']
    ring
  rw [hin] at hsub
  simp only [Real.cos_zero,Real.cos_pi,mul_one,mul_neg,mul_one] at hsub
  rw [intervalIntegral.integral_symm (a := (-2:ℝ)) (b := (2:ℝ))] at hsub
  have hp : (∫ t in (-2:ℝ)..2,density t*Real.log |z-t|)=potential z := by
    rw [potential,integral_law_interval]
  rw [hp] at hsub
  have he : (-2:ℝ)/Real.pi=-(2/Real.pi) := by ring
  rw [he,neg_mul] at hsub
  linarith

lemma angular_log_intervalIntegrable (z a b : ℝ) :
    IntervalIntegrable (fun theta => Real.log |z-2*Real.cos theta|) volume a b := by
  have hM : MeromorphicOn (fun theta : ℝ => z-2*Real.cos theta) (uIcc a b) := by
    intro theta ht
    fun_prop
  simpa only [Real.log_abs,Function.comp_def] using hM.intervalIntegrable_log

lemma sine_weighted_intervalIntegrable (z a b : ℝ) :
    IntervalIntegrable (fun theta => Real.sin theta^2*Real.log |z-2*Real.cos theta|) volume a b := by
  exact (angular_log_intervalIntegrable z a b).continuousOn_mul (by fun_prop)

/-- True angular expression over the full circle, with its literal quadratic
angular weight, ready for the boundary logarithm moment calculation. -/
theorem potential_eq_circle_weighted_integral (z : ℝ) :
    potential z=(2*Real.pi)⁻¹*∫ theta in (0:ℝ)..(2*Real.pi),
      (1-Real.cos (2*theta))*Real.log |z-2*Real.cos theta| := by
  let f := fun theta : ℝ => Real.sin theta^2*Real.log |z-2*Real.cos theta|
  have hsym : (∫ theta in Real.pi..(2*Real.pi),f theta)=∫ theta in (0:ℝ)..Real.pi,f theta := by
    have he : (∫ theta in Real.pi..(2*Real.pi),f (2*Real.pi-theta))=
        ∫ theta in (0:ℝ)..Real.pi,f theta := by
      simpa only [sub_self,show 2*Real.pi-Real.pi=Real.pi by ring] using
        intervalIntegral.integral_comp_sub_left f (2*Real.pi) (a := Real.pi) (b := 2*Real.pi)
    rw [← he]
    apply intervalIntegral.integral_congr
    intro theta ht
    dsimp only [f]
    rw [Real.sin_two_pi_sub,Real.cos_two_pi_sub,neg_sq]
  have hfull : (∫ theta in (0:ℝ)..(2*Real.pi),f theta)=2*∫ theta in (0:ℝ)..Real.pi,f theta := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (sine_weighted_intervalIntegrable z 0 Real.pi) (sine_weighted_intervalIntegrable z Real.pi (2*Real.pi)),hsym]
    ring
  have htrig (theta : ℝ) : 1-Real.cos (2*theta)=2*Real.sin theta^2 := by
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq theta]
  simp_rw [htrig,mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  change potential z=(2*Real.pi)⁻¹*(2*∫ theta in (0:ℝ)..(2*Real.pi),f theta)
  rw [hfull,potential_eq_sine_integral]
  dsimp only [f]
  field_simp

end
end SlowEquilibration.SemicircleAngularPotential
