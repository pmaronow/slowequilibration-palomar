-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCuspEpsilon
public import SlowEquilibration.RealAnalyticCuspPrimitive

@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter Asymptotics
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal replica-symmetric trial pressure from the source. -/
def cuspTrialPressure (μ : InfiniteMixture) (β r : ℝ) : ℝ :=
  (β ^ 2 * (μ.xi 1 + μ.xi r) + r + Real.log (1 - r)) / 2

namespace CuspCoordinate
variable {μ : InfiniteMixture} (c : CuspCoordinate μ)

def scaledTrial (h r : ℝ) : ℝ :=
  (((1 + c.a * h ^ (2 * c.m)) / μ.Amax) * (μ.xi 1 + μ.xi r) + r +
    Real.log (1 - r)) / 2

def trialBarrier (h : ℝ) : ℝ := c.scaledTrial h (c.rightRoot h) - c.scaledTrial h (c.leftRoot h)

theorem scaledTrial_eq (h r : ℝ) : c.scaledTrial h r = μ.cuspTrialPressure (c.temperature h) r := by
  have he : c.temperature h ^ 2 = (1 + c.a * h ^ (2 * c.m)) / μ.Amax :=
    (eq_div_iff μ.Amax_pos.ne').mpr (c.temperature_sq h)
  rw [scaledTrial,cuspTrialPressure,he]

theorem trialBarrier_eq (h : ℝ) : c.trialBarrier h =
    μ.cuspTrialPressure (c.temperature h) (c.rightRoot h) -
    μ.cuspTrialPressure (c.temperature h) (c.leftRoot h) := by
  rw [trialBarrier,c.scaledTrial_eq,c.scaledTrial_eq]

private theorem qD_interior (c : CuspCoordinate μ) : μ.qD ∈ Ioo (0 : ℝ) 1 := by
  simpa only [c.zero,add_zero] using c.interior 0
    (show (0 : ℝ) ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos])

private theorem rightRoot_analytic : AnalyticAt ℝ c.rightRoot 0 := analyticAt_const.add c.analytic
private theorem leftRoot_analytic : AnalyticAt ℝ c.leftRoot 0 :=
  analyticAt_const.add (c.analytic.comp_of_eq (analyticAt_id.neg : AnalyticAt ℝ (fun x : ℝ => -x) 0) (by simp))

private theorem rootTrial_analytic {R : ℝ → ℝ} (hR : AnalyticAt ℝ R 0) (hR0 : R 0 = μ.qD) :
    AnalyticAt ℝ (fun h => c.scaledTrial h (R h)) 0 := by
  have hi := c.qD_interior
  have hxi : AnalyticAt ℝ μ.xi (R 0) := by
    rw [hR0]
    exact μ.analyticOnNhd_xi _ ⟨by linarith [hi.1],hi.2⟩
  exact ((((analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow (2*c.m)))).div_const).mul
    (analyticAt_const.add (hxi.comp hR))).add hR |>.add
    ((analyticAt_const.sub hR).log (by change 0 < 1 - R 0; rw [hR0]; linarith [hi.2]))).div_const

theorem trialBarrier_analytic : AnalyticAt ℝ c.trialBarrier 0 :=
  (c.rootTrial_analytic c.rightRoot_analytic (by simp [rightRoot,c.zero])).sub
    (c.rootTrial_analytic c.leftRoot_analytic (by simp [leftRoot,c.zero]))

theorem trialBarrier_zero : c.trialBarrier 0 = 0 := by simp [trialBarrier,leftRoot,rightRoot]

private theorem rootTrial_hasDerivAt {R : ℝ → ℝ} {h dR : ℝ}
    (hR : HasDerivAt R dR h) (hi : R h ∈ Ioo (0 : ℝ) 1)
    (hlevel : μ.A (R h) = μ.Amax / (1 + c.a * h ^ (2 * c.m))) :
    HasDerivAt (fun x => c.scaledTrial x (R x))
      ((c.a * (2 * c.m : ℕ) / (2 * μ.Amax)) * h ^ (2 * c.m - 1) * (μ.xi 1 + μ.xi (R h))) h := by
  have hxi := (μ.analyticOnNhd_xi (R h) ⟨by linarith [hi.1],hi.2⟩).differentiableAt.hasDerivAt.comp h hR
  have hlog := ((hasDerivAt_const h (1 : ℝ)).sub hR).log (by linarith [hi.2] : 1 - R h ≠ 0)
  have hb := (((hasDerivAt_id h).pow (2*c.m)).const_mul c.a |>.const_add 1).div_const μ.Amax
  have ht := ((hb.mul (hxi.const_add (μ.xi 1))).add hR |>.add hlog).div_const 2
  have hn : 1 + c.a * h ^ (2*c.m) ≠ 0 := by
    have hp : 0 ≤ h ^ (2*c.m) := by rw [pow_mul]; positivity
    have := c.a_pos
    positivity
  have hstat : ((1 + c.a * h ^ (2*c.m)) / μ.Amax) * deriv μ.xi (R h) = R h / (1 - R h) := by
    rw [μ.A_eq_threshold hi,Thresholds.A] at hlevel
    field_simp [hn,hi.1.ne',μ.Amax_pos.ne',(sub_pos.mpr hi.2).ne'] at hlevel ⊢
    nlinarith [hlevel]
  convert ht using 1
  · rfl
  · simp only [id_eq,Pi.sub_apply,Pi.pow_apply,Function.comp_apply,mul_one]
    have hM := μ.Amax_pos.ne'
    have hr := (sub_pos.mpr hi.2).ne'
    field_simp [hM,hr] at hstat ⊢
    linear_combination -dR * hstat

/-- The moving-endpoint terms cancel because both endpoints are actual level roots. -/
theorem trialBarrier_deriv :
    ∀ᶠ h in 𝓝 (0 : ℝ), deriv c.trialBarrier h =
      (c.a * (2 * c.m : ℕ) / (2 * μ.Amax)) * h ^ (2 * c.m - 1) *
        (μ.xi (c.rightRoot h) - μ.xi (c.leftRoot h)) := by
  have hsmall : ∀ᶠ h in 𝓝 (0 : ℝ), h ∈ Ioo (-c.radius) c.radius :=
    Ioo_mem_nhds (by linarith [c.radius_pos]) c.radius_pos
  filter_upwards [hsmall,c.rightRoot_analytic.eventually_analyticAt,
    c.leftRoot_analytic.eventually_analyticAt] with h hh hR hL
  have hn : -h ∈ Icc (-c.radius) c.radius := by constructor <;> linarith [hh.1,hh.2]
  have hli : c.leftRoot h ∈ Ioo (0 : ℝ) 1 := c.interior (-h) hn
  have hri : c.rightRoot h ∈ Ioo (0 : ℝ) 1 := c.interior h ⟨hh.1.le,hh.2.le⟩
  have hln : μ.A (c.leftRoot h) = μ.Amax / (1 + c.a * h ^ (2*c.m)) := by
    have he := c.normal (-h) hn
    have hp : (-h) ^ (2*c.m) = h ^ (2*c.m) := Even.neg_pow (even_two_mul c.m) h
    simpa only [leftRoot,hp] using he
  have hrn := c.normal h ⟨hh.1.le,hh.2.le⟩
  have hd := (c.rootTrial_hasDerivAt hR.differentiableAt.hasDerivAt hri hrn).sub
    (c.rootTrial_hasDerivAt hL.differentiableAt.hasDerivAt hli hln)
  rw [show deriv c.trialBarrier h = _ from hd.deriv]
  ring

private theorem xi_roots_remainder :
    (fun h : ℝ => μ.xi (c.rightRoot h) - μ.xi (c.leftRoot h) - 2 * deriv μ.xi μ.qD * h)
      =O[𝓝 (0 : ℝ)] (fun h => h ^ 2) := by
  let X : ℝ → ℝ := fun h => μ.xi (c.rightRoot h) - μ.xi (c.leftRoot h)
  have hi := c.qD_interior
  have hxi := μ.analyticOnNhd_xi μ.qD ⟨by linarith [hi.1],hi.2⟩
  have hr0 : c.rightRoot 0 = μ.qD := by simp [rightRoot,c.zero]
  have hl0 : c.leftRoot 0 = μ.qD := by simp [leftRoot,c.zero]
  have ha : AnalyticAt ℝ X 0 :=
    (by simpa only [hr0] using hxi : AnalyticAt ℝ μ.xi (c.rightRoot 0)).comp c.rightRoot_analytic |>.sub
      ((by simpa only [hl0] using hxi : AnalyticAt ℝ μ.xi (c.leftRoot 0)).comp c.leftRoot_analytic)
  have hrD : HasDerivAt c.rightRoot 1 0 := c.derivative.const_add μ.qD
  have hlD : HasDerivAt c.leftRoot (-1) 0 := by
    change HasDerivAt (fun x : ℝ => μ.qD + c.g (-x)) (-1) 0
    have hn : HasDerivAt (fun x : ℝ => -x) (-1) 0 := (hasDerivAt_id 0).neg
    simpa only [leftRoot,Function.comp_def,neg_zero,mul_neg_one] using ((show HasDerivAt c.g 1 (-0) by simpa using c.derivative).comp 0 hn).const_add μ.qD
  have hd : deriv X 0 = 2 * deriv μ.xi μ.qD := by
    have hr := (by simpa only [hr0] using hxi.differentiableAt.hasDerivAt :
      HasDerivAt μ.xi (deriv μ.xi μ.qD) (c.rightRoot 0)).comp 0 hrD
    have hl := (by simpa only [hl0] using hxi.differentiableAt.hasDerivAt :
      HasDerivAt μ.xi (deriv μ.xi μ.qD) (c.leftRoot 0)).comp 0 hlD
    simpa only [X,Function.comp_def,Pi.sub_def,mul_one,mul_neg_one,sub_neg_eq_add,two_mul] using (hr.sub hl).deriv
  simpa only [X,hr0,hl0,sub_self,sub_zero,hd] using
    RealAnalyticCuspPrimitive.analytic_first_order ha

/-- The integrated leading coefficient, first in the analytic root parameter. -/
theorem trialBarrier_remainder :
    (fun h : ℝ => c.trialBarrier h -
      ((2 * c.m : ℕ) * c.a * μ.qD / (((2 * c.m + 1 : ℕ) : ℝ) * (1 - μ.qD))) * h ^ (2 * c.m + 1))
      =O[𝓝 (0 : ℝ)] (fun h => h ^ (2 * c.m + 2)) := by
  have hh := RealAnalyticCuspPrimitive.barrier_from_derivative (by have := c.m_pos; omega : 1 ≤ 2*c.m)
    c.trialBarrier_analytic c.trialBarrier_zero c.xi_roots_remainder c.trialBarrier_deriv
  have hi := c.qD_interior
  have hA : μ.A μ.qD = μ.Amax := by
    have hn := c.normal 0 (show (0 : ℝ) ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos])
    simpa only [c.zero,add_zero,zero_pow (by have := c.m_pos; omega : 2*c.m ≠ 0),mul_zero,add_zero,div_one] using hn
  rw [μ.A_eq_threshold hi,Thresholds.A] at hA
  have he : (c.a * (2 * c.m : ℕ) / (2 * μ.Amax)) * (2 * deriv μ.xi μ.qD) / (2*c.m+1 : ℕ) =
      ((2 * c.m : ℕ) * c.a * μ.qD / (((2 * c.m + 1 : ℕ) : ℝ) * (1 - μ.qD))) := by
    field_simp [hi.1.ne',μ.Amax_pos.ne',(sub_pos.mpr hi.2).ne'] at hA ⊢
    linear_combination c.a * (2 * c.m : ℕ) * hA
  rwa [he] at hh

end CuspCoordinate
end SlowEquilibration.InfiniteMixture
