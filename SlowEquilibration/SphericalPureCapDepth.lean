-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapExteriorNormalized

@[expose] public section

/-! The exact monotone energy-deficit bound of source §9.19. -/

namespace SlowEquilibration.SphericalPureCapDepth
noncomputable section
open Set MeasureTheory PureStationarity SphericalModel
set_option autoImplicit false

/-- Lowering the critical value by `v ≥ 0` decreases the entire raw cap
latitude integral by at least the fixed factor `exp(-β v a^p)`. -/
theorem pure_cap_raw_integral_depth_le
    (p : ℕ) {β a H v : ℝ} (hβ : 0 < β)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hv : 0 ≤ v)
    (N : ℕ) (hN : 4 ≤ N) :
    (∫ t in a..1,
      (1-t^2)^(((N:ℝ)-3)/2) *
        Real.exp (β*(H-v)*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) ≤
      Real.exp (-β*v*a^p) *
        (∫ t in a..1,
          (1-t^2)^(((N:ℝ)-3)/2) *
            Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) := by
  have hpow : 0 ≤ ((N:ℝ)-3)/2 := by
    have : (4:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hpowCont : Continuous (fun t : ℝ => (1-t^2)^(((N:ℝ)-3)/2)) :=
    (Real.continuous_rpow_const hpow).comp
      (continuous_const.sub (continuous_id.pow 2))
  have hresCont : Continuous (pureResidualCoefficient p β) := by
    unfold pureResidualCoefficient pureResidualAtOne
    fun_prop
  have hF : IntervalIntegrable (fun t : ℝ =>
      (1-t^2)^(((N:ℝ)-3)/2) *
        Real.exp (β*(H-v)*t^p+(N:ℝ)*pureResidualCoefficient p β t/2))
      volume a 1 := by
    apply Continuous.intervalIntegrable
    exact hpowCont.mul (Real.continuous_exp.comp (by fun_prop))
  have hG : IntervalIntegrable (fun t : ℝ =>
      (1-t^2)^(((N:ℝ)-3)/2) *
        Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2))
      volume a 1 := by
    apply Continuous.intervalIntegrable
    exact hpowCont.mul (Real.continuous_exp.comp (by fun_prop))
  have hpt : ∀ t ∈ Icc a 1,
      (1-t^2)^(((N:ℝ)-3)/2) *
        Real.exp (β*(H-v)*t^p+(N:ℝ)*pureResidualCoefficient p β t/2) ≤
      Real.exp (-β*v*a^p) *
        ((1-t^2)^(((N:ℝ)-3)/2) *
          Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) := by
    intro t ht
    have htp : a^p ≤ t^p := pow_le_pow_left₀ ha0 ht.1 p
    have hβv : 0 ≤ β*v := mul_nonneg hβ.le hv
    have hExp : Real.exp (β*(H-v)*t^p+(N:ℝ)*pureResidualCoefficient p β t/2) ≤
        Real.exp (-β*v*a^p)*
          Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left htp hβv]
    have hEntropy : 0 ≤ (1-t^2)^(((N:ℝ)-3)/2) := by
      have hbase : 0 ≤ 1-t^2 := by nlinarith [ha0,ht.1,ht.2]
      exact Real.rpow_nonneg hbase _
    calc
      _ ≤ (1-t^2)^(((N:ℝ)-3)/2) *
          (Real.exp (-β*v*a^p)*
            Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) :=
              mul_le_mul_of_nonneg_left hExp hEntropy
      _ = _ := by ring
  have hi := intervalIntegral.integral_mono_on ha1.le hF
    (hG.const_mul (Real.exp (-β*v*a^p))) hpt
  simpa only [intervalIntegral.integral_const_mul] using hi

/-- The same source depth estimate with the literal spherical coarea factor. -/
theorem pure_cap_normalized_integral_depth_le
    (p : ℕ) {β a H v : ℝ} (hβ : 0 < β)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hv : 0 ≤ v)
    (N : ℕ) (hN : 4 ≤ N) :
    (latitudeNormalization (N-1)).toReal *
      (∫ t in a..1,
        (1-t^2)^(((N:ℝ)-3)/2) *
          Real.exp (β*(H-v)*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) ≤
      Real.exp (-β*v*a^p) *
        ((latitudeNormalization (N-1)).toReal *
          (∫ t in a..1,
            (1-t^2)^(((N:ℝ)-3)/2) *
              Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2))) := by
  have hh := pure_cap_raw_integral_depth_le p (H := H) hβ ha0 ha1 hv N hN
  have hnorm : 0 ≤ (latitudeNormalization (N-1)).toReal := ENNReal.toReal_nonneg
  have hmul := mul_le_mul_of_nonneg_left hh hnorm
  convert hmul using 1
  ring

end
end SlowEquilibration.SphericalPureCapDepth
