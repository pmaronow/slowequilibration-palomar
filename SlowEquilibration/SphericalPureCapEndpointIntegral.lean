-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapAwayGap
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! The entropy power controls the pole of the pure latitude integral. -/

namespace SlowEquilibration.SphericalPureCapEndpointIntegral
noncomputable section
open Set MeasureTheory
open PureStationarity
set_option autoImplicit false

/-- On a fixed pole interval the raw spherical entropy factor has the
exponentially small bound used in the source §9.19 endpoint argument. -/
theorem endpoint_entropy_integral_le
    (N : ℕ) (hN : 4 ≤ N) {ε B : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (g : ℝ → ℝ)
    (hgcont : ContinuousOn g (Icc (1-ε) 1))
    (hg : ∀ t ∈ Icc (1-ε) 1, g t ≤ B) :
    (∫ t in (1-ε)..1,
      (1-t^2)^(((N:ℝ)-3)/2) * Real.exp ((N:ℝ)*g t)) ≤
        ε*(2*ε)^(((N:ℝ)-3)/2)*Real.exp ((N:ℝ)*B) := by
  have hpow : 0 ≤ ((N:ℝ)-3)/2 := by
    have : (4:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hcontPow : Continuous (fun t : ℝ => (1-t^2)^(((N:ℝ)-3)/2)) :=
    (Real.continuous_rpow_const hpow).comp (continuous_const.sub (continuous_id.pow 2))
  have hcontExp : ContinuousOn (fun t : ℝ => Real.exp ((N:ℝ)*g t)) (Icc (1-ε) 1) :=
    Real.continuous_exp.comp_continuousOn (continuous_const.continuousOn.mul hgcont)
  have hint : IntervalIntegrable
      (fun t : ℝ => (1-t^2)^(((N:ℝ)-3)/2)*Real.exp ((N:ℝ)*g t))
      volume (1-ε) 1 :=
    (hcontPow.continuousOn.mul hcontExp).intervalIntegrable_of_Icc (by linarith)
  have hpt : ∀ t ∈ Icc (1-ε) 1,
      (1-t^2)^(((N:ℝ)-3)/2)*Real.exp ((N:ℝ)*g t) ≤
        (2*ε)^(((N:ℝ)-3)/2)*Real.exp ((N:ℝ)*B) := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    have hbase0 : 0 ≤ 1-t^2 := by nlinarith [ht.2]
    have hbase : 1-t^2 ≤ 2*ε := by
      calc
        1-t^2 = (1-t)*(1+t) := by ring
        _ ≤ ε*2 := by
          apply mul_le_mul
          · linarith [ht.1]
          · linarith [ht.2]
          · linarith [ht0]
          · linarith [ht.2]
        _ = 2*ε := by ring
    have hpowle := Real.rpow_le_rpow hbase0 hbase hpow
    have hN0 : (0:ℝ) ≤ N := by positivity
    have hexp : Real.exp ((N:ℝ)*g t) ≤ Real.exp ((N:ℝ)*B) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hg t ht) hN0)
    exact mul_le_mul hpowle hexp (Real.exp_pos _).le
      (Real.rpow_nonneg (by positivity : 0 ≤ 2*ε) _)
  have hbound := intervalIntegral.integral_mono_on (by linarith : 1-ε ≤ (1:ℝ))
    hint (intervalIntegrable_const) hpt
  calc
    _ ≤ ∫ t in (1-ε)..1,
        (2*ε)^(((N:ℝ)-3)/2)*Real.exp ((N:ℝ)*B) := hbound
    _ = ε*(2*ε)^(((N:ℝ)-3)/2)*Real.exp ((N:ℝ)*B) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring

/-- On the physical latitude interval the pure conditional covariance never
exceeds its full variance `β²`. -/
theorem pureResidualCoefficient_le_beta_sq
    (p : ℕ) (hp : 4 ≤ p) (β : ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    pureResidualCoefficient p β t ≤ β^2 := by
  rw [pureResidualCoefficient_eq p (by omega : 2 ≤ p)]
  have hp0 : (0:ℝ) ≤ p := by positivity
  have hsq : 0 ≤ 1-t^2 := by nlinarith [ht.1,ht.2]
  have hremain : 0 ≤ t^(2*p)+(p:ℝ)*t^(2*p-2)*(1-t^2) :=
    add_nonneg (pow_nonneg ht.1 _) (mul_nonneg
      (mul_nonneg hp0 (pow_nonneg ht.1 _)) hsq)
  nlinarith [mul_nonneg (sq_nonneg β) hremain]

/-- An actual pure conditional mean has an exponentially small raw pole
integral whenever its critical value is at most `N e + L`. -/
theorem pure_cap_endpoint_raw_integral_le
    (p : ℕ) (hp : 4 ≤ p) {β e L H ε : ℝ}
    (hβ : 0 < β) (hL : 0 ≤ L) (hH0 : 0 ≤ H)
    (N : ℕ) (hN : 4 ≤ N) (hH : H ≤ (N:ℝ)*e+L)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∫ t in (1-ε)..1,
      (1-t^2)^(((N:ℝ)-3)/2) *
        Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) ≤
      ε*(2*ε)^(((N:ℝ)-3)/2)*
        Real.exp ((N:ℝ)*(β*e+β^2/2+β*L)) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let g : ℝ → ℝ := fun t => (β*H/(N:ℝ))*t^p+pureResidualCoefficient p β t/2
  have hgcont : ContinuousOn g (Icc (1-ε) 1) := by
    unfold g pureResidualCoefficient pureResidualAtOne
    fun_prop
  have hg : ∀ t ∈ Icc (1-ε) 1, g t ≤ β*e+β^2/2+β*L := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht.1],ht.2⟩
    have htp : t^p ≤ 1 := pow_le_one₀ ht'.1 ht'.2
    have hC := pureResidualCoefficient_le_beta_sq p hp β ht'
    have hNH : β*H*t^p ≤ β*H := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left htp (mul_nonneg hβ.le hH0)
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hβL : β*L ≤ (N:ℝ)*(β*L) := by
      nlinarith [mul_nonneg hβ.le hL]
    have hmain : (β*H*t^p)/(N:ℝ) ≤ β*e+β*L := by
      apply (div_le_iff₀ hNr).mpr
      nlinarith [mul_le_mul_of_nonneg_left hH hβ.le, hNH, hβL]
    dsimp [g]
    calc
      β*H/(N:ℝ)*t^p+pureResidualCoefficient p β t/2 =
          (β*H*t^p)/(N:ℝ)+pureResidualCoefficient p β t/2 := by ring
      _ ≤ β*e+β*L+β^2/2 := add_le_add hmain (by linarith [hC])
      _ = β*e+β^2/2+β*L := by ring
  have hraw := endpoint_entropy_integral_le N hN hε0 hε1 g hgcont hg
  convert hraw using 1
  · congr 1
    ext t
    congr 1
    dsimp [g]
    field_simp [hNr.ne']

/-- Choose the pole cutoff beyond any prescribed interior latitude. For all
large dimensions, its raw conditional-mean integral is exponentially below
any prescribed reference free-energy exponent. -/
theorem exists_pure_cap_endpoint_exponential_bound
    (p : ℕ) (hp : 4 ≤ p) {β e L a F : ℝ}
    (hβ : 0 < β) (hL : 0 ≤ L) (ha : a ∈ Ico (0:ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ a < 1-ε ∧
      ∃ N₀ : ℕ, ∀ N ≥ N₀, 4 ≤ N → ∀ H : ℝ,
        0 ≤ H → H ≤ (N:ℝ)*e+L →
        (∫ t in (1-ε)..1,
          (1-t^2)^(((N:ℝ)-3)/2) *
            Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) ≤
          Real.exp ((N:ℝ)*(F-1)) := by
  let B := β*e+β^2/2+β*L
  let d := Real.exp (2*(F-B-2))
  let ε := min ((1-a)/4) (d/4)
  have hd0 : 0 < d := Real.exp_pos _
  have hε0 : 0 < ε := by dsimp [ε]; exact lt_min (by linarith [ha.2]) (by positivity)
  have hε1 : ε < 1 := by
    calc ε ≤ (1-a)/4 := min_le_left _ _
      _ < 1 := by linarith [ha.1]
  have haε : a < 1-ε := by
    have hh : ε ≤ (1-a)/4 := min_le_left _ _
    linarith [ha.2]
  have hz0 : 0 < 2*ε := by positivity
  have hz1 : 2*ε < 1 := by
    have hh : ε ≤ (1-a)/4 := min_le_left _ _
    linarith [ha.1,ha.2]
  have hzd : 2*ε < d := by
    have hh : ε ≤ d/4 := min_le_right _ _
    linarith
  have hlog : Real.log (2*ε) < 2*(F-B-2) := by
    have hh := Real.log_lt_log hz0 hzd
    dsimp [d] at hh
    rwa [Real.log_exp] at hh
  have hεlog : Real.log ε ≤ 0 := Real.log_nonpos hε0.le hε1.le
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (-(3/2:ℝ)*Real.log (2*ε))
  refine ⟨ε,hε0,hε1,haε,N₀,?_⟩
  intro N hNN₀ hN H hH0 hH
  have hraw := pure_cap_endpoint_raw_integral_le p hp hβ hL hH0 N hN hH hε0 hε1
  apply hraw.trans
  have hrepr : ε*(2*ε)^(((N:ℝ)-3)/2)*Real.exp ((N:ℝ)*B) =
      Real.exp (Real.log ε+Real.log (2*ε)*(((N:ℝ)-3)/2)+(N:ℝ)*B) := by
    rw [Real.rpow_def_of_pos hz0,Real.exp_add,Real.exp_add,Real.exp_log hε0]
  rw [hrepr]
  apply Real.exp_le_exp.mpr
  have hNr : (0:ℝ) ≤ N := by positivity
  have hN₀r : (N₀:ℝ) ≤ N := by exact_mod_cast hNN₀
  have hcount : -(3/2:ℝ)*Real.log (2*ε) ≤ (N:ℝ) :=
    (le_of_lt hN₀).trans hN₀r
  have hmul := mul_le_mul_of_nonneg_left hlog.le (show 0 ≤ (N:ℝ)/2 by positivity)
  dsimp [B] at *
  nlinarith [hmul]

end
end SlowEquilibration.SphericalPureCapEndpointIntegral
