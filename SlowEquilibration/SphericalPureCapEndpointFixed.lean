-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapEndpointIntegral

/-! A near-pole cutoff chosen once for all bounded energy-shift windows.
The shift `L` enters the raw exponent additively, so only the dimension
threshold depends on `L`. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapEndpointFixed
noncomputable section
open Filter Set MeasureTheory PureStationarity
open SphericalPureCapEndpointIntegral
open scoped Topology
set_option autoImplicit false

/-- The near-pole raw integral has an additive `βL` energy-window cost. -/
theorem pure_cap_endpoint_raw_integral_additive_le
    (p : ℕ) (hp : 4 ≤ p) {β e L H ε : ℝ}
    (hβ : 0 < β) (hH0 : 0 ≤ H)
    (N : ℕ) (hN : 4 ≤ N) (hH : H ≤ (N:ℝ)*e+L)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∫ t in (1-ε)..1,
      (1-t^2)^(((N:ℝ)-3)/2) *
        Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) ≤
      ε*(2*ε)^(((N:ℝ)-3)/2)*
        Real.exp ((N:ℝ)*(β*e+β^2/2)+β*L) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hH' : H ≤ (N:ℝ)*(e+L/(N:ℝ)) := by
    apply hH.trans
    have hN0 : (N:ℝ) ≠ 0 := hNr.ne'
    field_simp
    exact le_refl _
  have hH'' : H ≤ (N:ℝ)*(e+L/(N:ℝ))+0 := by simpa using hH'
  have hh := pure_cap_endpoint_raw_integral_le p hp hβ
    (e:=e+L/(N:ℝ)) (L:=0)
    (show 0 ≤ (0:ℝ) by norm_num) hH0 N hN hH'' hε0 hε1
  convert hh using 1
  congr 1
  congr 1
  have hN0 : (N:ℝ) ≠ 0 := hNr.ne'
  field_simp
  ring

/-- The endpoint cutoff is independent of `L`; only the eventual dimension
threshold changes as the energy window widens. -/
theorem exists_pure_cap_endpoint_fixed_epsilon
    (p : ℕ) (hp : 4 ≤ p) {β e a F : ℝ}
    (hβ : 0 < β) (ha : a ∈ Ico (0:ℝ) 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ a < 1-ε ∧
      ∀ L : ℝ, 0 ≤ L → ∃ N₀ : ℕ, ∀ N ≥ N₀, 4 ≤ N → ∀ H : ℝ,
        0 ≤ H → H ≤ (N:ℝ)*e+L →
        (∫ t in (1-ε)..1,
          (1-t^2)^(((N:ℝ)-3)/2) *
            Real.exp (β*H*t^p+(N:ℝ)*pureResidualCoefficient p β t/2)) ≤
          Real.exp ((N:ℝ)*(F-1)) := by
  let B := β*e+β^2/2
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
    have hh := min_le_right ((1-a)/4) (d/4)
    dsimp [ε]
    linarith
  have hlog : Real.log (2*ε) < 2*(F-B-2) := by
    have hh := Real.log_lt_log hz0 hzd
    dsimp [d] at hh
    rwa [Real.log_exp] at hh
  have hεlog : Real.log ε ≤ 0 := Real.log_nonpos hε0.le hε1.le
  refine ⟨ε,hε0,hε1,haε,?_⟩
  intro L hL
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (β*L-(3/2:ℝ)*Real.log (2*ε))
  refine ⟨N₀,?_⟩
  intro N hNN₀ hN H hH0 hH
  have hraw := pure_cap_endpoint_raw_integral_additive_le p hp hβ hH0
    N hN hH hε0 hε1
  apply hraw.trans
  have hrepr : ε*(2*ε)^(((N:ℝ)-3)/2)*
      Real.exp ((N:ℝ)*B+β*L) =
      Real.exp (Real.log ε+Real.log (2*ε)*(((N:ℝ)-3)/2)+
        ((N:ℝ)*B+β*L)) := by
    rw [Real.rpow_def_of_pos hz0]
    calc
      ε*Real.exp (Real.log (2*ε)*(((N:ℝ)-3)/2))*
          Real.exp ((N:ℝ)*B+β*L) =
        Real.exp (Real.log ε)*Real.exp (Real.log (2*ε)*(((N:ℝ)-3)/2))*
          Real.exp ((N:ℝ)*B+β*L) := by rw [Real.exp_log hε0]
      _ = _ := by simp only [Real.exp_add,mul_assoc]
  rw [hrepr]
  apply Real.exp_le_exp.mpr
  have hNr : (0:ℝ) ≤ N := by positivity
  have hN₀r : (N₀:ℝ) ≤ N := by exact_mod_cast hNN₀
  have hcount : β*L-(3/2:ℝ)*Real.log (2*ε) ≤ (N:ℝ) :=
    (le_of_lt hN₀).trans hN₀r
  have hmul := mul_le_mul_of_nonneg_left hlog.le (show 0 ≤ (N:ℝ)/2 by positivity)
  dsimp [B] at *
  nlinarith [hmul]

end
end SlowEquilibration.SphericalPureCapEndpointFixed
