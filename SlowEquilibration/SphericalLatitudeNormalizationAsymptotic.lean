-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeNormalization
public import Mathlib.Analysis.SpecialFunctions.Stirling

@[expose] public section

/-! The exact coarea Gamma ratio has the sharp square-root normalization
needed by microscopic latitude Laplace estimates. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open Filter
open scoped Topology
set_option autoImplicit false

theorem gamma_half_ratio_lower {x : ℝ} (hx : 0 < x) :
    x*Real.Gamma x ≤ Real.sqrt (x+1/2)*Real.Gamma (x+1/2) := by
  have h := gamma_half_ratio_le_sqrt (show 0 < x+1/2 by linarith)
  have hstep : x+1/2+1/2=x+1 := by ring
  rw [hstep,Real.Gamma_add_one hx.ne'] at h
  exact h

/-- Gautschi's half-step Gamma bounds in a form whose endpoints both tend to
one after dividing by `sqrt x`. -/
theorem gamma_half_ratio_unit_bounds {x : ℝ} (hx : 0 < x) :
    x/(x+1/2) ≤
      Real.Gamma (x+1/2)/(Real.sqrt x*Real.Gamma x) ∧
      Real.Gamma (x+1/2)/(Real.sqrt x*Real.Gamma x) ≤ 1 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have ht : 0 < Real.sqrt (x+1/2) := Real.sqrt_pos.mpr (by linarith)
  have hg : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hA : 0 < Real.Gamma (x+1/2) := Real.Gamma_pos_of_pos (by linarith)
  have hu := gamma_half_ratio_le_sqrt hx
  have hl := gamma_half_ratio_lower hx
  have hst : Real.sqrt x ≤ Real.sqrt (x+1/2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hst
    (mul_nonneg ht.le hA.le)
  have hsquare : (Real.sqrt (x+1/2))^2=x+1/2 :=
    Real.sq_sqrt (by linarith)
  have hcross : x*(Real.sqrt x*Real.Gamma x) ≤
      Real.Gamma (x+1/2)*(x+1/2) := by
    have hh := mul_le_mul_of_nonneg_right hl hs.le
    nlinarith [hmul,hh,hsquare]
  constructor
  · exact (div_le_div_iff₀ (by linarith : 0 < x+1/2)
      (mul_pos hs hg)).mpr hcross
  · exact (div_le_iff₀ (mul_pos hs hg)).mpr (by simpa using hu)

theorem gamma_half_ratio_unit_tendsto :
    Tendsto (fun n : ℕ =>
      Real.Gamma ((n:ℝ)/2+1/2)/
        (Real.sqrt ((n:ℝ)/2)*Real.Gamma ((n:ℝ)/2)))
      atTop (𝓝 (1:ℝ)) := by
  have hlow : Tendsto (fun n : ℕ => (n:ℝ)/((n:ℝ)+1))
      atTop (𝓝 (1:ℝ)) := by
    have hrewrite : (fun n : ℕ => (n:ℝ)/((n:ℝ)+1)) =
        (fun n : ℕ => 1-1/((n:ℝ)+1)) := by
      funext n
      have hn : (n:ℝ)+1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hrewrite]
    simpa using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hbounds : ∀ᶠ n : ℕ in atTop,
      (n:ℝ)/((n:ℝ)+1) ≤
        Real.Gamma ((n:ℝ)/2+1/2)/
          (Real.sqrt ((n:ℝ)/2)*Real.Gamma ((n:ℝ)/2)) ∧
        Real.Gamma ((n:ℝ)/2+1/2)/
          (Real.sqrt ((n:ℝ)/2)*Real.Gamma ((n:ℝ)/2)) ≤ 1 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnreal : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hx : 0 < (n:ℝ)/2 := by positivity
    have h := gamma_half_ratio_unit_bounds hx
    have heq : ((n:ℝ)/2)/((n:ℝ)/2+1/2) =
        (n:ℝ)/((n:ℝ)+1) := by
      have hN : (n:ℝ)+1 ≠ 0 := by positivity
      field_simp
    simpa only [heq] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow
    tendsto_const_nhds
    (hbounds.mono fun _ hn => hn.1)
    (hbounds.mono fun _ hn => hn.2)

private theorem sqrt_half_over_latitude_dimension (n : ℕ) :
    Real.sqrt ((n:ℝ)/2)/
        (Real.sqrt Real.pi*Real.sqrt (((n+1:ℕ):ℝ))) =
      Real.sqrt ((n:ℝ)/(((n+1:ℕ):ℝ)))/
        Real.sqrt (2*Real.pi) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hN : 0 < (((n+1:ℕ):ℝ)) := by positivity
  have hn : 0 ≤ (n:ℝ) := by positivity
  have hl : 0 ≤ Real.sqrt ((n:ℝ)/2)/
      (Real.sqrt Real.pi*Real.sqrt (((n+1:ℕ):ℝ))) := by positivity
  have hr : 0 ≤ Real.sqrt ((n:ℝ)/(((n+1:ℕ):ℝ)))/
      Real.sqrt (2*Real.pi) := by positivity
  have hsq :
      (Real.sqrt ((n:ℝ)/2)/
        (Real.sqrt Real.pi*Real.sqrt (((n+1:ℕ):ℝ))))^2 =
      (Real.sqrt ((n:ℝ)/(((n+1:ℕ):ℝ)))/
        Real.sqrt (2*Real.pi))^2 := by
    rw [div_pow,div_pow,mul_pow,
      Real.sq_sqrt (by positivity : 0 ≤ (n:ℝ)/2),
      Real.sq_sqrt hπ.le,Real.sq_sqrt hN.le,
      Real.sq_sqrt (div_nonneg hn hN.le),
      Real.sq_sqrt (by positivity : 0 ≤ 2*Real.pi)]
    field_simp
  nlinarith

private theorem sqrt_half_over_latitude_dimension_tendsto :
    Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)/2)/
      (Real.sqrt Real.pi*Real.sqrt (((n+1:ℕ):ℝ))))
      atTop (𝓝 (1/Real.sqrt (2*Real.pi))) := by
  have hratio : Tendsto (fun n : ℕ => (n:ℝ)/((n:ℝ)+1))
      atTop (𝓝 (1:ℝ)) := by
    have hrewrite : (fun n : ℕ => (n:ℝ)/((n:ℝ)+1)) =
        (fun n : ℕ => 1-1/((n:ℝ)+1)) := by
      funext n
      have hn : (n:ℝ)+1 ≠ 0 := by positivity
      field_simp
      ring
    rw [hrewrite]
    simpa using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hroot : Tendsto (fun n : ℕ => Real.sqrt ((n:ℝ)/((n:ℝ)+1)))
      atTop (𝓝 (1:ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto (1:ℝ)).comp hratio
  have h := hroot.div_const (Real.sqrt (2*Real.pi))
  have heq : (fun n : ℕ => Real.sqrt ((n:ℝ)/((n:ℝ)+1)) /
      Real.sqrt (2*Real.pi)) =
      (fun n : ℕ => Real.sqrt ((n:ℝ)/2)/
        (Real.sqrt Real.pi*Real.sqrt (((n+1:ℕ):ℝ)))) := by
    funext n
    simpa only [Nat.cast_add,Nat.cast_one] using
      (sqrt_half_over_latitude_dimension n).symm
  rw [←heq]
  simpa only [one_div] using h

/-- Sharp asymptotic for the genuine spherical coarea density, with ambient
dimension `n+1` and latitude dimension `n`. -/
theorem latitudeNormalization_toReal_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => (latitudeNormalization n).toReal /
      Real.sqrt (((n+1:ℕ):ℝ))) atTop
      (𝓝 (1/Real.sqrt (2*Real.pi))) := by
  have hfactor : ∀ n : ℕ, 1 ≤ n →
      (latitudeNormalization n).toReal /
          Real.sqrt (((n+1:ℕ):ℝ)) =
        (Real.Gamma ((n:ℝ)/2+1/2)/
          (Real.sqrt ((n:ℝ)/2)*Real.Gamma ((n:ℝ)/2))) *
        (Real.sqrt ((n:ℝ)/2)/
          (Real.sqrt Real.pi*Real.sqrt (((n+1:ℕ):ℝ)))) := by
    intro n hn
    have hnreal : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hx : 0 < (n:ℝ)/2 := by positivity
    have hs : Real.sqrt ((n:ℝ)/2) ≠ 0 :=
      (Real.sqrt_pos.mpr hx).ne'
    have hg : Real.Gamma ((n:ℝ)/2) ≠ 0 :=
      (Real.Gamma_pos_of_pos hx).ne'
    have hp : Real.sqrt Real.pi ≠ 0 :=
      (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hN : Real.sqrt (((n+1:ℕ):ℝ)) ≠ 0 := by positivity
    rw [latitudeNormalization_toReal hn]
    have hcast : (((n+1:ℕ):ℝ))/2=(n:ℝ)/2+1/2 := by
      push_cast
      ring
    rw [hcast]
    field_simp
  have heq : (fun n : ℕ => (latitudeNormalization n).toReal /
      Real.sqrt (((n+1:ℕ):ℝ))) =ᶠ[atTop]
      (fun n : ℕ =>
        (Real.Gamma ((n:ℝ)/2+1/2)/
          (Real.sqrt ((n:ℝ)/2)*Real.Gamma ((n:ℝ)/2))) *
        (Real.sqrt ((n:ℝ)/2)/
          (Real.sqrt Real.pi*Real.sqrt (((n+1:ℕ):ℝ))))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact hfactor n hn
  have h := gamma_half_ratio_unit_tendsto.mul
    sqrt_half_over_latitude_dimension_tendsto
  simpa only [one_mul] using h.congr' heq.symm

end
end SlowEquilibration.SphericalModel
