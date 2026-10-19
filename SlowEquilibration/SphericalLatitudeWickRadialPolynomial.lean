-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeTensorMoments

/-! True radial polynomial factors in the physical latitude Wick expansion.
All coefficients retain the genuine Gaussian radial moment. Their weighted
derivatives have dimension-independent bounds, before contraction with the
actual original tensor. -/

@[expose] public section
namespace SlowEquilibration.SphericalLatitudeTensorMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalUniformWickMoments
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeEvenWickCoefficient (n j : ℕ) : ℝ :=
  ((n+1 : ℕ) : ℝ)^j/gaussianNormMoment n (2*j)

/-- The literal even latitude coefficient is its r-independent actual
radial coefficient times the exact physical polynomial (1-r²)^j. -/
theorem latitudeWickCoefficient_even_eq {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : |r| ≤ 1) (j : ℕ) :
    latitudeWickCoefficient n r (2*j)=latitudeEvenWickCoefficient n j*(1-r^2)^j := by
  have hnr : (n : ℝ)≠0 := (Nat.cast_pos.mpr (by omega : 0 < n)).ne'
  have hm : gaussianNormMoment n (2*j)≠0 := (gaussianNormMoment_pos hn (2*j)).ne'
  have hs : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
  have hscale : (latitudeScale n r)^(2*j)=
      (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))^j := by
    rw [pow_mul,latitudeScale,Real.sq_sqrt (by positivity)]
  have hsphere : (Real.sqrt n)^(2*j)=(n : ℝ)^j := by
    rw [pow_mul,Real.sq_sqrt (Nat.cast_nonneg n)]
  unfold latitudeWickCoefficient sphereWickCoefficient latitudeEvenWickCoefficient
  rw [hscale,hsphere,mul_pow,div_pow]
  field_simp [hnr,hm]

/-- The actual coefficient remains uniformly controlled, with n+1/n kept. -/
theorem latitudeEvenWickCoefficient_mem {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    latitudeEvenWickCoefficient n j∈Icc 0 (2^j) := by
  have h := latitudeWickCoefficient_even_mem hn (r := 0) (by norm_num) j
  rw [latitudeWickCoefficient_even_eq hn (by norm_num : |(0 : ℝ)| ≤ 1) j] at h
  simpa only [zero_pow (by norm_num : 2≠0),sub_zero,one_pow,mul_one] using h

def radialWickMonomial (q j : ℕ) (r : ℝ) : ℝ := r^q*(1-r^2)^j

theorem radialWickMonomial_hasDerivAt (q j : ℕ) (r : ℝ) :
    HasDerivAt (radialWickMonomial q j)
      ((q : ℝ)*r^(q-1)*(1-r^2)^j-2*(j : ℝ)*r^(q+1)*(1-r^2)^(j-1)) r := by
  have h := ((hasDerivAt_id r).pow q).mul (((hasDerivAt_id r).pow 2).const_sub 1 |>.pow j)
  have hf : (id^q*(fun t : ℝ => 1-(id^2) t)^j)=radialWickMonomial q j := by
    funext t
    rfl
  rw [hf] at h
  simp only [Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] at h
  apply h.congr_deriv
  simp only [pow_succ]
  ring

/-- Multiplication by the spherical radial velocity cancels the possible
endpoint singularity, leaving the exact bounded polynomial derivative. -/
theorem weighted_radialWickMonomial_derivative (q j : ℕ) (r : ℝ) :
    (1-r^2)*deriv (radialWickMonomial q j) r=
      (q : ℝ)*r^(q-1)*(1-r^2)^(j+1)-2*(j : ℝ)*r^(q+1)*(1-r^2)^j := by
  rw [(radialWickMonomial_hasDerivAt q j r).deriv]
  by_cases hj : j=0
  · subst j
    simp
    ring
  · have he : j-1+1=j := by omega
    have hp : (1-r^2)*(1-r^2)^(j-1)=(1-r^2)^j := by rw [←pow_succ',he]
    rw [show (1-r^2)^(j+1)=(1-r^2)^j*(1-r^2) from pow_succ _ _]
    linear_combination (-2*(j : ℝ)*r^(q+1))*hp

/-- Every correction factor has a bound depending only on fixed degree. -/
theorem weighted_radialWickMonomial_derivative_abs_le (q j : ℕ) {r : ℝ}
    (hr : |r| ≤ 1) : |(1-r^2)*deriv (radialWickMonomial q j) r| ≤ (q : ℝ)+2*j := by
  have hs : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
  have hs1 : 1-r^2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hpow (k : ℕ) : |r^k| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg r) hr
  have hspow (k : ℕ) : |(1-r^2)^k| ≤ 1 := by
    rw [abs_of_nonneg (pow_nonneg hs k)]
    exact pow_le_one₀ hs hs1
  rw [weighted_radialWickMonomial_derivative]
  apply (abs_sub _ _).trans
  have hfirst : |(q : ℝ)*r^(q-1)*(1-r^2)^(j+1)| ≤ (q : ℝ) := by
    rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg q)]
    calc
      _ ≤ (q : ℝ)*1*1 := by
        gcongr
        · exact hpow _
        · exact hspow _
      _ = _ := by ring
  have hsecond : |2*(j : ℝ)*r^(q+1)*(1-r^2)^j| ≤ 2*(j : ℝ) := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg (Nat.cast_nonneg j)]
    calc
      _ ≤ 2*(j : ℝ)*1*1 := by
        gcongr
        · exact hpow _
        · exact hspow _
      _ = _ := by ring
  exact add_le_add hfirst hsecond

end
end SlowEquilibration.SphericalLatitudeTensorMoments
