-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeProbeGeometry

@[expose] public section

/-! # Uniform localization error for the two actual physical probes

The degree-one and degree-two kernels are finite polynomials of three
ordinary overlaps. Their explicit uniform errors are controlled by the
two replicas' physical latitude deviations, including at the poles.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set SphericalModel
open scoped Topology
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem abs_pow_sub_pow_le_unit {a b : ℝ} (ha : |a|≤1) (hb : |b|≤1) (d : ℕ) :
    |a^d-b^d|≤(d : ℝ)*|a-b| := by
  have h := abs_pow_sub_pow_le (a := a) (b := b) (n := d)
  have hp := pow_le_one₀ (le_max_of_le_left (abs_nonneg a)) (max_le ha hb) (n := d-1)
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0≤|a-b| *(d : ℝ))
  exact h.trans (by nlinarith)

private theorem abs_probe_power_le_four (k : Fin 2) {a : ℝ} (ha : |a|≤2) :
    |a^(k.val+1)|≤4 := by
  fin_cases k
  · norm_num
    exact ha.trans (by norm_num : (2 : ℝ)≤4)
  · change |a^2|≤4
    rw [abs_pow]
    nlinarith [abs_nonneg a]

private theorem abs_probe_power_sub_le_four (k : Fin 2) {a b : ℝ}
    (ha : |a|≤2) (hb : |b|≤2) :
    |a^(k.val+1)-b^(k.val+1)|≤4*|a-b| := by
  have hh := abs_pow_sub_pow_le (a := a) (b := b) (n := k.val+1)
  fin_cases k
  · norm_num
    nlinarith [abs_nonneg (a-b)]
  · change |a^2-b^2|≤4*|a-b|
    norm_num at hh
    have hm := mul_le_mul_of_nonneg_left (max_le ha hb) (by positivity : 0≤|a-b| *2)
    exact hh.trans (by nlinarith)

private theorem abs_mul_center_le {r r' q : ℝ} (_hr : |r|≤1) (hr' : |r'|≤1) (hq : |q|≤1) :
    |r*r'-q*q|≤|r-q|+|r'-q| := by
  rw [show r*r'-q*q=(r-q)*r'+q*(r'-q) by ring]
  have h1 := mul_le_mul_of_nonneg_left hr' (abs_nonneg (r-q))
  have h2 := mul_le_mul_of_nonneg_right hq (abs_nonneg (r'-q))
  exact (abs_add_le _ _).trans (by simp only [abs_mul];linarith)

/-- Explicit deterministic coefficient of the true two-probe localization
error; it is independent of every dimension and Gaussian realization. -/
def amplitudeProbeLocalizationConstant (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) : ℝ :=
  mixtureCoefficients μ p₀*(Nat.choose p₀.val.val (k.val+1) : ℝ)*
    (4*(p₀.val.val-(k.val+1) : ℕ)+4)

theorem amplitudeProbeLocalizationConstant_nonneg (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) :
    0≤amplitudeProbeLocalizationConstant μ p₀ k := by
  unfold amplitudeProbeLocalizationConstant
  exact mul_nonneg (mul_nonneg (mixtureCoefficients_nonnegative μ p₀) (Nat.cast_nonneg _)) (by positivity)

/-- The actual selected physical kernel can be centered using only the
replicas' physical latitude errors. No inverse transverse norm is used. -/
theorem amplitudePhysicalProbePolynomial_center_error_le (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) {r r' q R : ℝ}
    (hr : |r|≤1) (hr' : |r'|≤1) (hq : |q|≤1) (hR : |R|≤1) :
    |amplitudePhysicalProbePolynomial μ p₀ k r r' R-amplitudePhysicalProbePolynomial μ p₀ k q q R|≤
      amplitudeProbeLocalizationConstant μ p₀ k*(|r-q|+|r'-q|) := by
  let A := r*r'
  let B := q*q
  let d := p₀.val.val-(k.val+1)
  let c := mixtureCoefficients μ p₀*(Nat.choose p₀.val.val (k.val+1) : ℝ)
  have hc : 0≤c := mul_nonneg (mixtureCoefficients_nonnegative μ p₀) (Nat.cast_nonneg _)
  have hA : |A|≤1 := by dsimp [A];rw [abs_mul];nlinarith [abs_nonneg r,abs_nonneg r']
  have hB : |B|≤1 := by dsimp [B];rw [abs_mul];nlinarith [abs_nonneg q]
  have hRA : |R-A|≤2 := (abs_sub R A).trans (by linarith)
  have hRB : |R-B|≤2 := (abs_sub R B).trans (by linarith)
  have hBd : |B^d|≤1 := by rw [abs_pow];exact pow_le_one₀ (abs_nonneg B) hB
  have hD := abs_pow_sub_pow_le_unit hA hB d
  have hP := abs_probe_power_le_four k hRA
  have hDiff := abs_probe_power_sub_le_four k hRA hRB
  rw [show (R-A)-(R-B)=-(A-B) by ring,abs_neg] at hDiff
  have h1 := mul_le_mul hD hP (by positivity : 0≤|(R-A)^(k.val+1)|) (by positivity : 0≤(d : ℝ)*|A-B|)
  have h2 := mul_le_mul hBd hDiff (abs_nonneg _) (by norm_num : (0 : ℝ)≤1)
  have hpoly : |A^d*(R-A)^(k.val+1)-B^d*(R-B)^(k.val+1)|≤(4*(d : ℝ)+4)*|A-B| := by
    rw [show A^d*(R-A)^(k.val+1)-B^d*(R-B)^(k.val+1)=
      (A^d-B^d)*(R-A)^(k.val+1)+B^d*((R-A)^(k.val+1)-(R-B)^(k.val+1)) by ring]
    exact (abs_add_le _ _).trans (by simp only [abs_mul];nlinarith)
  have hAB := abs_mul_center_le hr hr' hq
  change |A-B|≤|r-q|+|r'-q| at hAB
  have hbound := mul_le_mul_of_nonneg_left hAB (by positivity : 0≤4*(d : ℝ)+4)
  have hlast := mul_le_mul_of_nonneg_left (hpoly.trans hbound) hc
  unfold amplitudePhysicalProbePolynomial amplitudeProbeLocalizationConstant
  change |c*A^d*(R-A)^(k.val+1)-c*B^d*(R-B)^(k.val+1)|≤c*(4*(d : ℝ)+4)*(|r-q|+|r'-q|)
  rw [show c*A^d*(R-A)^(k.val+1)-c*B^d*(R-B)^(k.val+1)=
    c*(A^d*(R-A)^(k.val+1)-B^d*(R-B)^(k.val+1)) by ring,abs_mul,abs_of_nonneg hc]
  simpa only [mul_assoc] using hlast

/-- The same physical polynomial controls its diagonal trial coefficient. -/
theorem amplitudeSelectedCoefficient_center_error_le (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) {r q : ℝ} (hr : |r|≤1) (hq : |q|≤1) :
    |amplitudeSelectedCoefficient μ p₀ k r-amplitudeSelectedCoefficient μ p₀ k q|≤
      (2*amplitudeProbeLocalizationConstant μ p₀ k)*|r-q| := by
  have hh := amplitudePhysicalProbePolynomial_center_error_le μ p₀ k hr hr hq (by norm_num : |(1 : ℝ)|≤1)
  rw [amplitudePhysicalProbePolynomial_diag,amplitudePhysicalProbePolynomial_diag] at hh
  exact hh.trans_eq (by ring)

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
