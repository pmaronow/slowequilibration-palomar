-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianQuadratic
public import SlowEquilibration.GaussianNormMean

@[expose] public section

/-! A genuine shifted linear Gaussian endpoint bound for the labeled
one-step spherical ground comparison. The common Gaussian field is retained
in the exact quadratic integral. This is the dual trial endpoint; its
identification with every primal Huang--Sellke profile is a separate
variational obligation. -/

namespace SlowEquilibration.SphericalParisiShiftedGaussianTrial

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def shiftedNormMoment (h : E) (a ell : ℝ) : ℝ :=
  ∫ g : E,Real.exp (ell*‖h+Real.sqrt a • g‖) ∂stdGaussian E

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem young_norm (x : E) {ell b : ℝ} (hEll : 0 ≤ ell) (hb : 0 < b) :
    ell*‖x‖ ≤ ell*b/2+ell/(2*b)*‖x‖^2 := by
  have hs := mul_nonneg hEll (sq_nonneg (‖x‖-b))
  apply (mul_le_mul_iff_right₀ (show 0 < 2*b by positivity)).mp
  have he : (2*b)*(ell*b/2+ell/(2*b)*‖x‖^2)=ell*b^2+ell*‖x‖^2 := by field_simp
  rw [he]
  nlinarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem quadratic_envelope_eq (h g : E) {a : ℝ} (ha : 0 ≤ a) (ell b : ℝ) :
    Real.exp (ell*b/2+ell/(2*b)*‖h+Real.sqrt a • g‖^2) =
      Real.exp (ell*b/2+ell/(2*b)*‖h‖^2)*
        Real.exp (inner ℝ ((ell*Real.sqrt a/b) • h) g-
          ((1-ell*a/b)-1)/2*‖g‖^2) := by
  rw [← Real.exp_add,norm_add_sq_real,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg a),mul_pow,Real.sq_sqrt ha,
    real_inner_smul_right,real_inner_smul_left]
  congr 1
  ring

private theorem quadratic_envelope_integrable (h : E) {a ell b : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hmargin : 0 < b-ell*a) :
    Integrable (fun g : E => Real.exp (ell*b/2+ell/(2*b)*‖h+Real.sqrt a • g‖^2))
      (stdGaussian E) := by
  have hz : 0 < 1-ell*a/b := by
    rw [sub_div' hb.ne',one_mul]
    exact div_pos hmargin hb
  have hi := (GaussianQuadratic.integrable_exp_quadratic hz
    ((ell*Real.sqrt a/b) • h)).const_mul (Real.exp (ell*b/2+ell/(2*b)*‖h‖^2))
  apply hi.congr
  exact .of_forall (fun g => (quadratic_envelope_eq h g ha ell b).symm)

theorem shiftedNormMoment_integrable (h : E) {a ell b : ℝ}
    (ha : 0 ≤ a) (hEll : 0 ≤ ell) (hb : 0 < b) (hmargin : 0 < b-ell*a) :
    Integrable (fun g : E => Real.exp (ell*‖h+Real.sqrt a • g‖)) (stdGaussian E) := by
  have hm : AEStronglyMeasurable (fun g : E => Real.exp (ell*‖h+Real.sqrt a • g‖))
      (stdGaussian E) :=
    (Real.continuous_exp.comp ((continuous_const.add
      (continuous_id.const_smul (Real.sqrt a))).norm.const_mul ell)).aestronglyMeasurable
  apply (quadratic_envelope_integrable h ha hb hmargin).mono' hm
  exact .of_forall (fun g => by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (young_norm _ hEll hb))

/-- The actual shifted Gaussian norm exponential moment is bounded by
the exact finite-dimensional quadratic integral, with the common mean kept. -/
theorem shiftedNormMoment_le_quadratic (h : E) {a ell b : ℝ}
    (ha : 0 ≤ a) (hEll : 0 ≤ ell) (hb : 0 < b) (hmargin : 0 < b-ell*a) :
    shiftedNormMoment h a ell ≤
      (1-ell*a/b)^(-((Module.finrank ℝ E : ℝ)/2))*
        Real.exp (ell*b/2+ell*‖h‖^2/(2*(b-ell*a))) := by
  have hz : 0 < 1-ell*a/b := by
    rw [sub_div' hb.ne',one_mul]
    exact div_pos hmargin hb
  have hh := integral_mono (shiftedNormMoment_integrable h ha hEll hb hmargin)
    (quadratic_envelope_integrable h ha hb hmargin)
    (fun g => Real.exp_le_exp.mpr (young_norm _ hEll hb))
  change shiftedNormMoment h a ell ≤ _ at hh
  apply hh.trans_eq
  simp_rw [quadratic_envelope_eq h _ ha ell b]
  rw [integral_const_mul,GaussianQuadratic.integral_exp_quadratic hz]
  rw [mul_left_comm,← Real.exp_add]
  congr 2
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,div_pow,mul_pow,Real.sq_sqrt ha]
  field_simp [hb.ne',hmargin.ne']
  ring

theorem shiftedNormMoment_one_le (h : E) {a ell b : ℝ}
    (ha : 0 ≤ a) (hEll : 0 ≤ ell) (hb : 0 < b) (hmargin : 0 < b-ell*a) :
    1 ≤ shiftedNormMoment h a ell := by
  have hh := integral_mono (integrable_const (1 : ℝ))
    (shiftedNormMoment_integrable h ha hEll hb hmargin)
    (fun g => Real.one_le_exp_iff.mpr (mul_nonneg hEll (norm_nonneg _)))
  simpa only [integral_const,probReal_univ,one_smul,shiftedNormMoment] using hh

/-- The genuine common-field logarithmic trial, before any primal/dual
variational minimization. It contains the exact degree/determinant term. -/
theorem log_shiftedNormMoment_le (h : E) {a ell b : ℝ}
    (ha : 0 ≤ a) (hEll : 0 ≤ ell) (hb : 0 < b) (hmargin : 0 < b-ell*a) :
    Real.log (shiftedNormMoment h a ell) ≤
      -((Module.finrank ℝ E : ℝ)/2)*Real.log (1-ell*a/b)+
        ell*b/2+ell*‖h‖^2/(2*(b-ell*a)) := by
  have hz : 0 < 1-ell*a/b := by
    rw [sub_div' hb.ne',one_mul]
    exact div_pos hmargin hb
  have hp : 0 < shiftedNormMoment h a ell :=
    lt_of_lt_of_le zero_lt_one (shiftedNormMoment_one_le h ha hEll hb hmargin)
  have hh := Real.log_le_log hp (shiftedNormMoment_le_quadratic h ha hEll hb hmargin)
  rw [Real.log_mul (Real.rpow_pos_of_pos hz _).ne' (Real.exp_pos _).ne',
    Real.log_rpow hz,Real.log_exp] at hh
  simpa only [add_assoc] using hh

end
end SlowEquilibration.SphericalParisiShiftedGaussianTrial
