-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteMixtureTaylorResidual
public import SlowEquilibration.SphericalCountRectangles

@[expose] public section

/-! Literal scalar covariance and nonnegative coefficients in source10.12
for the critical-conditioned latitude process. The source score quadratic
form is retained, and the possible degree-one coefficient is proved
nonnegative. Identification with the actual conditioned whole-field process,
and the nonnegative degree-zero regression variance, are separate obligations. -/

namespace SlowEquilibration.SphericalParisiConditionedLatitudeCovariance

noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet SphericalSequentialRegression SphericalMarkedWindows
open scoped BigOperators Matrix

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def centerCovariance (μ : FiniteMixture) (Q r : ℝ) : ℝ := μ.xi (Q*r)
def centerFirst (μ : FiniteMixture) (Q r : ℝ) : ℝ := Q*μ.xi1 (Q*r)
def gradientVariance (μ : FiniteMixture) (Q : ℝ) : ℝ := centerFirst μ Q 1

def sourceCross (μ : FiniteMixture) (Q r : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  scorePairEquiv (centerCovariance μ Q r, r*centerFirst μ Q r)

def sourceScoreCorrection (μ : FiniteMixture) (Q r : ℝ) : ℝ :=
  scoreQuadratic μ Q (sourceCross μ Q r)

def sourceConditionalMean (μ : FiniteMixture) (Q e k r : ℝ) : ℝ :=
  (fun i => sourceCross μ Q r i) ⬝ᵥ
    ((μ.scoreCovariance Q)⁻¹ *ᵥ (fun i => scorePairEquiv (e,k) i))

/-- The exact manuscript covariance tau_r, including its actual score
quadratic correction and gradient regression term. -/
def sourceTau (μ : FiniteMixture) (Q r t : ℝ) : ℝ :=
  centerCovariance μ Q (r^2+(1-r^2)*t)-sourceScoreCorrection μ Q r-
    (1-r^2)*(centerFirst μ Q r)^2/gradientVariance μ Q*t

def sourceLinearCoefficient (μ : FiniteMixture) (Q r : ℝ) : ℝ :=
  (1-r^2)*(centerFirst μ Q (r^2)-(centerFirst μ Q r)^2/gradientVariance μ Q)

private theorem center_firstCovariance_identity {P : ℕ} (c : Degree P → ℝ) (Q r : ℝ) :
    firstCovariance (centerCoefficients c Q) r=Q*firstCovariance c (Q*r) := by
  unfold firstCovariance centerCoefficients
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [mul_pow]
  have hpow : Q*Q^(p.val.val-1)=Q^p.val.val := by
    rw [← pow_succ',Nat.sub_add_cancel (show 1 ≤ p.val.val by omega)]
  rw [← hpow]
  ring

theorem centerFirst_eq_firstCovariance (μ : FiniteMixture) (Q r : ℝ) :
    centerFirst μ Q r=firstCovariance (centerCoefficients (mixtureCoefficients μ) Q) r := by
  rw [center_firstCovariance_identity,firstCovariance_mixture]
  rfl

/-- Actual finite-coefficient Cauchy--Schwarz for the first covariance
derivative. It admits either parity and needs no replica positivity. -/
theorem firstCovariance_squared_le {P : ℕ} (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    (r : ℝ) : (firstCovariance c r)^2 ≤ firstCovariance c 1*firstCovariance c (r^2) := by
  let w : Degree P → ℝ := fun p => c p*(p.val.val : ℝ)
  have hw (p : Degree P) : 0 ≤ w p := mul_nonneg (hc p) (Nat.cast_nonneg _)
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun p => w p*r^(p.val.val-1))
    (f := w) (g := fun p => w p*(r^(p.val.val-1))^2)
    (fun p _ => hw p) (fun p _ => mul_nonneg (hw p) (sq_nonneg _))
    (fun p _ => le_of_eq (by ring))
  convert hh using 1
  · rfl
  · unfold firstCovariance
    simp only [one_pow, mul_one, ← pow_mul, Nat.mul_comm 2]
    rfl

theorem source_gradientVariance_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    0 < gradientVariance μ Q := by
  unfold gradientVariance centerFirst
  rw [mul_one]
  exact mul_pos hQ (μ.xi1_pos hQ)

/-- Source10.12(b): the genuine possible degree-one coefficient of tau_r
is nonnegative, including odd original degrees. -/
theorem sourceLinearCoefficient_nonneg (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r ∈ Icc (0 : ℝ) 1) : 0 ≤ sourceLinearCoefficient μ Q r := by
  have hcs := firstCovariance_squared_le (centerCoefficients (mixtureCoefficients μ) Q)
    (centerCoefficients_nonnegative _ (mixtureCoefficients_nonnegative μ) hQ.le) r
  simp_rw [center_firstCovariance_identity, firstCovariance_mixture] at hcs
  have ha := source_gradientVariance_pos μ hQ
  have hh : (centerFirst μ Q r)^2/gradientVariance μ Q ≤ centerFirst μ Q (r^2) := by
    apply (div_le_iff₀ ha).mpr
    simpa only [gradientVariance, centerFirst, mul_one, mul_comm] using hcs
  unfold sourceLinearCoefficient
  exact mul_nonneg (by nlinarith [hr.1,hr.2]) (sub_nonneg.mpr hh)

/-- All nonconstant coefficients of the literal source tau_r. Degree one
is kept; degree≥2 are the actual binomial coefficients of the original xi. -/
def sourceNonconstantCoefficients (μ : FiniteMixture) (Q r : ℝ) : ℕ →₀ ℝ :=
  Finsupp.single 1 (sourceLinearCoefficient μ Q r)+
    μ.taylorResidualCoefficients (Q*r^2) (Q*(1-r^2))

theorem sourceNonconstantCoefficients_zero (μ : FiniteMixture) (Q r : ℝ) :
    sourceNonconstantCoefficients μ Q r 0 = 0 := by
  have hh : μ.taylorResidualCoefficients (Q*r^2) (Q*(1-r^2)) 0=0 :=
    μ.taylorResidualCoefficients_zero_below_two _ _ (k := 0) (by norm_num)
  simpa [sourceNonconstantCoefficients] using hh

theorem sourceNonconstantCoefficients_two_pos (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r ∈ Ioo (0 : ℝ) 1) :
    0 < sourceNonconstantCoefficients μ Q r 2 := by
  have hh : 0 < μ.taylorResidualCoefficients (Q*r^2) (Q*(1-r^2)) 2 :=
    μ.taylorResidualCoefficients_two_pos (mul_pos hQ (sq_pos_of_pos hr.1))
      (mul_pos hQ (by nlinarith [hr.1,hr.2]))
  simpa [sourceNonconstantCoefficients] using hh

theorem sourceNonconstantCoefficients_nonneg (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r ∈ Icc (0 : ℝ) 1) (j : ℕ) :
    0 ≤ sourceNonconstantCoefficients μ Q r j := by
  unfold sourceNonconstantCoefficients
  rw [Finsupp.add_apply]
  apply add_nonneg
  · by_cases hj : j=1
    · subst j
      simpa using sourceLinearCoefficient_nonneg μ hQ hr
    · simp [Ne.symm hj]
  · apply μ.taylorResidualCoefficients_nonneg
    · exact mul_nonneg hQ.le (sq_nonneg r)
    · exact mul_nonneg hQ.le (by nlinarith [hr.1,hr.2])

/-- Exact polynomial identity for the centered source tau_r, with every
coefficient nonnegative and the original linear term retained. -/
theorem source_nonconstant_polynomial_eq (μ : FiniteMixture) {Q r : ℝ}
    (hQ : 0 < Q) (hr : r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    (sourceNonconstantCoefficients μ Q r).sum (fun j a => a*t^j) =
      sourceTau μ Q r t-sourceTau μ Q r 0 := by
  have ha : 0 < Q*r^2 := mul_pos hQ (sq_pos_of_pos hr.1)
  have hb : 0 < Q*(1-r^2) := mul_pos hQ (by nlinarith [hr.1,hr.2])
  have hres := μ.taylorResidual_xi ha hb t
  unfold sourceNonconstantCoefficients
  rw [Finsupp.sum_add_index (by simp) (by intros; ring),
    Finsupp.sum_single_index (by simp)]
  simp only [pow_one]
  change sourceLinearCoefficient μ Q r*t+
    (μ.taylorResidual ha hb).xi t = _
  rw [hres]
  unfold sourceLinearCoefficient sourceTau centerCovariance centerFirst gradientVariance
  simp only [mul_zero,add_zero,sub_zero]
  have he : Q*(r^2+(1-r^2)*t)=Q*r^2+Q*(1-r^2)*t := by ring
  rw [he]
  ring

end
end SlowEquilibration.SphericalParisiConditionedLatitudeCovariance
