-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalAnalyticNeighborhood
public import SlowEquilibration.SphericalOriginalCenterLift

@[expose] public section

/-! The literal scalar Laplace exponent and Gaussian regression profiles
from manuscript Section 12. These are the profiles whose joint saddle
Hessian remains to be checked for the mixed upper band estimate. -/

namespace SlowEquilibration.SphericalTAPMixedBandExponent
noncomputable section
open Set SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity
open ConditionedEntrance SphericalCriticalLatitude
open scoped Matrix
set_option autoImplicit false

/-- The printed two-score cross vector `b(a)`. -/
def sourceMixedCross (μ : FiniteMixture) (Q a : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  scorePairEquiv (μ.xi (Real.sqrt Q*a),
    Real.sqrt Q*a*μ.xi1 (Real.sqrt Q*a))

/-- The printed gradient-regression variance reduction `d(a)`. -/
def sourceMixedGradientReduction (μ : FiniteMixture) (Q a : ℝ) : ℝ :=
  (1-a^2)*(μ.xi1 (Real.sqrt Q*a))^2/μ.xi1 Q

/-- The printed score-regression mean `m_(e,k)(a)`. Its coefficient row is
the actual original-field regression row proved in `regression_score_row_inverse`. -/
def sourceMixedMean (μ : FiniteMixture) (Q e k a : ℝ) : ℝ :=
  valueTheta μ Q a*e+radialTheta μ Q a*k

/-- The printed conditional variance `v(a)` of the original latitude field. -/
def sourceMixedVariance (μ : FiniteMixture) (Q a : ℝ) : ℝ :=
  μ.xi 1-(sourceMixedCross μ Q a 0*valueTheta μ Q a+
    sourceMixedCross μ Q a 1*radialTheta μ Q a)-
    sourceMixedGradientReduction μ Q a

/-- The exact annealed latitude exponent `Ξ(e,k,a)`. -/
def sourceMixedXi (μ : FiniteMixture) (β Q e k a : ℝ) : ℝ :=
  β*sourceMixedMean μ Q e k a+β^2/2*sourceMixedVariance μ Q a

/-- The literal joint exponent `g(e,k,a)` on exterior marks and |a|<1. -/
def sourceMixedBandExponent (μ : FiniteMixture) (β Q e k a : ℝ) : ℝ :=
  sourceRadialProfile μ Q e k+sourceMixedXi μ β Q e k a+
    Real.log (1-a^2)/2

theorem sourceMixedMean_eq_score_inverse (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (e k a : ℝ) :
    sourceMixedMean μ Q e k a =
      (fun i => sourceMixedCross μ Q a i) ⬝ᵥ
        ((μ.scoreCovariance Q)⁻¹ *ᵥ (fun i => scorePairEquiv (e,k) i)) := by
  rw [Matrix.dotProduct_mulVec]
  change sourceMixedMean μ Q e k a =
    Matrix.vecMul ![μ.xi (Real.sqrt Q*a),
      Real.sqrt Q*a*μ.xi1 (Real.sqrt Q*a)] (μ.scoreCovariance Q)⁻¹ ⬝ᵥ ![e,k]
  rw [← regression_score_row_inverse μ hQ hnp a]
  simp [sourceMixedMean,dotProduct,Fin.sum_univ_two]

private theorem mixed_contact_regression_row (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) :
    valueTheta μ Q (Real.sqrt Q)=1 ∧
    radialTheta μ Q (Real.sqrt Q)=0 := by
  have hdet : (μ.scoreCovariance Q).det ≠ 0 :=
    (μ.scoreCovariance_det_pos hQ hnp).ne'
  have hs : Real.sqrt Q*Real.sqrt Q=Q := Real.mul_self_sqrt hQ.le
  constructor
  · rw [valueTheta_eq, hs]
    unfold aScore secondScore
    have hd : (μ.scoreCovariance Q).det =
        μ.xi Q*(Q*μ.xi1 Q+Q^2*μ.xi2 Q)-(Q*μ.xi1 Q)^2 := by
      simp only [Matrix.det_fin_two,FiniteMixture.scoreCovariance,
        Fin.isValue,Fin.reduceEq,ite_true,ite_false]
      ring
    have he : (Q*μ.xi1 Q+Q^2*μ.xi2 Q)*μ.xi Q-
        Q*μ.xi1 Q*(Q*μ.xi1 Q)=
        (μ.scoreCovariance Q).det := by rw [hd]; ring
    rw [he]
    exact div_self hdet
  · rw [radialTheta_eq,hs]
    unfold aScore
    convert zero_div (μ.scoreCovariance Q).det using 1
    ring

/-- At the source contact latitude, the original-field conditional mean is
exactly the center energy, uniformly in the radial mark. -/
theorem sourceMixedMean_contact (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (e k : ℝ) :
    sourceMixedMean μ Q e k (Real.sqrt Q)=e := by
  obtain ⟨hv,hr⟩ := mixed_contact_regression_row μ hQ hnp
  simp [sourceMixedMean,hv,hr]

/-- The printed residual variance at the central latitude is exactly the
true Taylor-residual covariance, independently of the radial mark. -/
theorem sourceMixedVariance_contact (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) :
    sourceMixedVariance μ Q (Real.sqrt Q)=residualAtOne μ Q := by
  obtain ⟨hv,hr⟩ := mixed_contact_regression_row μ hQ hnp
  have hs : Real.sqrt Q*Real.sqrt Q=Q := Real.mul_self_sqrt hQ.le
  have hxi : μ.xi1 Q ≠ 0 := (μ.xi1_pos hQ).ne'
  unfold sourceMixedVariance sourceMixedCross sourceMixedGradientReduction residualAtOne
  simp only [scorePairEquiv_apply,Fin.isValue,hs,hv,hr,mul_one,mul_zero,add_zero]
  field_simp
  simp only [Matrix.cons_val_zero,Real.sq_sqrt hQ.le]

/-- The source joint exponent equals radial marked complexity plus the
energy tilt and residual band free energy at the contact latitude. -/
theorem sourceMixedBandExponent_contact (μ : FiniteMixture) {β Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (e k : ℝ) :
    sourceMixedBandExponent μ β Q e k (Real.sqrt Q)=
      sourceRadialProfile μ Q e k+β*e+
        (Real.log (1-Q)+β^2*residualAtOne μ Q)/2 := by
  rw [sourceMixedBandExponent,sourceMixedXi,
    sourceMixedMean_contact μ hQ hnp,
    sourceMixedVariance_contact μ hQ hnp,
    Real.sq_sqrt hQ.le]
  ring

end
end SlowEquilibration.SphericalTAPMixedBandExponent
