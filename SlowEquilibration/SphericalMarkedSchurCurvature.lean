-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.TwoByTwoLeastCurvature
public import SlowEquilibration.SphericalRadialEnergyTilt
public import SlowEquilibration.CSStructure

/-! The positive modified score precision in the manuscript. Its least
curvature is the literal smaller eigenvalue, and its Schur complement is
derived from the genuine finite-mixture covariance. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open TwoAtomStationarity
open scoped Matrix
set_option maxHeartbeats 400000

def sourceModifiedRadialCurvature (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  sourceRadialCurvature μ Q-1/(2*(Q^2*μ.xi2 Q))

def sourceSchurCurvature (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  sourceModifiedRadialCurvature μ Q-(sourceEnergyRadialCross μ Q)^2/sourceEnergyCurvature μ Q

def sourceMarkedLeastCurvature (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  TwoByTwoLeastCurvature.least (sourceEnergyCurvature μ Q) (sourceEnergyRadialCross μ Q)
    (sourceModifiedRadialCurvature μ Q)

def sourceMarkedPrecision (μ : FiniteMixture) (Q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![sourceEnergyCurvature μ Q,sourceEnergyRadialCross μ Q;
    sourceEnergyRadialCross μ Q,sourceModifiedRadialCurvature μ Q]

theorem sourceEnergyRadialCross_eq (μ : FiniteMixture) (Q : ℝ) :
    sourceEnergyRadialCross μ Q=-(Q*μ.xi1 Q)/(μ.scoreCovariance Q).det := by
  simp only [sourceEnergyRadialCross,Matrix.inv_def,Ring.inverse_eq_inv,
    Matrix.adjugate_fin_two,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  unfold FiniteMixture.scoreCovariance
  simp only [Fin.isValue,Fin.reduceEq,ite_true,ite_false]
  ring

theorem sourceEnergyRadialCross_neg (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) : sourceEnergyRadialCross μ Q < 0 := by
  rw [sourceEnergyRadialCross_eq]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos hQ (μ.xi1_pos hQ)))
    (μ.scoreCovariance_det_pos hQ hnp)

theorem sourceScoreCovariance_det_eq (μ : FiniteMixture) (Q : ℝ) :
    (μ.scoreCovariance Q).det=μ.xi Q*(Q*μ.xi1 Q+Q^2*μ.xi2 Q)-(Q*μ.xi1 Q)^2 := by
  rw [Matrix.det_fin_two]
  simp only [FiniteMixture.scoreCovariance,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
  ring

private theorem schur_algebra {a b V D : ℝ} (hD : D ≠ 0) (hAB : a+b ≠ 0)
    (hb : b ≠ 0) (heq : D=V*(a+b)-a^2) :
    (V/D-1/(2*b))-(-a/D)^2/((a+b)/D)=1/(a+b)-1/(2*b) := by
  field_simp [hD,hAB,hb]
  nlinarith [congrArg (fun z : ℝ => z*(2*b)) heq]

theorem sourceSchurCurvature_eq (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    sourceSchurCurvature μ Q=1/(Q*μ.xi1 Q+Q^2*μ.xi2 Q)-1/(2*(Q^2*μ.xi2 Q)) := by
  have ha := mul_pos hQ (μ.xi1_pos hQ)
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hD := (μ.scoreCovariance_det_pos hQ hnp).ne'
  have hAB := (add_pos ha hb).ne'
  have heq := sourceScoreCovariance_det_eq μ Q
  unfold sourceSchurCurvature sourceModifiedRadialCurvature
  rw [sourceRadialCurvature_eq,sourceEnergyRadialCross_eq,sourceEnergyCurvature_eq]
  exact schur_algebra hD hAB hb.ne' heq

theorem sourceRadialVariance_gt_energyRadial (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hd : 3 ≤ μ.minDegree) : Q*μ.xi1 Q < Q^2*μ.xi2 Q := by
  have hh := mul_lt_mul_of_pos_left (CSStructure.degree_gap μ hd hQ) hQ
  nlinarith

theorem sourceSchurCurvature_pos (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hd : 3 ≤ μ.minDegree) (hnp : μ.minDegree < μ.maxDegree) :
    0 < sourceSchurCurvature μ Q := by
  rw [sourceSchurCurvature_eq μ hQ hnp]
  have ha := mul_pos hQ (μ.xi1_pos hQ)
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  apply sub_pos.mpr
  exact one_div_lt_one_div_of_lt (add_pos ha hb) (by
    linarith [sourceRadialVariance_gt_energyRadial μ hQ hd])

/-- The manuscript's least modified-precision eigenvalue is positive. -/
theorem sourceMarkedLeastCurvature_pos (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hd : 3 ≤ μ.minDegree) (hnp : μ.minDegree < μ.maxDegree) :
    0 < sourceMarkedLeastCurvature μ Q :=
  TwoByTwoLeastCurvature.least_pos (sourceEnergyCurvature_pos μ hQ hnp)
    (sourceSchurCurvature_pos μ hQ hd hnp)

theorem sourceMarkedLeastCurvature_le_schur (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hd : 3 ≤ μ.minDegree) (hnp : μ.minDegree < μ.maxDegree) :
    sourceMarkedLeastCurvature μ Q ≤ sourceSchurCurvature μ Q :=
  TwoByTwoLeastCurvature.least_le_schur (sourceEnergyCurvature_pos μ hQ hnp)
    (sourceSchurCurvature_pos μ hQ hd hnp)

theorem sourceMarkedPrecision_quadratic_lower (μ : FiniteMixture) (Q e k : ℝ) :
    sourceMarkedLeastCurvature μ Q*(e^2+k^2) ≤
      sourceEnergyCurvature μ Q*e^2+2*sourceEnergyRadialCross μ Q*e*k+
        sourceModifiedRadialCurvature μ Q*k^2 :=
  TwoByTwoLeastCurvature.quadratic_lower _ _ _ _ _

/-- An actual nonzero eigenvector of the literal modified covariance inverse
attains the stated least curvature. -/
theorem sourceMarkedPrecision_least_eigenvector (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧
      sourceMarkedPrecision μ Q *ᵥ v=sourceMarkedLeastCurvature μ Q • v := by
  let e := -sourceEnergyRadialCross μ Q/
    (sourceEnergyCurvature μ Q-sourceMarkedLeastCurvature μ Q)
  obtain ⟨he,hk⟩ := TwoByTwoLeastCurvature.least_eigenvector
    (A := sourceEnergyCurvature μ Q) (C := sourceModifiedRadialCurvature μ Q)
    (sourceEnergyRadialCross_neg μ hQ hnp).ne
  refine ⟨![e,1],?_,?_⟩
  · intro hh
    have hx := congrFun hh 1
    norm_num at hx
  · ext i
    fin_cases i
    · norm_num [sourceMarkedPrecision,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      exact he
    · norm_num [sourceMarkedPrecision,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
      exact hk

/-- Every eigenvalue of the literal modified precision is at least the
attained eigenvalue, establishing that this is its smallest eigenvalue. -/
theorem sourceMarkedPrecision_eigenvalue_lower (μ : FiniteMixture) (Q η : ℝ)
    {v : Fin 2 → ℝ} (hv : v ≠ 0)
    (heig : sourceMarkedPrecision μ Q *ᵥ v=η • v) :
    sourceMarkedLeastCurvature μ Q ≤ η := by
  have h0 := congrFun heig 0
  have h1 := congrFun heig 1
  simp only [sourceMarkedPrecision,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Pi.smul_apply,
    smul_eq_mul] at h0 h1
  have hh := sourceMarkedPrecision_quadratic_lower μ Q (v 0) (v 1)
  have hp : 0 < (v 0)^2+(v 1)^2 := by
    by_contra hn
    have hz0 : v 0=0 := by nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]
    have hz1 : v 1=0 := by nlinarith [sq_nonneg (v 0),sq_nonneg (v 1)]
    apply hv
    ext i
    fin_cases i <;> assumption
  nlinarith [congrArg (fun z : ℝ => z*v 0) h0,congrArg (fun z : ℝ => z*v 1) h1]

end SlowEquilibration.SphericalMarkedWindows
