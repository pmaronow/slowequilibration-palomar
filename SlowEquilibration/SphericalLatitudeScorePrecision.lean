-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeScoreDensity

@[expose] public section

/-! The actual affine score precision splits into the independent radial
and conditional-height quadratic penalties used in strong-field complexity. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression
open scoped Matrix
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem two_dimensional_score_precision {v a A : ℝ} (hA : 0 < A)
    (hd : 0 < v*A-a^2) (x : EuclideanSpace ℝ (Fin 2)) :
    (fun i => x i) ⬝ᵥ ((!![v,a;a,A] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ *ᵥ (fun i => x i)) =
      (x 1)^2/A+(x 0-a*x 1/A)^2/(v-a^2/A) := by
  have hV : 0 < v-a^2/A := by
    apply (div_pos hd hA).trans_eq
    field_simp
  have hdet : v*A-a*a ≠ 0 := by nlinarith
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.adjugate_fin_two_of, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp [hA.ne', hV.ne', hdet, ne_of_gt hd]
  ring

def latitudeValueVariance {P : ℕ} (c : Degree P → ℝ) : ℝ := covariancePolynomial c 1

def latitudeDerivativeVariance {P : ℕ} (c : Degree P → ℝ) (q : ℝ) : ℝ :=
  (1-q^2)*firstCovariance c 1

def latitudeCurvatureVariance {P : ℕ} (c : Degree P → ℝ) (q : ℝ) : ℝ :=
  (1-q^2)^2*secondCovariance c 1

def latitudeConditionalValueVariance {P : ℕ} (c : Degree P → ℝ) (q : ℝ) : ℝ :=
  latitudeValueVariance c-(latitudeDerivativeVariance c q)^2/
    (latitudeDerivativeVariance c q+latitudeCurvatureVariance c q)

theorem latitudeScoreCovariance_eq_matrix {P : ℕ} (c : Degree P → ℝ) (q : ℝ) :
    latitudeScoreCovariance c q =
      !![latitudeValueVariance c, latitudeDerivativeVariance c q;
        latitudeDerivativeVariance c q, latitudeDerivativeVariance c q+latitudeCurvatureVariance c q] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem latitude_score_precision {P : ℕ} (c : Degree P → ℝ) (q : ℝ)
    (hA : 0 < latitudeDerivativeVariance c q+latitudeCurvatureVariance c q)
    (hd : 0 < (latitudeScoreCovariance c q).det) (x : EuclideanSpace ℝ (Fin 2)) :
    latitudeScoreQuadratic c q x =
      (x 1)^2/(latitudeDerivativeVariance c q+latitudeCurvatureVariance c q)+
        (x 0-latitudeDerivativeVariance c q*x 1/
          (latitudeDerivativeVariance c q+latitudeCurvatureVariance c q))^2/
            latitudeConditionalValueVariance c q := by
  rw [latitudeScoreQuadratic, latitudeScoreCovariance_eq_matrix]
  apply two_dimensional_score_precision hA
  rw [latitudeScoreCovariance_eq_matrix, Matrix.det_fin_two] at hd
  simpa only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, pow_two] using hd


theorem center_latitudeDerivativeVariance_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {q : ℝ} (hq : |q| < 1) :
    0 < latitudeDerivativeVariance (centerCoefficients (mixtureCoefficients μ) Q) q := by
  have ht : 0 < 1-q^2 := by nlinarith [(abs_lt.mp hq).1, (abs_lt.mp hq).2]
  rw [latitudeDerivativeVariance, firstCovariance_center, firstCovariance_mixture]
  exact mul_pos ht (mul_pos hQ (mixture_xi1_pos μ hQ))

theorem center_latitudeCurvatureVariance_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {q : ℝ} (hq : |q| < 1) :
    0 < latitudeCurvatureVariance (centerCoefficients (mixtureCoefficients μ) Q) q := by
  have ht : 0 < 1-q^2 := by nlinarith [(abs_lt.mp hq).1, (abs_lt.mp hq).2]
  rw [latitudeCurvatureVariance, secondCovariance_center, secondCovariance_mixture]
  exact mul_pos (sq_pos_of_pos ht) (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ))

theorem center_latitudeConditionalValueVariance_pos (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) :
    0 < latitudeConditionalValueVariance (centerCoefficients (mixtureCoefficients μ) Q) q := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hA : 0 < latitudeDerivativeVariance c q+latitudeCurvatureVariance c q :=
    add_pos (center_latitudeDerivativeVariance_pos μ hQ hq1) (center_latitudeCurvatureVariance_pos μ hQ hq1)
  have hd := center_latitudeScoreCovariance_det_pos μ hQ hq0 hq1
  rw [latitudeScoreCovariance_eq_matrix, Matrix.det_fin_two] at hd
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hd
  change 0 < latitudeValueVariance c-(latitudeDerivativeVariance c q)^2/
    (latitudeDerivativeVariance c q+latitudeCurvatureVariance c q)
  apply (div_pos hd hA).trans_eq
  field_simp
  ring

/-- Exact BCNS radial and conditional-height penalties for the actual
normalized affine score, with all covariance hypotheses discharged. -/
theorem center_latitude_score_precision (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    {q : ℝ} (hq0 : q ≠ 0) (hq1 : |q| < 1) (x : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    latitudeScoreQuadratic c q x =
      (x 1)^2/(latitudeDerivativeVariance c q+latitudeCurvatureVariance c q)+
        (x 0-latitudeDerivativeVariance c q*x 1/
          (latitudeDerivativeVariance c q+latitudeCurvatureVariance c q))^2/
            latitudeConditionalValueVariance c q :=
  latitude_score_precision _ q
    (add_pos (center_latitudeDerivativeVariance_pos μ hQ hq1) (center_latitudeCurvatureVariance_pos μ hQ hq1))
    (center_latitudeScoreCovariance_det_pos μ hQ hq0 hq1) x

end
end SlowEquilibration.SphericalLatitudeChartKacRice
