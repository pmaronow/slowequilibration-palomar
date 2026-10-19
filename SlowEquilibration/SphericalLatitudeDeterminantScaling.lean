-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCountIntensity
public import SlowEquilibration.ConditionedDeterminantMoments
public import SlowEquilibration.UnrestrictedConditionedDeterminants

@[expose] public section

/-! Exact conversion from the actual latitude Hessian determinant to the
ordinary physical GOE mean with the correct two-dimensional codimension. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalGaussianJet SlowEquilibration.GOEScaling
open SlowEquilibration.GOERawMoments SlowEquilibration.GOEPhysicalPotential
open SlowEquilibration.ConditionedDeterminantMoments SlowEquilibration.UnrestrictedConditionedDeterminants
open scoped ENNReal
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem scaleFactor_mul_square (n N : ℕ) {v t : ℝ} (_hv : 0 ≤ v) (ht : 0 ≤ t) :
    scaleFactor n N (t^2*v)=t*scaleFactor n N v := by
  unfold scaleFactor
  rw [show t^2*v*(n+1 : ℝ)/N=t^2*(v*(n+1 : ℝ)/N) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]

theorem actual_goeLaw_map_scalar (n : ℕ) {N : ℕ} (hN : 0 < N)
    {v t : ℝ} (hv : 0 ≤ v) (ht : 0 ≤ t) :
    (goeLaw (n+1) N v).map (fun W => t • W)=goeLaw (n+1) N (t^2*v) := by
  have hm (r : ℝ) : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => r • W) := by fun_prop
  rw [← goeLaw_scale n hN hv, ← goeLaw_scale n hN (mul_nonneg (sq_nonneg t) hv),
    Measure.map_map (hm t) (hm _)]
  congr 1
  funext W
  simp only [Function.comp_def, smul_smul, scaleFactor_mul_square n N hv ht]

theorem physicalMean_lintegral_ofReal (n N : ℕ) (v k : ℝ) :
    (∫⁻ W, ENNReal.ofReal (matrixAbsoluteDet n k W) ∂goeLaw (n+1) N v)=
      ENNReal.ofReal (physicalMean n N v k) := by
  have hi : Integrable (matrixAbsoluteDet n k) (goeLaw (n+1) N v) := by
    simpa only [shifted_abs_det] using (fixed_shifted_determinant_integrable (n+1) N v k).abs
  exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).symm

/-- Exact finite-dimensional physical scaling: inner tangent dimension n+1,
original tensor ambient dimension n+3, and section radial target (n+3)k. -/
theorem latitudeDeterminantMean_eq_physicalMean (n : ℕ) {v q : ℝ}
    (hv : 0 ≤ v) (hq : |q| ≤ 1) (k : ℝ) :
    latitudeDeterminantMean (n+1) v q (((n+3 : ℕ) : ℝ)*k) =
      ENNReal.ofReal ((((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ))^(n+1) *
        physicalMean n (n+3) ((1-q^2)^2*v) k) := by
  let r : ℝ := ((n+3 : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)
  let t : ℝ := 1-q^2
  have hr : 0 < r := div_pos (by positivity) (by positivity)
  have ht : 0 ≤ t := by dsimp only [t]; nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  have hs : (latitudeScale (n+1) q)^2=r*t := latitudeScale_sq hq
  have he (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
      |((latitudeScale (n+1) q)^2 • W -
        ((((n+3 : ℕ) : ℝ)*k)/((n+2 : ℕ) : ℝ)) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)).det| =
      r^(n+1)*matrixAbsoluteDet n k (t • W) := by
    have hm : (latitudeScale (n+1) q)^2 • W -
        ((((n+3 : ℕ) : ℝ)*k)/((n+2 : ℕ) : ℝ)) • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) =
        r • (t • W-k • 1) := by
      rw [hs, smul_sub, smul_smul, smul_smul]
      congr 1
      congr 1
      dsimp only [r]
      ring
    rw [hm, Matrix.det_smul, Fintype.card_fin, abs_mul, abs_of_pos (pow_pos hr _), shifted_abs_det]
  have hm : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => t • W) := by fun_prop
  have hd : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
      ENNReal.ofReal (matrixAbsoluteDet n k W)) := (matrixAbsoluteDet_measurable n k).ennreal_ofReal
  unfold latitudeDeterminantMean
  simp_rw [he, ENNReal.ofReal_mul (pow_pos hr _).le]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_map hd hm, actual_goeLaw_map_scalar n (by omega) hv ht,
    physicalMean_lintegral_ofReal]
  rw [← ENNReal.ofReal_mul (pow_pos hr _).le]

end
end SlowEquilibration.SphericalLatitudeChartKacRice
