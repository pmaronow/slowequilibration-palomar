-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianCovarianceRepresentation
public import SlowEquilibration.GaussianNormConcentration
public import SlowEquilibration.GaussianNormMean

/-! Dimension-free ordinary norm moments of actual centered Gaussian
vectors with bounded covariance and bounded expected-norm scale. -/
@[expose] public section
namespace SlowEquilibration.GaussianVectorPolynomialMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianCovarianceRepresentation GaussianNormMean
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- True ordinary moments on the object's own space, with no moment
premise: Gaussian representation, the actual Gaussian mean norm, and genuine
Herbst concentration provide the uniform factorial bound. -/
theorem centered_gaussian_norm_moments (μ : Measure E) [IsGaussian μ]
    (hmean : ∫ x,x ∂μ=0) {σ A : ℝ} (hσ : 0 < σ)
    (hcov : ∀ x:E,covarianceBilin μ x x ≤ σ^2*‖x‖^2)
    (hscale : σ*Real.sqrt (Module.finrank ℝ E:ℝ) ≤ A) :
    ∀ r:ℕ,Integrable (fun x:E=>‖x‖^r) μ ∧
      (∫ x,‖x‖^r ∂μ) ≤ (r.factorial:ℝ)*Real.exp (A+σ^2/2) := by
  obtain ⟨W,hW,hLaw⟩:=exists_fixed_bounded_gaussian_realization μ hmean hσ.le hcov
  let P:=SYK.standardGaussianMeasureOnEuclidean (Fin (Module.finrank ℝ E))
  have hstd : P=stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) := map_pi_eq_stdGaussian
  have : IsGaussian P:=by rw [hstd];infer_instance
  have hLip : LipschitzWith σ.toNNReal (fun g:EuclideanSpace ℝ (Fin (Module.finrank ℝ E))=>‖W g‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq,dist_eq_norm,Real.coe_toNNReal _ hσ.le]
    calc
      _ ≤ ‖W x-W y‖:=abs_norm_sub_norm_le _ _
      _=‖W (x-y)‖:=by rw [map_sub]
      _ ≤ ‖W‖*‖x-y‖:=W.le_opNorm _
      _ ≤ σ*‖x-y‖:=mul_le_mul_of_nonneg_right hW (norm_nonneg _)
  have hInt : Integrable (fun g=>‖W g‖) P:=((IsGaussian.hasGaussianLaw_id (μ:=P)).map_fun W).integrable.norm
  have hIntId : Integrable (fun g:EuclideanSpace ℝ (Fin (Module.finrank ℝ E))=>‖g‖) P:=by
    simpa only [id_eq] using (IsGaussian.integrable_fun_id (μ:=P)).norm
  let m:=∫ g,‖W g‖ ∂P
  have hM : m ≤ A := by
    calc
      _ ≤ ∫ g,σ*‖g‖ ∂P:=integral_mono_ae hInt (hIntId.const_mul σ)
        (ae_of_all _ (fun g=>(W.le_opNorm g).trans (mul_le_mul_of_nonneg_right hW (norm_nonneg _))))
      _=σ*(∫ g,‖g‖ ∂P):=integral_const_mul _ _
      _ ≤ σ*Real.sqrt (Module.finrank ℝ E:ℝ):=mul_le_mul_of_nonneg_left
        (by simpa only [Fintype.card_fin] using standardGaussian_integral_norm_le_sqrt_card (ι:=Fin (Module.finrank ℝ E))) hσ.le
      _ ≤ A:=hscale
  have hG:=SYK.product_standardGaussian_hasSubgaussianMGF
    (fun g:EuclideanSpace ℝ (Fin (Module.finrank ℝ E))=>‖W g‖) σ hσ hLip
  have hExp : Integrable (fun g=>Real.exp ‖W g‖) P := by
    apply ((hG.integrable_exp_mul 1).const_mul (Real.exp m)).congr
    exact ae_of_all P (fun g=>by
      simp only [one_mul]
      rw [← Real.exp_add]
      congr 1
      dsimp only [m]
      ring)
  have hExpBound : (∫ g,Real.exp ‖W g‖ ∂P) ≤ Real.exp (A+σ^2/2) := by
    have heq : (fun g=>Real.exp ‖W g‖)=(fun g=>Real.exp m*Real.exp (‖W g‖-m)) := by
      funext g
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq,integral_const_mul]
    have hh:=hG.mgf_le 1
    simp only [mgf,one_mul,one_pow,mul_one,Real.coe_toNNReal _ (sq_nonneg σ)] at hh
    calc
      _ ≤ Real.exp m*Real.exp (σ^2/2):=mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le
      _=Real.exp (m+σ^2/2):=(Real.exp_add _ _).symm
      _ ≤ Real.exp (A+σ^2/2):=Real.exp_le_exp.mpr (add_le_add hM le_rfl)
  intro r
  have hpoint (g:EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
      ‖W g‖^r ≤ (r.factorial:ℝ)*Real.exp ‖W g‖ := by
    have hh:=Real.pow_div_factorial_le_exp ‖W g‖ (norm_nonneg (W g)) r
    have hp : (0:ℝ) < r.factorial:=Nat.cast_pos.mpr (Nat.factorial_pos r)
    simpa only [mul_comm] using (div_le_iff₀ hp).mp hh
  have hPow : Integrable (fun g=>‖W g‖^r) P:=(hExp.const_mul (r.factorial:ℝ)).mono'
    ((W.continuous.norm.pow r).measurable.aestronglyMeasurable)
    (ae_of_all _ (fun g=>by simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)] using hpoint g))
  constructor
  · rw [← hLaw]
    exact (integrable_map_measure (continuous_norm.pow r).measurable.aestronglyMeasurable W.continuous.measurable.aemeasurable).mpr hPow
  · rw [← hLaw,integral_map (μ:=P) (φ:=W) (f:=fun x:E=>‖x‖^r) W.continuous.measurable.aemeasurable (continuous_norm.pow r).measurable.aestronglyMeasurable]
    calc
      _ ≤ ∫ g,(r.factorial:ℝ)*Real.exp ‖W g‖ ∂P:=integral_mono_ae hPow (hExp.const_mul _) (ae_of_all _ hpoint)
      _=(r.factorial:ℝ)*(∫ g,Real.exp ‖W g‖ ∂P):=integral_const_mul _ _
      _ ≤ _:=mul_le_mul_of_nonneg_left hExpBound (Nat.cast_nonneg _)

end
end SlowEquilibration.GaussianVectorPolynomialMoments
