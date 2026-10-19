module
public import QuantitativePaper.VectorConditionalVariance
public import QuantitativePaper.VectorEnergyRegularity

@[expose] public section

/-! Literal field-Hessian quadratic forms and the actual conditional terminal
spin variance, obtained from the genuine first and second response derivatives. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem vectorFieldHessian_quadratic_eq_secondResponse {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x w : Field n) :
    inner ℝ w (vectorFieldHessian s β t p j x w)=
      vectorObservableSecondResponse s β t p (fun σ => fieldDot w σ) j 0 x := by
  let f := vectorRecursion s β t p j
  have hs : ContDiff ℝ 2 f := (contDiff_vectorRecursion_field s β t p j).of_le (by simp)
  have he : (fun r : ℝ => fderiv ℝ f (x+r • w) w)=
      fun r => vectorObservableResponse s β t p (fun σ => fieldDot w σ) j r x := by
    funext r
    exact (hasDerivAt_on_affine_line f hs x w r).unique
      (hasDerivAt_vectorRecursion_field_line s β t p w j r x)
  have hd := hasDerivAt_directional_on_affine_line f hs x w 0
  rw [he] at hd
  let R : ℝ≥0 := (Real.sqrt (n : ℝ)*‖w‖).toNNReal
  have hb (σ : Configuration n) : |fieldDot w σ|≤R := by
    change |fieldDot w σ|≤((Real.sqrt (n : ℝ)*‖w‖).toNNReal : ℝ)
    rw [Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    exact abs_fieldDot w σ
  have hresp := hasDerivAt_vectorObservableResponse s β t p (fun σ => fieldDot w σ) R hb j 0 x
  have hh := hd.unique hresp
  rw [real_inner_comm,vectorFieldHessian,inner_hessianOperator]
  simpa only [f,zero_smul,add_zero,directionalHessian] using hh

theorem vectorFieldHessian_covariance_quadratic_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n × ℝ) (j : ℕ) (x w : Field n) :
    observableDepthMass s j*vectorObservableCovariance s β t p (fun σ => fieldDot w σ) j 0 x ≤
      inner ℝ w (vectorFieldHessian s β t p j x w) ∧
    inner ℝ w (vectorFieldHessian s β t p j x w) ≤
      vectorObservableCovariance s β t p (fun σ => fieldDot w σ) j 0 x := by
  rw [vectorFieldHessian_quadratic_eq_secondResponse]
  let R : ℝ≥0 := (Real.sqrt (n : ℝ)*‖w‖).toNNReal
  have hb (σ : Configuration n) : |fieldDot w σ|≤R := by
    change |fieldDot w σ|≤((Real.sqrt (n : ℝ)*‖w‖).toNNReal : ℝ)
    rw [Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    exact abs_fieldDot w σ
  exact vectorObservableSecondResponse_covariance_bounds s β t p _ R hb j 0 x

theorem vectorFieldHessian_actual_conditionalVariance_bounds {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (i : ℕ) (hi : i≤k+2) (w : Field n) :
    ∀ᵐp ∂vectorEuclideanJointLaw s β t a,
      observableDepthMass s (k+2-i)*
        condVar (vectorPastSigma s β t i) (fun p => fieldDot w p.2)
          (vectorEuclideanJointLaw s β t a) p ≤
        inner ℝ w (vectorFieldHessian s β t (vectorEuclideanStateLinear s β t i p.1).1
          (k+2-i) (vectorEuclideanStateLinear s β t i p.1).2 w) ∧
      inner ℝ w (vectorFieldHessian s β t (vectorEuclideanStateLinear s β t i p.1).1
          (k+2-i) (vectorEuclideanStateLinear s β t i p.1).2 w) ≤
        condVar (vectorPastSigma s β t i) (fun p => fieldDot w p.2)
          (vectorEuclideanJointLaw s β t a) p := by
  filter_upwards [vectorSecondResponse_actual_conditionalVariance_bounds s β t a
    (fun σ => fieldDot w σ) i hi] with p hp
  simpa only [vectorFieldHessian_quadratic_eq_secondResponse] using hp

end QuantitativePaper
