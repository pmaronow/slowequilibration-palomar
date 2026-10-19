-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinInterpolation
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! # Dimension-independent Gaussian perturbation fluctuations

For an arbitrary base spin probability, the literal Gaussian log-partition
has Lipschitz constant bounded by the feature norm. Its centered absolute
fluctuation therefore has a dimension-independent bound. This supplies the
concentration input in Panchenko, arXiv:0708.2453v1, Lemma 1.
-/

namespace SlowEquilibration.GaussianPerturbationFluctuation
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
open GaussianSpinInterpolation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι]

/-- The true Gaussian log-partition has the bounded feature's Lipschitz
constant for every base probability law. -/
theorem logPartition_lipschitz (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    LipschitzWith K.toNNReal (logPartition ν L) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((logPartition_contDiff ν L hL hK hb).differentiable (by norm_num))
  intro w
  rw [(logPartition_hasFDerivAt ν L hL hK hb w).fderiv]
  apply (NNReal.coe_le_coe).mp
  change ‖score ν L w‖ ≤ (K.toNNReal : ℝ)
  rw [Real.coe_toNNReal K hK]
  exact norm_score_le ν L hL hK hb w

lemma abs_le_scale_exp_add (x : ℝ) {K : ℝ} (hK : 0 < K) :
    |x| ≤ K*(Real.exp (K⁻¹*x)+Real.exp (-K⁻¹*x)) := by
  have hid : K*(K⁻¹*x)=x := by field_simp
  have hp := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (K⁻¹*x)) hK.le
  have hm := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-K⁻¹*x)) hK.le
  rw [abs_le]
  constructor <;> nlinarith [mul_pos hK (Real.exp_pos (K⁻¹*x)),
    mul_pos hK (Real.exp_pos (-K⁻¹*x))]

/-- Actual centered absolute fluctuations of a Lipschitz Gaussian
observable are bounded uniformly in dimension. -/
theorem integral_abs_centered_le {K : ℝ} (hK : 0 < K)
    (F : EuclideanSpace ℝ ι → ℝ) (hF : LipschitzWith K.toNNReal F) :
    (∫ w,|F w-∫ z,F z ∂SYK.standardGaussianMeasureOnEuclidean ι|
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ 2*Real.exp (1/2)*K := by
  let G := SYK.standardGaussianMeasureOnEuclidean ι
  let X : EuclideanSpace ℝ ι → ℝ := fun w => F w-∫ z,F z ∂G
  have hs := SYK.product_standardGaussian_hasSubgaussianMGF F K hK hF
  have hiX : Integrable (fun w => |X w|) G := by
    simpa only [Real.norm_eq_abs] using hs.integrable.norm
  have hip : Integrable (fun w => Real.exp (K⁻¹*X w)) G := hs.integrable_exp_mul _
  have him : Integrable (fun w => Real.exp (-K⁻¹*X w)) G := hs.integrable_exp_mul _
  have hbp := SYK.product_standardGaussian_mgf_le F K hK hF K⁻¹
  have hbm := SYK.product_standardGaussian_mgf_le F K hK hF (-K⁻¹)
  have hpowp : K^2*(K⁻¹)^2/2=(1 : ℝ)/2 := by field_simp
  have hpowm : K^2*(-K⁻¹)^2/2=(1 : ℝ)/2 := by rw [neg_sq];exact hpowp
  rw [hpowp] at hbp
  rw [hpowm] at hbm
  change (∫ w,Real.exp (K⁻¹*X w) ∂G) ≤ Real.exp (1/2) at hbp
  change (∫ w,Real.exp (-K⁻¹*X w) ∂G) ≤ Real.exp (1/2) at hbm
  change (∫ w,|X w| ∂G) ≤ _
  calc
    _ ≤ ∫ w,K*(Real.exp (K⁻¹*X w)+Real.exp (-K⁻¹*X w)) ∂G :=
      integral_mono hiX ((hip.add him).const_mul K) (fun w => abs_le_scale_exp_add (X w) hK)
    _ = K*((∫ w,Real.exp (K⁻¹*X w) ∂G)+(∫ w,Real.exp (-K⁻¹*X w) ∂G)) := by
      rw [integral_const_mul,integral_add hip him]
    _ ≤ _ := by nlinarith

/-- The literal Gaussian Gibbs log-partition has dimension-free centered
absolute fluctuations controlled by its actual feature bound. -/
theorem logPartition_integral_abs_centered_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 < K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) :
    (∫ w,|logPartition ν L w-∫ z,logPartition ν L z
        ∂SYK.standardGaussianMeasureOnEuclidean ι|
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤ 2*Real.exp (1/2)*K :=
  integral_abs_centered_le hK (logPartition ν L) (logPartition_lipschitz ν L hL hK.le hb)

end
end SlowEquilibration.GaussianPerturbationFluctuation
