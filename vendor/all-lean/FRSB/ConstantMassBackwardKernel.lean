module
public import FRSB.ConstantMassBackwardTest
public import FRSB.ConstantMassKernel

@[expose] public section

/-! The analytic backward quotient is the actual normalized kernel expectation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology NNReal
namespace FRSB
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory

theorem gaussianHeatFlow_exp_eq_exp_coleHopf (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hA : HasLinearGrowth A) (hAm : Measurable A) (x : ℝ) :
    gaussianHeatFlow (fun y => Real.exp (m * A y)) v x = Real.exp (m * coleHopf m v A x) := by
  by_cases hm : m = 0
  · simp [hm, gaussianHeatFlow]
  · simpa only [gaussianHeatFlow, Real.toNNReal_coe] using (exp_mul_coleHopf hA hAm hm v x).symm

theorem backwardHeatQuotient_exp_eq_kernel_integral (m : ℝ) (v : ℝ≥0) (A : ℝ → ℝ)
    (hAc : Continuous A) (hAg : HasLinearGrowth A) (ψ : ℝ → ℝ) (hψ : Measurable ψ) (x : ℝ) :
    backwardHeatQuotient (fun y => Real.exp (m * A y) * ψ y) (fun y => Real.exp (m * A y)) v x =
      ∫ y, ψ y ∂constantMassKernel m v A x := by
  rw [integral_constantMassKernel m v A hAc hAg x ψ]
  have hshift : (gaussianReal 0 v).map (fun z => x + z) = gaussianReal x v := by
    simpa using gaussianReal_map_const_add (μ := 0) (v := v) x
  have hwm : Measurable (fun y => ψ y * constantMassWeight m v A x y) := by
    apply hψ.mul
    unfold constantMassWeight
    fun_prop
  rw [← hshift, integral_map (by fun_prop)
    hwm.aestronglyMeasurable]
  rw [backwardHeatQuotient, gaussianHeatFlow_exp_eq_exp_coleHopf m v A hAg hAc.measurable,
    gaussianHeatFlow, Real.toNNReal_coe, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with z
  unfold constantMassWeight
  rw [mul_sub, Real.exp_sub]
  ring

theorem parisiBackwardQuotient_eq_kernel_integral (β : ℝ) (μ : ParisiMeasure) (b m v x : ℝ)
    (hb : b ∈ Icc (0 : ℝ) 1) (hv : 0 ≤ v) (ψ : ℝ → ℝ) (hψ : Measurable ψ) :
    parisiBackwardQuotient β μ b m ψ v x =
      ∫ y, ψ y ∂constantMassKernel m v.toNNReal (fun y => parisiPotential β μ (b, y)) x := by
  have he := backwardHeatQuotient_exp_eq_kernel_integral m v.toNNReal
    (fun y => parisiPotential β μ (b, y))
    ((continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id))
    (parisiPotential_hasLinearGrowth β μ b hb) ψ hψ x
  rw [Real.coe_toNNReal v hv] at he
  exact he

end FRSB
