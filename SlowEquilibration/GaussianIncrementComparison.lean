-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinComparison

/-! Gaussian comparison from increment covariance, with arbitrary bounded
continuous or measurable spin features. No constant pointwise variance is
required. This is the finite-temperature Sudakov–Fernique comparison used for
covariance-dominated matrix fields. -/

@[expose] public section
namespace SlowEquilibration.GaussianSpinComparison
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace V]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem signedTrace_nonneg_of_increment_comparison (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool)
    (hinc : ∀ᵐ z ∂ν.prod ν, 0 ≤ signedKernel L label z.1 z.1 +
      signedKernel L label z.2 z.2 - 2 * signedKernel L label z.1 z.2)
    (θ : ℝ) (w : EuclideanSpace ℝ ι) :
    0 ≤ ∑ i, covarianceSign label i * variance (coordinateObservable L i)
      (GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w) := by
  let G := GaussianSpinInterpolation.gibbsMeasure ν (rotatedLinear L label θ) w
  have : IsProbabilityMeasure G := GaussianSpinInterpolation.gibbsMeasure_probability ν _
    (rotatedLinear_measurable L hL label θ) (rotatedLinear_bound ν L hK hb label θ) w
  have hac : G ≪ ν := GaussianSpinInterpolation.gibbsMeasure_absolutelyContinuous ν _ w
  have hd : Integrable (fun v => signedKernel L label v v) G :=
    signedKernel_diagonal_integrable ν L hL hK hb label θ w
  have hp : Integrable (fun p : V × V => signedKernel L label p.1 p.2) (G.prod G) :=
    signedKernel_pair_integrable ν L hL hK hb label θ w
  have h1 : Integrable (fun p : V × V => signedKernel L label p.1 p.1) (G.prod G) :=
    measurePreserving_fst.integrable_comp_of_integrable hd
  have h2 : Integrable (fun p : V × V => signedKernel L label p.2 p.2) (G.prod G) :=
    measurePreserving_snd.integrable_comp_of_integrable hd
  have hsum : Integrable (fun p : V × V => signedKernel L label p.1 p.1 +
      signedKernel L label p.2 p.2) (G.prod G) := by
    exact h1.fun_add h2
  have hnonneg := integral_nonneg_of_ae (hinc.filter_mono (hac.prod hac).ae_le)
  rw [integral_sub hsum (hp.const_mul 2), integral_add h1 h2,
    integral_const_mul, integral_fun_fst (fun v => signedKernel L label v v),
    integral_fun_snd (fun v => signedKernel L label v v), probReal_univ, one_smul] at hnonneg
  rw [signedVarianceTrace_eq_kernels ν L hL hK hb label θ w]
  change 0 ≤ (∫ v, signedKernel L label v v ∂G) -
    ∫ p : V × V, signedKernel L label p.1 p.2 ∂G.prod G
  linarith

/-- Actual Gaussian log-partition comparison under increment-covariance
domination. The two compared endpoints are the genuine disjoint-coordinate
Gaussian fields defined by the supplied feature map. -/
theorem gaussian_increment_comparison (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool)
    (hinc : ∀ᵐ z ∂ν.prod ν, 0 ≤ signedKernel L label z.1 z.1 +
      signedKernel L label z.2 z.2 - 2 * signedKernel L label z.1 z.2) :
    averagedRotatedLogPartition ν L label 0 ≤
      averagedRotatedLogPartition ν L label (Real.pi / 2) := by
  have hF (θ : ℝ) := averagedRotatedLogPartition_hasDerivAt_signedTrace ν L hL hK hb label θ
  have hmono : MonotoneOn (averagedRotatedLogPartition ν L label) (Icc 0 (Real.pi / 2)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuous_iff_continuousAt.mpr (fun θ => (hF θ).continuousAt)).continuousOn
      (fun θ _ => (hF θ).differentiableAt.differentiableWithinAt)
    intro θ hθ
    rw [(hF θ).deriv]
    have hθc := interior_subset hθ
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθc.1
      (by linarith [hθc.2, Real.pi_pos])
    have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hθc.1, Real.pi_pos], hθc.2⟩
    exact mul_nonneg (mul_nonneg hs hc) (integral_nonneg fun w =>
      signedTrace_nonneg_of_increment_comparison ν L hL hK hb label hinc θ w)
  exact hmono ⟨le_rfl, by linarith [Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], le_rfl⟩ (by linarith [Real.pi_pos])

end
end SlowEquilibration.GaussianSpinComparison
