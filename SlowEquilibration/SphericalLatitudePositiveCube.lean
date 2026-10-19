-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCubeRegularity
public import SlowEquilibration.SphericalLatitudeThreeBlockPressure
public import SlowEquilibration.GaussianThreeBlockKernelBudget
public import SlowEquilibration.GaussianThreeBlockParameterComparison
public import SlowEquilibration.SphericalPositiveParameterCube

@[expose] public section

/-! # Actual positive-cube latitude pressure and covariance averages

All parameter integrability and held-perturbation costs are proved for
the literal normalized positive cube law and actual Gaussian banks.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalPositivePerturbation
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n P K : ℕ}

def latitudePositiveCubePressure (n K : ℕ) (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v θ : ℝ) : ℝ :=
  GaussianThreeBlockComparison.parameterAveragedPressure (positiveCubeLaw K) (sphereLaw n)
    (fun cube => latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ

def latitudePositiveCubePairKernel (n K : ℕ) (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v θ : ℝ) : ℝ :=
  GaussianThreeBlockComparison.parameterAveragedPairKernel (positiveCubeLaw K) (sphereLaw n)
    (fun cube => latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ

theorem latitudePositivity_pressure_integrable (hn : 1 ≤ n) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) {v : ℝ} (hv : 0 ≤ v) (θ : ℝ) :
    Integrable (fun cube : Fin K → ℝ =>
      GaussianThreeBlockComparison.averagedRotatedLogPartition (sphereLaw n)
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ)
      (positiveCubeLaw K) := by
  let B := Real.sqrt (β^2*((n+1 : ℕ) : ℝ)*covariancePolynomial c 1+κ*(n : ℝ)+(2*v)^2)
  apply Integrable.of_bound (latitudePositivity_pressure_measurable hn c β κ u e q v θ).aestronglyMeasurable
    (B*(∫D : LatitudeThreeDisorder n P (TensorCoordinate n K),‖D‖
      ∂SYK.standardGaussianMeasureOnEuclidean (LatitudeThreeCoordinate n P (TensorCoordinate n K))))
  filter_upwards [positiveCubeLaw_abs_le_two K] with cube hcube
  exact GaussianThreeBlockComparison.norm_averagedRotatedLogPartition_le_gaussianNorm (sphereLaw n) _
    (latitudeThreeLinear_continuous c β κ u e q _
      (latitudePositivityFeature_continuous n K v cube)).measurable (Real.sqrt_nonneg _)
    (latitudeThreeLinear_positivity_bound hn c hc β hκ u hu e he hq hv cube hcube) latitudeThreeLabel θ

/-- True integrability of the literal disorder-averaged replica kernel on
the actual positive cube, from its actual feature norm budget. -/
theorem latitudePositivity_meanPair_integrable (hn : 1 ≤ n) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) {v : ℝ} (hv : 0 ≤ v) (θ : ℝ) :
    Integrable (fun cube : Fin K → ℝ =>
      GaussianThreeBlockComparison.meanPairKernel (sphereLaw n)
        (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ)
      (positiveCubeLaw K) := by
  let B := Real.sqrt (β^2*((n+1 : ℕ) : ℝ)*covariancePolynomial c 1+κ*(n : ℝ)+(2*v)^2)
  apply Integrable.of_bound (latitudePositivity_meanPair_measurable hn c β κ u e q v θ).aestronglyMeasurable
    ((Fintype.card (LatitudeThreeCoordinate n P (TensorCoordinate n K)) : ℝ)*B^2)
  filter_upwards [positiveCubeLaw_abs_le_two K] with cube hcube
  exact GaussianThreeBlockComparison.norm_meanPairKernel_le (sphereLaw n) _
    (latitudeThreeLinear_continuous c β κ u e q _
      (latitudePositivityFeature_continuous n K v cube)).measurable (Real.sqrt_nonneg _)
    (latitudeThreeLinear_positivity_bound hn c hc β hκ u hu e he hq hv cube hcube) latitudeThreeLabel θ

/-- The actual positive-cube averaged perturbation contributes between
zero and 2v² to every unnormalized latitude interpolation endpoint. -/
theorem latitudePositiveCubePressure_sub_mean_mem_Icc (hn : 1 ≤ n) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) {v : ℝ} (hv : 0 ≤ v) (θ : ℝ) :
    latitudePositiveCubePressure n K c β κ u e q v θ-
      GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n)
        (latitudeGuerraLinear c β κ u e q) latitudeGuerraLabel θ ∈ Icc 0 (2*v^2) := by
  let A := GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n)
    (latitudeGuerraLinear c β κ u e q) latitudeGuerraLabel θ
  let p := fun cube : Fin K → ℝ => GaussianThreeBlockComparison.averagedRotatedLogPartition (sphereLaw n)
    (latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube)) latitudeThreeLabel θ
  have hp : Integrable p (positiveCubeLaw K) :=
    latitudePositivity_pressure_integrable hn c hc β hκ u hu e he hq hv θ
  have hb : ∀ᵐ cube ∂positiveCubeLaw K,p cube-A∈Icc (0 : ℝ) (2*v^2) := by
    filter_upwards [positiveCubeLaw_abs_le_two K] with cube hcube
    have hh := latitudeThree_mean_increment_mem_Icc hn c hc β hκ u hu e he hq
      (latitudePositivityFeature n K v cube) (latitudePositivityFeature_continuous n K v cube)
      (latitudePositivityFeature_norm_sq_le hn hv cube hcube) θ
    rw [show (2*v)^2/2=2*v^2 by ring] at hh
    exact hh
  have hl : 0 ≤ ∫cube,p cube-A ∂positiveCubeLaw K := integral_nonneg_of_ae (hb.mono fun cube hc => hc.1)
  have hupp := integral_mono_ae (hp.sub (integrable_const A)) (integrable_const (2*v^2)) (hb.mono fun cube hc => hc.2)
  simp only [Pi.sub_apply] at hupp
  rw [integral_sub hp (integrable_const A)] at hl hupp
  simp only [integral_const,probReal_univ,one_smul] at hl hupp
  change (∫cube,p cube ∂positiveCubeLaw K)-A∈Icc (0 : ℝ) (2*v^2)
  exact ⟨hl,hupp⟩

end
end SlowEquilibration.SphericalModel
