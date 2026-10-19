-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFeaturePositiveCube
public import SlowEquilibration.GaussianThreeBlockKernelBudget

/-! Actual replica-covariance and pressure averages of the independent
positive tensor cube for arbitrary continuous spherical feature fields. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianFeatureDirac

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation SphericalPositivePerturbation
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n K : ℕ}

/-- The actual covariance is jointly Borel before restricting the cube. -/
theorem cube_meanPair_measurable (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k v θ : ℝ) :
    Measurable (fun cube : Fin K → ℝ => GaussianThreeBlockComparison.meanPairKernel
      (sphereLaw n) (cubeLinear A β k v cube) threeLabel θ) := by
  let T := cubeLinear (K := K) A β k v (fun _ => 1)
  obtain ⟨B,hB,hTb⟩ := exists_cube_bound hn A hA β k v (fun _ => 1)
  have hT : Measurable T := (cubeLinear_continuous A hA β k v _).measurable
  let _ := gibbsKernel_markov (sphereLaw n) T hT hB hTb
  let G := (gibbsKernel (sphereLaw n) T).comap (cubeRealization (ι := ι) n K θ)
    (cubeRealization_continuous n K θ).measurable
  let χ : Vector n × Vector n → ℝ := fun z =>
    GaussianSpinComparison.signedKernel (twoLinear A β k) twoLabel z.1 z.2
  have hc (i : TwoCoordinate n ι) : Continuous (GaussianSpinComparison.coordinateObservable (twoLinear A β k) i) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).continuous.comp (twoLinear_continuous A hA β k)
  have hχ : Continuous χ := by
    dsimp [χ]
    unfold GaussianSpinComparison.signedKernel
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul (((hc i).comp continuous_fst).mul ((hc i).comp continuous_snd))
  have hjoint : Measurable (fun p => ∫z,χ z ∂(G ×ₖ G) p) := hχ.measurable.stronglyMeasurable.integral_kernel.measurable
  have hm := hjoint.stronglyMeasurable.integral_prod_right'
    (ν := SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K))) |>.measurable
  convert hm using 1
  funext cube
  unfold GaussianThreeBlockComparison.meanPairKernel
  apply integral_congr_ae
  exact .of_forall fun D => by
    rw [GaussianThreeBlockComparison.pairKernelExpectation,cube_gibbs_realization]
    dsimp only
    rw [Kernel.prod_apply]
    change (∫z,GaussianThreeBlockComparison.signedKernel (cubeLinear A β k v cube) threeLabel z.1 z.2
      ∂(gibbsMeasure (sphereLaw n) T (cubeRealization n K θ (cube,D))).prod
        (gibbsMeasure (sphereLaw n) T (cubeRealization n K θ (cube,D))))=
      ∫z,χ z ∂(gibbsKernel (sphereLaw n) T (cubeRealization n K θ (cube,D))).prod
        (gibbsKernel (sphereLaw n) T (cubeRealization n K θ (cube,D)))
    rw [gibbsKernel_apply (sphereLaw n) T hT hB hTb]
    apply integral_congr_ae
    exact .of_forall fun z => three_signedKernel_eq A β k _ z.1 z.2

/-- Actual positive-cube pressure integrability, proved by the compact
original feature and genuine uniform tensor diagonal budget. -/
theorem cube_pressure_integrable (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k : ℝ) {v : ℝ} (hv : 0≤v) (θ : ℝ) :
    Integrable (fun cube : Fin K → ℝ => GaussianThreeBlockComparison.averagedRotatedLogPartition
      (sphereLaw n) (cubeLinear A β k v cube) threeLabel θ) (positiveCubeLaw K) := by
  obtain ⟨B,hB,hbound⟩ := exists_uniform_cube_bound (K := K) hn A hA β k hv
  apply Integrable.of_bound (cube_pressure_measurable hn A hA β k v θ).aestronglyMeasurable
    (B*(∫D : EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K)),‖D‖
      ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K))))
  filter_upwards [positiveCubeLaw_abs_le_two K] with cube hcube
  exact GaussianThreeBlockComparison.norm_averagedRotatedLogPartition_le_gaussianNorm (sphereLaw n) _
    (cubeLinear_continuous A hA β k v cube).measurable hB (hbound cube hcube) threeLabel θ

/-- Integrability of the literal averaged Gibbs pair covariance. -/
theorem cube_meanPair_integrable (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k : ℝ) {v : ℝ} (hv : 0≤v) (θ : ℝ) :
    Integrable (fun cube : Fin K → ℝ => GaussianThreeBlockComparison.meanPairKernel
      (sphereLaw n) (cubeLinear A β k v cube) threeLabel θ) (positiveCubeLaw K) := by
  obtain ⟨B,hB,hbound⟩ := exists_uniform_cube_bound (K := K) hn A hA β k hv
  apply Integrable.of_bound (cube_meanPair_measurable hn A hA β k v θ).aestronglyMeasurable
    ((Fintype.card (ThreeCoordinate n ι (TensorCoordinate n K)) : ℝ)*B^2)
  filter_upwards [positiveCubeLaw_abs_le_two K] with cube hcube
  exact GaussianThreeBlockComparison.norm_meanPairKernel_le (sphereLaw n) _
    (cubeLinear_continuous A hA β k v cube).measurable hB (hbound cube hcube) threeLabel θ

/-- Exact cube-averaged held-bank cost, before any dimension limit. -/
theorem cube_pressure_sub_twoMean_mem_Icc (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k : ℝ) {v : ℝ} (hv : 0≤v) (θ : ℝ) :
    GaussianThreeBlockComparison.parameterAveragedPressure (positiveCubeLaw K) (sphereLaw n)
      (cubeLinear A β k v) threeLabel θ-
      GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n) (twoLinear A β k) twoLabel θ∈Icc 0 (2*v^2) := by
  let Q := GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n) (twoLinear A β k) twoLabel θ
  let P := fun cube : Fin K → ℝ => GaussianThreeBlockComparison.averagedRotatedLogPartition
    (sphereLaw n) (cubeLinear A β k v cube) threeLabel θ
  have hiP : Integrable P (positiveCubeLaw K) := cube_pressure_integrable hn A hA β k hv θ
  have hb : ∀ᵐ cube ∂positiveCubeLaw K,P cube-Q∈Icc (0:ℝ) (2*v^2) := by
    filter_upwards [positiveCubeLaw_abs_le_two K] with cube hcube
    have ht := three_mean_increment_mem_Icc hn A hA β k (cubeFeature n K v cube)
      (SphericalModel.latitudePositivityFeature_continuous n K v cube)
      (SphericalModel.latitudePositivityFeature_norm_sq_le hn hv cube hcube) θ
    rw [show (2*v)^2/2=2*v^2 by ring] at ht
    exact ht
  have hl := integral_nonneg_of_ae (hb.mono fun x hx => hx.1)
  have hu := integral_mono_ae (hiP.sub (integrable_const Q)) (integrable_const (2*v^2))
    (hb.mono fun x hx => hx.2)
  simp only [Pi.sub_apply] at hu
  rw [integral_sub hiP (integrable_const Q)] at hl hu
  simp only [integral_const,probReal_univ,one_smul] at hl hu
  exact ⟨hl,hu⟩

end SlowEquilibration.GaussianFeatureDirac
