-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeChartKacRice
public import SlowEquilibration.SphericalChartGeometry

@[expose] public section

/-! Literal derivative-zero counts of the actual affine latitude field,
under the original tensor disorder law. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalChartKacRice SlowEquilibration.SphereChartVolume
open SlowEquilibration.WholeFieldRegression SlowEquilibration.GaussianLocalCoordinates
open SlowEquilibration.SphericalForm SlowEquilibration.SphericalChartGeometry
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeField {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+2) P)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (x : Vector (n+1)) : ℝ := field c J (latitudeMap w e q x)

theorem latitudeField_contDiff {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+2) P)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) :
    ContDiff ℝ ⊤ (latitudeField c J w e q) := by
  apply (field_contDiff c J).comp
  unfold latitudeMap
  fun_prop

theorem affineChartGamma_zero_iff_derivative_zero {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    {u : Vector n} (hu : ‖u‖ < 2) (g : EuclideanDisorder (n+2) P) :
    affineChartGamma c w e q u g = 0 ↔
      fderiv ℝ (fun y => field c (unpackDisorder g) (affineChart n w e q y)) u = 0 := by
  constructor
  · intro hzero
    ext v
    rw [← affineChartGamma_directional_derivative c w e q hu, hzero, inner_zero_right, zero_apply]
  · intro hzero
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [affineChartGamma_directional_derivative c w e q hu, hzero, zero_apply]

theorem affineChartGamma_zero_iff_intrinsic {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    {u : Vector n} (hu : ‖u‖ < 2) (g : EuclideanDisorder (n+2) P) :
    affineChartGamma c w e q u g = 0 ↔
      surfaceGradient (latitudeField c (unpackDisorder g) w e q) (manuscriptChart n u) = 0 := by
  rw [affineChartGamma_zero_iff_derivative_zero c w e q hu]
  exact chart_critical_iff_intrinsic hu _
    ((latitudeField_contDiff c (unpackDisorder g) w e q).differentiable (by simp) _)

def actualLatitudeChartCount {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (psi : Disorder (n+2) P → Vector n → ℝ≥0∞) (J : Disorder (n+2) P) : ℝ≥0∞ :=
  ∑' u : {u : Vector n | u ∈ ball 0 2 ∧
    fderiv ℝ (fun y => field c J (affineChart n w e q y)) u = 0}, psi J u

def actualLatitudeChartHessian {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (J : Disorder (n+2) P) (u : Vector n) : Vector n →L[ℝ] Vector n :=
  spatialJacobian (affineChartGamma c w e q) (euclideanDisorder J) u

theorem actualLatitudeChartCount_eq_zeroCount {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (psi : Disorder (n+2) P → Vector n → ℝ≥0∞) (J : Disorder (n+2) P) :
    actualLatitudeChartCount c w e q psi J = zeroCount (affineChartGamma c w e q) (ball 0 2)
      (fun z u => psi (unpackDisorder z) u) (euclideanDisorder J) := by
  classical
  have he : {u : Vector n | u ∈ ball 0 2 ∧ affineChartGamma c w e q u (euclideanDisorder J) = 0} =
      {u : Vector n | u ∈ ball 0 2 ∧
        fderiv ℝ (fun y => field c J (affineChart n w e q y)) u = 0} := by
    ext u
    exact and_congr_right (fun hu => by
      simpa only [unpack_euclideanDisorder] using
        affineChartGamma_zero_iff_derivative_zero c w e q (by simpa using hu) (euclideanDisorder J))
  unfold actualLatitudeChartCount zeroCount
  rw [he]
  simp only [unpack_euclideanDisorder]

/-- The literal full-tensor-law Kac--Rice formula for actual critical points
of the affine latitude field, with every full-field Borel mark allowed. -/
theorem actual_tensor_latitude_chart_kacRice {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hfirst : 0 < firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1)
    (psi : Disorder (n+2) P → Vector n → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (n+2) P × Vector n => psi z.1 z.2) :
    AEMeasurable (actualLatitudeChartCount c w e q psi) (disorderLaw (n+2) P) ∧
    (∫⁻ J, actualLatitudeChartCount c w e q psi J ∂disorderLaw (n+2) P) =
      ∫⁻ u in ball 0 2, GaussianRegression.observationPdf (affineChartGamma c w e q u) 0 *
        ∫⁻ J, ENNReal.ofReal |(actualLatitudeChartHessian c w e q J u).det| * psi J u
          ∂coefficientKernel (affineChartGamma c w e q u) 0 := by
  let psiE := fun z : EuclideanDisorder (n+2) P => fun u => psi (unpackDisorder z) u
  have hm : Measurable fun z : EuclideanDisorder (n+2) P × Vector n => psiE z.1 z.2 :=
    hpsi.comp (((unpackCLM (n+2) P).continuous.measurable.comp measurable_fst).prodMk measurable_snd)
  have hk := affine_latitude_marked_kacRice c hc hfirst w hw e he hq psiE hm
  have hlaw := actual_flattened_gaussian (n+2) P
  have hcount := funext fun J => actualLatitudeChartCount_eq_zeroCount c w e q psi J
  have hMap : AEMeasurable (zeroCount (affineChartGamma c w e q) (ball 0 2) psiE)
      ((disorderLaw (n+2) P).map euclideanDisorder) := by
    rw [hlaw.map_eq]
    exact hk.1
  have hAE := hMap.comp_aemeasurable' hlaw.aemeasurable
  refine ⟨?_, ?_⟩
  · rw [hcount]
    exact hAE
  · rw [hcount, hlaw.lintegral_comp hk.1, hk.2]
    apply setLIntegral_congr_fun isOpen_ball.measurableSet
    intro u hu
    dsimp only
    congr 1
    rw [coefficientKernel_apply]
    have hmark : Measurable (fun J : Disorder (n+2) P =>
        ENNReal.ofReal |(actualLatitudeChartHessian c w e q J u).det| * psi J u) := by
      have h := spatial_mark_measurable (affineChartGamma c w e q) u
        (((affineChartGamma_contDiffOn c w e q).contDiffAt
          (isOpen_ball.mem_nhds hu)).differentiableAt_one) psiE hm
      have hg : Measurable (euclideanDisorder (N := n+2) (P := P)) :=
        (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Coordinate (n+2) P => ℝ)).symm.continuous.measurable.comp
          (flatDisorder_measurable _ _)
      simpa only [actualLatitudeChartHessian, Function.comp_def, psiE, unpack_euclideanDisorder]
        using h.comp hg
    rw [lintegral_map hmark (unpackCLM (n+2) P).continuous.measurable]
    rfl

end
end SlowEquilibration.SphericalLatitudeChartKacRice
