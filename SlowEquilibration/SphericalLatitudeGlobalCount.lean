-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeConditionedHessian
public import SlowEquilibration.SphericalKacRiceGluing

@[expose] public section

/-! Genuine global critical-point counts for the actual affine latitude
field. The omitted chart pole is proved almost surely noncritical from its
actual positive-variance Gaussian derivative. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalForm SlowEquilibration.SphericalKacRiceGluing
open SlowEquilibration.SphericalChartGeometry SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphereChartVolume SlowEquilibration.WholeFieldRegression
open SlowEquilibration.IntrinsicHessianLaw SlowEquilibration.SphereHessian
open SphericalAging.HardSphereDynamics
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitude_fixed_point_noncritical_ae {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hfirst : 0 < firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    ∀ᵐ J ∂disorderLaw (n+2) P, surfaceGradient (latitudeField c J w e q) y ≠ 0 := by
  let i : Fin n := ⟨0, by omega⟩
  have hlaw := tangentGradientCoordinate_hasLaw (by omega) c hc (latitudeMap w e q y)
    (latitudeMap_norm_sq (by omega) w hw e he hq.le y hy)
    (latitudeEmbeddedFrame e y hy) (latitudeEmbeddedFrame_orthonormal e y hy)
    (latitudeEmbeddedFrame_tangent w e he q y hy) i
  have : NullSingletonClass (gaussianReal 0 (firstCovariance c 1).toNNReal) :=
    nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hfirst))
  have hnonzero : ∀ᵐ J ∂disorderLaw (n+2) P,
      tangentGradientCoordinates c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy) J i ≠ 0 := by
    rw [ae_iff]
    have hz := hlaw.measure_eq (p := fun z => z=0) (measurableSet_singleton 0)
    simpa only [not_not, Set.ofPred_eq_eq_singleton, measure_singleton] using hz
  have hs : latitudeScale n q ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have ht : 0 < 1-q^2 := by nlinarith [(abs_lt.mp hq).1, (abs_lt.mp hq).2]
    exact mul_pos (div_pos (by positivity) (by positivity)) ht
  have hsphere : OnSphere y := by
    change inner ℝ y y = _
    rw [real_inner_self_eq_norm_sq]
    exact hy
  have hproj : tangentProjection y (tangentFrame y hy i)=tangentFrame y hy i := by
    rw [tangentProjection_eq_starProjection (by omega) y hsphere]
    exact (tangentPlane y).starProjection_eq_self_iff.mpr (tangentBasis y hy i).2
  filter_upwards [hnonzero] with J hJ
  intro hcrit
  have hd := inner_surfaceGradient (latitudeField c J w e q) y (tangentFrame y hy i)
  rw [hcrit, inner_zero_left, hproj, latitudeField_directional_derivative] at hd
  have hh : latitudeScale n q *
      tangentGradientCoordinates c (latitudeMap w e q y) (latitudeEmbeddedFrame e y hy) J i=0 := by
    simpa only [tangentGradientCoordinates, latitudeEmbeddedFrame, jet, iteratedFDeriv_one_apply,
      map_smul, smul_eq_mul] using hd.symm
  exact hJ ((mul_eq_zero.mp hh).resolve_left hs)

def actualLatitudeSphereCount {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (psi : Disorder (n+2) P → Vector (n+1) → ℝ≥0∞) (J : Disorder (n+2) P) : ℝ≥0∞ :=
  ∑' y : {y : Vector (n+1) | ‖y‖^2=((n+1 : ℕ) : ℝ) ∧
      surfaceGradient (latitudeField c J w e q) y=0}, psi J y

theorem actualLatitudeSphereCount_eq_chart_of_noncritical_pole {n P : ℕ}
    (c : Degree P → ℝ) (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (psi : Disorder (n+2) P → Vector (n+1) → ℝ≥0∞) (J : Disorder (n+2) P)
    (hpole : surfaceGradient (latitudeField c J w e q) (southPole n) ≠ 0) :
    actualLatitudeSphereCount c w e q psi J =
      actualLatitudeChartCount c w e q (fun J u => psi J (manuscriptChart n u)) J := by
  classical
  let C := {u : Vector n | u ∈ ball 0 2 ∧
    fderiv ℝ (fun y => field c J (affineChart n w e q y)) u=0}
  let S := {y : Vector (n+1) | ‖y‖^2=((n+1 : ℕ) : ℝ) ∧
    surfaceGradient (latitudeField c J w e q) y=0}
  have hcrit (u : Vector n) (hu : ‖u‖ < 2) :
      fderiv ℝ (fun y => field c J (affineChart n w e q y)) u=0 ↔
        surfaceGradient (latitudeField c J w e q) (manuscriptChart n u)=0 :=
    chart_critical_iff_intrinsic hu _ ((latitudeField_contDiff c J w e q).differentiable (by simp) _)
  let f : C → S := fun u => ⟨manuscriptChart n u,
    manuscriptChart_norm_sq (by simpa using u.property.1),
    (hcrit u (by simpa using u.property.1)).mp u.property.2⟩
  have hi : Injective f := by
    intro u v huv
    apply Subtype.ext
    exact manuscriptChart_injOn n u.property.1 v.property.1 (congrArg Subtype.val huv)
  have hsurj : Surjective f := by
    intro x
    have hxp : (x : Vector (n+1)) ≠ southPole n := by
      intro hxp
      apply hpole
      rw [← hxp]
      exact x.property.2
    have hx : (x : Vector (n+1)) ∈ manuscriptChart n '' ball (0 : Vector n) 2 := by
      rw [manuscriptChart_image_ball_except_pole]
      exact ⟨x.property.1, hxp⟩
    obtain ⟨u, hu, hux⟩ := hx
    have hz : fderiv ℝ (fun y => field c J (affineChart n w e q y)) u=0 := by
      apply (hcrit u (by simpa using hu)).mpr
      rw [hux]
      exact x.property.2
    exact ⟨⟨u, hu, hz⟩, Subtype.ext hux⟩
  let equiv : C ≃ S := Equiv.ofBijective f ⟨hi, hsurj⟩
  exact (equiv.tsum_eq (fun y : S => psi J y)).symm

/-- Actual global affine-sphere marked Kac--Rice under the original
disorder law; the chart-pole exception is removed internally by its genuine
Gaussian derivative law. -/
theorem actual_latitude_sphere_marked_kacRice {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (hfirst : 0 < firstCovariance c 1)
    (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| < 1)
    (psi : Disorder (n+2) P → Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (n+2) P × Vector (n+1) => psi z.1 z.2) :
    AEMeasurable (actualLatitudeSphereCount c w e q psi) (disorderLaw (n+2) P) ∧
    (∫⁻ J, actualLatitudeSphereCount c w e q psi J ∂disorderLaw (n+2) P) =
      ∫⁻ u in ball 0 2, GaussianRegression.observationPdf (affineChartGamma c w e q u) 0 *
        ENNReal.ofReal (manuscriptChartGram n u).det *
          ∫⁻ J, ENNReal.ofReal |(intrinsicHessian (latitudeField c J w e q) (manuscriptChart n u)).det| *
            psi J (manuscriptChart n u) ∂coefficientKernel (affineChartGamma c w e q u) 0 := by
  have hmchart : Measurable (manuscriptChart n) := by
    unfold manuscriptChart
    exact (((chartAmbientIsometry n).continuous.comp sphereChartND_continuous).const_smul
      (Real.sqrt (n+1 : ℕ))).measurable
  have hm : Measurable fun z : Disorder (n+2) P × Vector n => psi z.1 (manuscriptChart n z.2) :=
    hpsi.comp (measurable_fst.prodMk (hmchart.comp measurable_snd))
  have hk := actual_tensor_latitude_intrinsic_kacRice c hc hfirst w hw e he hq
    (fun J u => psi J (manuscriptChart n u)) hm
  have hpole := latitude_fixed_point_noncritical_ae hn c hc hfirst w hw e he hq
    (southPole n) (southPole_norm_sq n)
  have hcount : actualLatitudeSphereCount c w e q psi =ᵐ[disorderLaw (n+2) P]
      actualLatitudeChartCount c w e q (fun J u => psi J (manuscriptChart n u)) := by
    filter_upwards [hpole] with J hJ
    exact actualLatitudeSphereCount_eq_chart_of_noncritical_pole c w e q psi J hJ
  exact ⟨hk.1.congr hcount.symm, (lintegral_congr_ae hcount).trans hk.2⟩

end
end SlowEquilibration.SphericalLatitudeChartKacRice
