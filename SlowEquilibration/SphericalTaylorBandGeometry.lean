-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorResidualKernel
public import SlowEquilibration.SphericalLatitudeTransport
public import SlowEquilibration.SphericalLatitudeSequentialRegression

@[expose] public section

/-! Literal transverse bands through an affine-latitude critical point,
including their original-sphere geometry and every-target posterior field
identity. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicHessianLaw
open SlowEquilibration.SphericalLatitudeChartKacRice SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalSequentialRegression
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def bottomTransverseFrame {n : ℕ} (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2))
    (y : Vector (n+1)) : Vector n →ₗᵢ[ℝ] Vector (n+2) := e.comp (latitudeFrameAt y)

theorem bottomTransverseFrame_reference_orthogonal {n : ℕ} (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ v,inner ℝ (e v) w=0)
    (y : Vector (n+1)) (z : Vector n) : inner ℝ (bottomTransverseFrame e y z) w=0 :=
  he _

theorem bottomTransverseFrame_center_orthogonal {n : ℕ} (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ v,inner ℝ (e v) w=0)
    (q : ℝ) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (z : Vector n) :
    inner ℝ (bottomTransverseFrame e y z) (latitudeMap w e q y)=0 := by
  change inner ℝ (e (latitudeFrameAt y z)) (latitudeMap w e q y)=0
  simp only [latitudeMap,inner_add_right,
    real_inner_smul_right,he,e.inner_map_map,latitudeFrameAt_orthogonal y hy,mul_zero,add_zero]

def transverseBandPoint {N d : ℕ} (m : Vector N) (e : Vector d →ₗᵢ[ℝ] Vector N)
    (q : ℝ) (y : Vector d) : Vector N := Real.sqrt q • (m+transverseOffset e q y)

theorem transverseOffset_norm_sq {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (e : Vector d →ₗᵢ[ℝ] Vector N) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (y : Vector d) (hy : ‖y‖^2=(d : ℝ)) :
    ‖transverseOffset e q y‖^2=(N : ℝ)*((1-q)/q) := by
  rw [← real_inner_self_eq_norm_sq,transverseOffset_inner hN hd e hq,
    overlap_self hd y hy,mul_one]

theorem transverseBandPoint_norm_sq {N d : ℕ} (hN : 0 < N) (hd : 0 < d)
    (m : Vector N) (hm : ‖m‖^2=(N : ℝ)) (e : Vector d →ₗᵢ[ℝ] Vector N)
    (he : ∀ y,inner ℝ (e y) m=0) {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (y : Vector d) (hy : ‖y‖^2=(d : ℝ)) : ‖transverseBandPoint m e q y‖^2=(N : ℝ) := by
  have hz := transverseOffset_tangent m e he q y
  have hz' : inner ℝ m (transverseOffset e q y)=0 := by rw [real_inner_comm]; exact hz
  rw [transverseBandPoint,← real_inner_self_eq_norm_sq,real_inner_smul_left,real_inner_smul_right,
    ← mul_assoc,← pow_two,Real.sq_sqrt hq.1.le,inner_add_left,inner_add_right,inner_add_right,
    hz,hz',add_zero,zero_add,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    hm,transverseOffset_norm_sq hN hd e hq y hy]
  field_simp [hq.1.ne']
  ring

theorem transverseBandPoint_reference_overlap {N d : ℕ} (w m : Vector N)
    (e : Vector d →ₗᵢ[ℝ] Vector N) (he : ∀ y,inner ℝ (e y) w=0)
    (q : ℝ) (y : Vector d) :
    overlap (transverseBandPoint m e q y) w=Real.sqrt q*overlap m w := by
  simp only [transverseBandPoint,transverseOffset,overlap,real_inner_smul_left,
    inner_add_left,he,mul_zero,add_zero]
  ring

/-- Actual criticality removes the full linear term on the transverse
subspace, not merely on a selected finite collection of directions. -/
theorem latitude_critical_transverse_derivative_zero {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) {q : ℝ} (hq : |q|<1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (hcrit : surfaceGradient (latitudeField c J w e q) y=0) (z : Vector n) :
    fderiv ℝ (field c J) (latitudeMap w e q y) (bottomTransverseFrame e y z)=0 := by
  have hsphere : OnSphere y := by
    change inner ℝ y y=_
    rw [real_inner_self_eq_norm_sq]
    exact hy
  have hp : tangentProjection y (latitudeFrameAt y z)=latitudeFrameAt y z := by
    rw [tangentProjection_eq_starProjection (by omega) y hsphere]
    apply (tangentPlane y).starProjection_eq_self_iff.mpr
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [real_inner_comm]
    exact latitudeFrameAt_orthogonal y hy z
  have h := inner_surfaceGradient (latitudeField c J w e q) y (latitudeFrameAt y z)
  rw [hcrit,inner_zero_left,hp,latitudeField_directional_derivative] at h
  have hs : latitudeScale n q ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have hq2 : 0<1-q^2 := by nlinarith [(abs_lt.mp hq).1,(abs_lt.mp hq).2]
    exact mul_pos (div_pos (by positivity) (by positivity)) hq2
  simp only [jet,iteratedFDeriv_one_apply,map_smul,smul_eq_mul] at h
  change 0=latitudeScale n q*fderiv ℝ (field c J) (latitudeMap w e q y)
    (bottomTransverseFrame e y z) at h
  exact (mul_eq_zero.mp h.symm).resolve_left hs

/-- The genuine posterior is supported on one simultaneous identity for
all points of the transverse band. -/
theorem latitude_posterior_transverse_field_identity {n : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ v,inner ℝ (e v) w=0)
    {q : ℝ} (hq0 : q≠0) (hq1 : |q|<1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) (b : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    ∀ᵐ J ∂coefficientKernel (latitudeJointCLM c w e q y hy) (jointScoreTarget n b),
      ∀ z : Vector n, fieldOfMixture μ J
        (transverseBandPoint (latitudeMap w e q y) (bottomTransverseFrame e y) Q z)=
        b 0+taylorRemainderCLM c (latitudeMap w e q y)
          (transverseOffset (bottomTransverseFrame e y) Q z) (euclideanDisorder J) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  filter_upwards [coefficientKernel_observation_ae _
    (center_latitudeJointCLM_surjective μ hQ w hw e he hq0 hq1 y hy) (jointScoreTarget n b)] with J hJ
  have hv : field c J (latitudeMap w e q y)=b 0 := by
    simpa only [actualObservation,latitudeJointCLM_apply_inl,latitudeScoreCLM_apply_zero,
      flatJetCLM_apply,unpack_euclideanDisorder,jet,iteratedFDeriv_zero_apply,jointScoreTarget,
      Sum.elim_inl,c] using
      congrArg (fun v => v (Sum.inl (0 : Fin 2))) hJ
  have hg : gradientCLM c (latitudeMap w e q y) (latitudeGradientDirections e q y hy)
      (euclideanDisorder J)=0 := by
    apply PiLp.ext
    intro i
    exact congrArg (fun v => v (Sum.inr i)) hJ
  have hcrit := (latitude_gradient_zero_iff_intrinsic c w e q y hy (euclideanDisorder J)).mp hg
  simp only [unpack_euclideanDisorder] at hcrit
  intro z
  have hd := latitude_critical_transverse_derivative_zero c J w e hq1 y hy hcrit z
  rw [taylorRemainderCLM_actual,transverseOffset,map_smul,hd,smul_zero,sub_zero,hv]
  have hf := field_center_scale (c := mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) hQ.le J
    (latitudeMap w e q y+transverseOffset (bottomTransverseFrame e y) Q z)
  change _=b 0+(field c J _-b 0)
  rw [add_sub_cancel]
  exact hf.symm

end
end SlowEquilibration.SphericalTaylorRemainder
