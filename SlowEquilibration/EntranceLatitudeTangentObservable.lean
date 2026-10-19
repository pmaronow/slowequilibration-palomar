-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.EntranceLatitudeConcentration
public import SlowEquilibration.SphereHessian
public import SlowEquilibration.SphericalGaussianJet
public import Mathlib.Analysis.Calculus.MeanValue

/-! The manuscript observable `V_x(u) = N^(-1/2) ⟨∇H_Q(u),x⟩`
is the actual tangential gradient of the ordered tensor field. Its boundedness
and latitude Lipschitz constants are derived from the genuine tensor
regularity event before consuming spherical concentration. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace
namespace SlowEquilibration.EntranceLatitudeTangentObservable
open SphericalModel SphericalForm SphericalGaussianJet SphereHessian
open EntranceLatitudeConcentration
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N P : ℕ}

/-- Both already constructed intrinsic gradients use the literal same
orthogonal projection; this is an equality of actual functions. -/
theorem tangentGradient_eq_surfaceGradient (c : Degree P → ℝ)
    (J : Disorder N P) (u : Vector N) :
    tangentGradient c J u = surfaceGradient (field c J) u := by
  unfold tangentGradient surfaceGradient
  rw [SphericalAging.LandscapeDerivatives.tangentProjection_apply,
    SphericalForm.tangentProjection_apply]

/-- The genuine center-field tangent observable of source equation 8.25. -/
def observable (c : Degree P → ℝ) (J : Disorder N P) (x u : Vector N) : ℝ :=
  (Real.sqrt (N : ℝ))⁻¹ * inner ℝ (surfaceGradient (field c J) u) x

theorem observable_continuous (c : Degree P → ℝ) (J : Disorder N P)
    (x : Vector N) : Continuous (observable c J x) := by
  have hg := (field_gradient_contDiff c J).continuous
  have hproj : Continuous (fun u : Vector N => surfaceGradient (field c J) u) := by
    simp only [surfaceGradient, SphericalForm.tangentProjection_apply,
      SphericalAging.HardSphereDynamics.projection]
    exact hg.sub (((continuous_id.inner hg).div_const (N : ℝ)).smul continuous_id)
  exact (hproj.inner continuous_const).const_mul _

theorem observable_abs_le (hN : 1 ≤ N) (c : Degree P → ℝ)
    (J : Disorder N P) (hJ : J ∈ regularDisorder)
    (x u : Vector N) (hx : ‖x‖^2 = (N : ℝ)) (hu : ‖u‖^2 = (N : ℝ)) :
    |observable c J x u| ≤ derivativeConstant c * Real.sqrt (N : ℝ) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hxn := SphericalAging.LandscapeDerivatives.sphere_norm x hx
  have hgrad := (field_regularDisorder_sphere_bounds hN c J hJ u hu).1
  rw [tangentGradient_eq_surfaceGradient] at hgrad
  unfold observable
  rw [abs_mul, abs_inv, abs_of_pos hs]
  calc
    _ ≤ (Real.sqrt (N : ℝ))⁻¹ *
        (derivativeConstant c * Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans (by
        rw [hxn]
        exact mul_le_mul_of_nonneg_right hgrad hs.le)) (inv_nonneg.mpr hs.le)
    _ = _ := by field_simp

/-- Moving the spherical projection has the precise chord-distance cost
`2 ‖z‖ / √N`, without any regularity or moment assumption. -/
theorem projection_difference_norm_le (hN : 1 ≤ N) (u v z : Vector N)
    (hu : ‖u‖^2 = (N : ℝ)) (hv : ‖v‖^2 = (N : ℝ)) :
    ‖tangentProjection u z - tangentProjection v z‖ ≤
      (2 * ‖z‖ / Real.sqrt (N : ℝ)) * ‖u-v‖ := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hsq := Real.sq_sqrt hNr.le
  have hun := SphericalAging.LandscapeDerivatives.sphere_norm u hu
  have hvn := SphericalAging.LandscapeDerivatives.sphere_norm v hv
  have he : tangentProjection u z - tangentProjection v z =
      -(inner ℝ u z / (N : ℝ)) • (u-v) -
        (inner ℝ (u-v) z / (N : ℝ)) • v := by
    simp only [SphericalForm.tangentProjection_apply,
      SphericalAging.HardSphereDynamics.projection, inner_sub_left,
      sub_div, smul_sub, sub_smul, neg_smul]
    module
  rw [he]
  calc
    _ ≤ ‖-(inner ℝ u z / (N : ℝ)) • (u-v)‖ +
        ‖(inner ℝ (u-v) z / (N : ℝ)) • v‖ := norm_sub_le _ _
    _ = |inner ℝ u z| / (N : ℝ) * ‖u-v‖ +
        |inner ℝ (u-v) z| / (N : ℝ) * Real.sqrt (N : ℝ) := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_neg, abs_div, abs_div, abs_of_pos hNr, hvn]
    _ ≤ (Real.sqrt (N : ℝ) * ‖z‖) / (N : ℝ) * ‖u-v‖ +
        (‖u-v‖ * ‖z‖) / (N : ℝ) * Real.sqrt (N : ℝ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (by simpa only [hun] using abs_real_inner_le_norm u z) hNr.le) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
          (abs_real_inner_le_norm (u-v) z) hNr.le) hs.le
    _ = (2 * ‖z‖ * ‖u-v‖) * (Real.sqrt (N : ℝ)/(N : ℝ)) := by ring
    _ = (2 * ‖z‖ * ‖u-v‖) * (Real.sqrt (N : ℝ))⁻¹ := by
      congr 1
      field_simp
      nlinarith [hsq]
    _ = _ := by ring

/-- The actual Euclidean gradient is Lipschitz on the full convex ball,
using the proved ordered tensor Hessian bound. -/
theorem gradient_difference_norm_le (hN : 1 ≤ N) (c : Degree P → ℝ)
    (J : Disorder N P) (hJ : J ∈ regularDisorder) (u v : Vector N)
    (hu : ‖u‖ ≤ Real.sqrt (N : ℝ)) (hv : ‖v‖ ≤ Real.sqrt (N : ℝ)) :
    ‖gradient (field c J) u - gradient (field c J) v‖ ≤
      derivativeConstant c * ‖u-v‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => (field_gradient_contDiff c J).differentiable (by simp) y)
    (fun y hy => ?_) (convex_closedBall (0 : Vector N) (Real.sqrt (N : ℝ)))
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hu)
  rw [SphericalAging.LandscapeDerivatives.gradient_derivative_norm]
  exact (field_regularDisorder_ball_bounds hN c J hJ y
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)).2.2.1

/-- The literal intrinsic gradient has the manuscript's constant `3C`
in Euclidean chord distance on the original sphere. -/
theorem surfaceGradient_difference_norm_le (hN : 1 ≤ N) (c : Degree P → ℝ)
    (J : Disorder N P) (hJ : J ∈ regularDisorder) (u v : Vector N)
    (hu : ‖u‖^2 = (N : ℝ)) (hv : ‖v‖^2 = (N : ℝ)) :
    ‖surfaceGradient (field c J) u - surfaceGradient (field c J) v‖ ≤
      (3 * derivativeConstant c) * ‖u-v‖ := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hun := SphericalAging.LandscapeDerivatives.sphere_norm u hu
  have hvn := SphericalAging.LandscapeDerivatives.sphere_norm v hv
  have hg := (field_regularDisorder_ball_bounds hN c J hJ v hvn.le).2.1
  have hd := gradient_difference_norm_le hN c J hJ u v hun.le hvn.le
  have hp := tangentProjection_norm_le (by omega : N ≠ 0) u
    ((SphericalAging.HardSphereDynamics.onSphere_iff_norm_sq u).mpr hu)
  have he : surfaceGradient (field c J) u - surfaceGradient (field c J) v =
      tangentProjection u (gradient (field c J) u-gradient (field c J) v) +
      (tangentProjection u (gradient (field c J) v)-tangentProjection v (gradient (field c J) v)) := by
    simp only [surfaceGradient,map_sub]
    module
  rw [he]
  calc
    _ ≤ ‖tangentProjection u (gradient (field c J) u-gradient (field c J) v)‖ +
        ‖tangentProjection u (gradient (field c J) v)-tangentProjection v (gradient (field c J) v)‖ := norm_add_le _ _
    _ ≤ derivativeConstant c * ‖u-v‖ + (2 * ‖gradient (field c J) v‖ / Real.sqrt (N : ℝ)) * ‖u-v‖ :=
      add_le_add (((tangentProjection u).le_opNorm _).trans
        ((mul_le_of_le_one_left (norm_nonneg _) hp).trans hd))
        (projection_difference_norm_le hN u v _ hu hv)
    _ ≤ derivativeConstant c * ‖u-v‖ + (2 * derivativeConstant c) * ‖u-v‖ := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (div_le_iff₀ hs).mpr
      nlinarith
    _ = _ := by ring

theorem observable_lipschitzOn (hN : 1 ≤ N) (c : Degree P → ℝ)
    (J : Disorder N P) (hJ : J ∈ regularDisorder) (x : Vector N)
    (hx : ‖x‖^2 = (N : ℝ)) :
    LipschitzOnWith (3 * derivativeConstant c).toNNReal (observable c J x)
      {u | ‖u‖^2 = (N : ℝ)} := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hC : 0 ≤ derivativeConstant c := (derivativeConstant_pos c).le
  have hxn := SphericalAging.LandscapeDerivatives.sphere_norm x hx
  apply LipschitzOnWith.of_dist_le_mul
  intro u hu v hv
  rw [Real.coe_toNNReal _ (by positivity),dist_eq_norm,dist_eq_norm]
  have he : observable c J x u-observable c J x v =
      (Real.sqrt (N : ℝ))⁻¹ * inner ℝ (surfaceGradient (field c J) u-surfaceGradient (field c J) v) x := by
    simp only [observable,inner_sub_left]
    ring
  rw [he,Real.norm_eq_abs,abs_mul,abs_inv,abs_of_pos hs]
  calc
    _ ≤ (Real.sqrt (N : ℝ))⁻¹ * ((3 * derivativeConstant c) * ‖u-v‖ * Real.sqrt (N : ℝ)) :=
      mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans (by
        rw [hxn]
        exact mul_le_mul_of_nonneg_right (surfaceGradient_difference_norm_le hN c J hJ u v hu hv) hs.le))
        (inv_nonneg.mpr hs.le)
    _ = _ := by field_simp

/-- Actual concentration of the frozen-field gradient observable on the
original latitude law. Every boundedness and Lipschitz premise of the
concentration theorem has been proved from the ordered tensor event. -/
theorem observable_centered_mgf_le {n : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n+1) P) (hJ : J ∈ regularDisorder)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y, inner ℝ (e y) x=0)
    {r : ℝ} (hr : |r| ≤ 1) (t : ℝ) :
    mgf (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (latitudeLaw x e r) t ≤
      Real.exp (|t| * (2 * derivativeConstant c * Real.sqrt ((n+1 : ℕ) : ℝ) *
        Real.exp (-(n : ℝ)/8)) + 288 * (derivativeConstant c)^2 * t^2) +
      Real.exp (2 * derivativeConstant c * Real.sqrt ((n+1 : ℕ) : ℝ) * |t| - (n : ℝ)/8) := by
  have hC : 0 ≤ derivativeConstant c := (derivativeConstant_pos c).le
  have hL := (observable_lipschitzOn (by omega) c J hJ x hx).mono
    (show {u : Vector (n+1) | ‖u‖^2=((n+1 : ℕ) : ℝ) ∧ overlap u x=r} ⊆
      {u | ‖u‖^2=((n+1 : ℕ) : ℝ)} from fun _ h => h.1)
  have hbound := latitude_observable_centered_mgf_le hn x hx e he hr
    (observable c J x) (observable_continuous c J x).measurable
    (3 * derivativeConstant c).toNNReal hL
    (show 0 ≤ derivativeConstant c * Real.sqrt ((n+1 : ℕ) : ℝ) by positivity)
    (fun u hu _ => observable_abs_le (by omega) c J hJ x u hx hu) t
  have hLsq : 32 * ((3 * derivativeConstant c).toNNReal : ℝ)^2 * t^2=
      288 * (derivativeConstant c)^2 * t^2 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    ring
  simpa only [hLsq,mul_assoc] using hbound

/-- Source specialization with the actual center coefficients, including
all physical mixture blocks and the exact normalization `N^(-1/2)`. -/
theorem center_observable_centered_mgf_le {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) (Q : ℝ) (J : Disorder (n+1) μ.maxDegree)
    (hJ : J ∈ regularDisorder) (x : Vector (n+1))
    (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y, inner ℝ (e y) x=0)
    {r : ℝ} (hr : |r| ≤ 1) (t : ℝ) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    mgf (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (latitudeLaw x e r) t ≤
      Real.exp (|t| * (2 * derivativeConstant c * Real.sqrt ((n+1 : ℕ) : ℝ) *
        Real.exp (-(n : ℝ)/8)) + 288 * (derivativeConstant c)^2 * t^2) +
      Real.exp (2 * derivativeConstant c * Real.sqrt ((n+1 : ℕ) : ℝ) * |t| - (n : ℝ)/8) :=
  observable_centered_mgf_le hn _ J hJ x hx e he hr t

end SlowEquilibration.EntranceLatitudeTangentObservable
