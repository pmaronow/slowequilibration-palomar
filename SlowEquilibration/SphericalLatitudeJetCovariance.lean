-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalDirectionalJetCovariance
public import SlowEquilibration.SphericalLatitudeActualKacRice

@[expose] public section

/-! Exact first-jet marks of the genuine affine latitude field. Its radial
direction is the affine section's radial direction, rather than the ambient
radius vector. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set InnerProductSpace
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeRadialVector {n : ℕ} (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2))
    (q : ℝ) (y : Vector (n+1)) : Vector (n+2) := latitudeScale n q • e y

theorem latitudeScale_sq {n : ℕ} {q : ℝ} (hq : |q| ≤ 1) :
    (latitudeScale n q)^2 = ((n+2 : ℕ) : ℝ)/((n+1 : ℕ) : ℝ)*(1-q^2) := by
  apply Real.sq_sqrt
  have hq2 : 0 ≤ 1-q^2 := by nlinarith [(abs_le.mp hq).1, (abs_le.mp hq).2]
  positivity

theorem latitudeMap_hasFDerivAt {n : ℕ} (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (y : Vector (n+1)) :
    HasFDerivAt (latitudeMap w e q) (latitudeScale n q • e.toContinuousLinearMap) y := by
  convert (e.toContinuousLinearMap.hasFDerivAt.const_smul (latitudeScale n q)).const_add (q • w) using 1
  · funext z
    rfl

theorem latitudeField_directional_derivative {n P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n+2) P) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ) (y v : Vector (n+1)) :
    fderiv ℝ (latitudeField c J w e q) y v =
      jet c 1 (latitudeMap w e q y) (fun _ => latitudeScale n q • e v) J := by
  have hd := ((field_contDiff c J).differentiable (by simp)
    (latitudeMap w e q y)).hasFDerivAt.comp y (latitudeMap_hasFDerivAt w e q y)
  change fderiv ℝ (field c J ∘ latitudeMap w e q) y v = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, LinearIsometry.coe_toContinuousLinearMap,
    jet, iteratedFDeriv_one_apply]

theorem latitudeRadialVector_norm_sq {n : ℕ}
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) {q : ℝ} (hq : |q| ≤ 1)
    (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    ‖latitudeRadialVector e q y‖^2 = ((n+2 : ℕ) : ℝ)*(1-q^2) := by
  simp only [latitudeRadialVector, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, e.norm_map,
    hy, latitudeScale_sq hq]
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem latitudeMap_inner_radial {n : ℕ} (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    inner ℝ (latitudeMap w e q y) (latitudeRadialVector e q y) =
      ((n+2 : ℕ) : ℝ)*(1-q^2) := by
  have hzero : inner ℝ w (e y)=0 := by rw [real_inner_comm, he]
  change inner ℝ (q • w+latitudeScale n q • e y) (latitudeScale n q • e y) = _
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_right, hzero,
    mul_zero, mul_zero, zero_add, real_inner_smul_left, real_inner_smul_right,
    e.inner_map_map, real_inner_self_eq_norm_sq, hy]
  rw [← mul_assoc, ← sq, latitudeScale_sq hq]
  have hn : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

/-- The actual value/radial covariance matrix of the affine latitude
field, derived from the original Gaussian tensor law. -/
theorem latitude_value_radial_covariances {n P : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (w : Vector (n+2)) (hw : ‖w‖^2=((n+2 : ℕ) : ℝ))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (he : ∀ x, inner ℝ (e x) w=0)
    {q : ℝ} (hq : |q| ≤ 1) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ)) :
    let x := latitudeMap w e q y
    let v := latitudeRadialVector e q y
    cov[jet c 0 x (fun i => Fin.elim0 i), jet c 0 x (fun i => Fin.elim0 i); disorderLaw (n+2) P] =
      ((n+2 : ℕ) : ℝ)*covariancePolynomial c 1 ∧
    cov[jet c 0 x (fun i => Fin.elim0 i), jet c 1 x (fun _ => v); disorderLaw (n+2) P] =
      ((n+2 : ℕ) : ℝ)*(1-q^2)*firstCovariance c 1 ∧
    cov[jet c 1 x (fun _ => v), jet c 1 x (fun _ => v); disorderLaw (n+2) P] =
      ((n+2 : ℕ) : ℝ)*((1-q^2)*firstCovariance c 1+(1-q^2)^2*secondCovariance c 1) := by
  dsimp only
  have hx := latitudeMap_norm_sq (by omega) w hw e he hq y hy
  have hiv := latitudeMap_inner_radial w e he hq y hy
  have hv := latitudeRadialVector_norm_sq e hq y hy
  have hvi : inner ℝ (latitudeRadialVector e q y) (latitudeMap w e q y) =
      ((n+2 : ℕ) : ℝ)*(1-q^2) := by
    rw [real_inner_comm]
    exact hiv
  have hN : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · change cov[fun J => field c J (latitudeMap w e q y),
      fun J => field c J (latitudeMap w e q y); disorderLaw (n+2) P] = _
    rw [field_covariance (by omega) c hc, overlap_self (by omega) _ hx]
  · rw [value_directional_covariance (by omega) c hc _ _ hx, hiv]
    ring
  · rw [directional_gradient_covariance (by omega) c hc _ _ _ hx,
      real_inner_self_eq_norm_sq, hv, hiv, hvi]
    simp only [show n+1+1=n+2 by omega]
    field_simp

end
end SlowEquilibration.SphericalLatitudeChartKacRice
