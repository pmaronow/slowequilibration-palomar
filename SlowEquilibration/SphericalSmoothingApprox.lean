module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalSmoothing

@[expose] public section

/-! # Actual uniform approximation by the normalized spherical kernels -/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped InnerProductSpace Topology ContDiff

/-- A concrete point on the actual radius-sqrt(N) sphere. -/
def sphereReferencePoint {N : ℕ} (hN : 1 ≤ N) : Vector N :=
  Real.sqrt N • basisVector ⟨0, by omega⟩

lemma sphereReferencePoint_onSphere {N : ℕ} (hN : 1 ≤ N) : OnSphere (sphereReferencePoint hN) := by
  rw [onSphere_iff_norm_sq]
  simp only [sphereReferencePoint, norm_smul, basisVector, EuclideanSpace.norm_single,
    norm_one, mul_one, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The actual positive kernel normalization. -/
def sphereSmoothingMass {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) : ℝ :=
  ∫ y, sphereSmoothingKernel ε (sphereReferencePoint hN) y ∂sphereLaw N

lemma sphereSmoothingMass_pos {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) : 0 < sphereSmoothingMass hN ε :=
  sphereSmoothingKernel_row_integral_pos hN ε _ (sphereReferencePoint_onSphere hN)

lemma sphereSmoothingKernel_row_mass {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) (x : Vector N)
    (hx : OnSphere x) : (∫ y, sphereSmoothingKernel ε x y ∂sphereLaw N) = sphereSmoothingMass hN ε := by
  apply sphereSmoothingKernel_row_integral_eq
  exact (SphericalAging.LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)).trans
    (SphericalAging.LandscapeDerivatives.sphere_norm _
      ((onSphere_iff_norm_sq _).mp (sphereReferencePoint_onSphere hN))).symm

/-- The true normalized averaging of an ambient continuous observable. -/
def sphericalSmoothObservable {N : ℕ} (hN : 1 ≤ N) (ε : ℝ) (p : Vector N → ℝ)
    (x : Vector N) : ℝ := (sphereSmoothingMass hN ε)⁻¹ * sphereSmoothingMoment (sphereLaw N) ε p x

lemma sphericalSmoothObservable_contDiff_one {N : ℕ} (hN : 1 ≤ N) {ε : ℝ} (hε : 0 < ε)
    {p : Vector N → ℝ} (hp : Continuous p) : ContDiff ℝ 1 (sphericalSmoothObservable hN ε p) :=
  contDiff_const.mul (sphereSmoothingMoment_contDiff_one (integrable_sphere_of_continuous hN hp) hε)

/-- The actual normalized spherical kernel error is bounded by the true
modulus of continuity on its support. -/
theorem sphericalSmoothObservable_error_le {N : ℕ} (hN : 1 ≤ N) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 ≤ δ) {p : Vector N → ℝ} (hp : Continuous p)
    (y : Vector N) (hy : OnSphere y)
    (hmod : ∀ x, OnSphere x → dist x y < ε → |p x - p y| ≤ δ) :
    |sphericalSmoothObservable hN ε p y - p y| ≤ δ := by
  let m := sphereSmoothingMass hN ε
  have hm : 0 < m := sphereSmoothingMass_pos hN ε
  have hK := sphereSmoothingKernel_integrable ε y
  have hi : Integrable (fun x => p x * sphereSmoothingKernel ε y x) (sphereLaw N) :=
    sphereSmoothingMoment_integrable (integrable_sphere_of_continuous hN hp) ε y
  have hq : Integrable (fun x => (p x - p y) * sphereSmoothingKernel ε y x) (sphereLaw N) :=
    sphereSmoothingMoment_integrable (integrable_sphere_of_continuous hN (hp.sub continuous_const)) ε y
  have he : sphericalSmoothObservable hN ε p y - p y =
      m⁻¹ * ∫ x, (p x - p y) * sphereSmoothingKernel ε y x ∂sphereLaw N := by
    rw [show (fun x => (p x - p y) * sphereSmoothingKernel ε y x) =
      (fun x => p x * sphereSmoothingKernel ε y x - p y * sphereSmoothingKernel ε y x) by funext x; ring,
      integral_sub hi (hK.const_mul _), integral_const_mul, sphereSmoothingKernel_row_mass hN ε y hy]
    dsimp [sphericalSmoothObservable, sphereSmoothingMoment, m]
    field_simp [(sphereSmoothingMass_pos hN ε).ne']
    <;> ring
  have hb : ∀ᵐ x ∂sphereLaw N,
      ‖(p x - p y) * sphereSmoothingKernel ε y x‖ ≤ δ * sphereSmoothingKernel ε y x := by
    filter_upwards [sphereLaw_support hN] with x hx
    have hxs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
    by_cases hd : ε ≤ dist x y
    · rw [sphereSmoothingKernel_zero_of_dist hε y x (by simpa only [dist_comm] using hd)]
      simp
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (sphereSmoothingKernel_nonneg ε y x)]
      exact mul_le_mul_of_nonneg_right (hmod x hxs (lt_of_not_ge hd)) (sphereSmoothingKernel_nonneg ε y x)
  have hnorm : ‖∫ x, (p x - p y) * sphereSmoothingKernel ε y x ∂sphereLaw N‖ ≤ δ * m := by
    calc
      _ ≤ ∫ x, ‖(p x - p y) * sphereSmoothingKernel ε y x‖ ∂sphereLaw N := norm_integral_le_integral_norm _
      _ ≤ ∫ x, δ * sphereSmoothingKernel ε y x ∂sphereLaw N := integral_mono_ae hq.norm (hK.const_mul δ) hb
      _ = _ := by rw [integral_const_mul, sphereSmoothingKernel_row_mass hN ε y hy]
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr hm)]
  calc
    _ ≤ m⁻¹ * (δ * m) := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hm.le)
    _ = δ := by field_simp [hm.ne']

/-- Genuine uniform approximation on the compact actual sphere as the
width tends to zero. -/
theorem sphericalSmoothObservable_uniform_approx {N : ℕ} (hN : 1 ≤ N)
    {p : Vector N → ℝ} (hp : Continuous p) (δ : ℝ) (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ ε, 0 < ε → ε < r →
      ∀ y, OnSphere y → |sphericalSmoothObservable hN ε p y - p y| < δ := by
  let S := Metric.sphere (0 : Vector N) (Real.sqrt N)
  have hu : UniformContinuousOn p S := (isCompact_sphere (0 : Vector N) (Real.sqrt N)).uniformContinuousOn_of_continuous hp.continuousOn
  obtain ⟨r, hr, hmod⟩ := Metric.uniformContinuousOn_iff.mp hu (δ / 2) (half_pos hδ)
  refine ⟨r, hr, ?_⟩
  intro ε hε her y hy
  apply (sphericalSmoothObservable_error_le hN hε (half_pos hδ).le hp y hy ?_).trans_lt (by linarith)
  intro x hx hxy
  have hm (z : Vector N) (hz : OnSphere z) : z ∈ S := by
    simpa only [S, Metric.mem_sphere, dist_zero_right] using
      SphericalAging.LandscapeDerivatives.sphere_norm z ((onSphere_iff_norm_sq z).mp hz)
  have hh := hmod x (hm x hx) y (hm y hy) (hxy.trans her)
  simpa only [Real.dist_eq] using hh.le

end
end SlowEquilibration.SphericalForm
