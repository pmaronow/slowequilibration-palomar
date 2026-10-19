-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceSphereLogSobolev
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
public import Mathlib.Analysis.Calculus.Rademacher

/-! Further analytic steps toward Section 8, `lem:ent-lsi`.
The angular Gaussian lift has the sharp local derivative bound, with no
loss in the Lipschitz constant. Its Gaussian Dirichlet energy is finite
in dimensions at least three. The singularity at the origin has vanishing
localized energy. The real-variable entropy/Fisher implication of
curvature dissipation is also proved.

This module does not assert the missing Gaussian logarithmic Sobolev
inequality or the existence and convergence of the required spherical
heat flow. In particular, the global `BakryEmerySphereLogSobolev`
interface is not yet discharged here.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceSphereLogSobolevFinal

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceSphereSharpConcentration SourceSphereLogSobolev
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- A sharp infinitesimal bound for the angle from a nonzero vector.
The denominator tends to `‖x‖`, rather than losing a fixed geometric factor. -/
theorem angle_le_norm_sub_div
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (hxy : ‖y - x‖ < ‖x‖) :
    InnerProductGeometry.angle x y ≤ ‖y - x‖ / (‖x‖ - ‖y - x‖) := by
  have hr : 0 < ‖x‖ := lt_of_le_of_lt (norm_nonneg (y - x)) hxy
  let u : E := ‖x‖⁻¹ • x
  let a : ℝ := inner ℝ u y
  let w : E := y - a • u
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, hr.ne']
  have hux : ‖x‖ • u = x := by
    simp [u, smul_smul, hr.ne']
  have huxinner : inner ℝ u x = ‖x‖ := by
    calc
      inner ℝ u x = inner ℝ u (‖x‖ • u) :=
        congrArg (fun z : E => inner ℝ u z) hux.symm
      _ = ‖x‖ := by rw [inner_smul_right, real_inner_self_eq_norm_sq, hu]; ring
  have ha_bound : ‖x‖ - ‖y - x‖ ≤ a := by
    have hc := (abs_le.mp (abs_real_inner_le_norm u (y - x))).1
    rw [inner_sub_right, hu, one_mul, huxinner] at hc
    change -‖y - x‖ ≤ a - ‖x‖ at hc
    linarith
  have ha : 0 < a := lt_of_lt_of_le (sub_pos.mpr hxy) ha_bound
  have hyu : inner ℝ y u = a := (real_inner_comm y u).symm
  have hw_sq : ‖w‖ ^ 2 = ‖y‖ ^ 2 - a ^ 2 := by
    dsimp only [w]
    rw [norm_sub_sq_real, inner_smul_right, hyu, norm_smul,
      Real.norm_eq_abs, abs_of_pos ha, hu]
    ring
  have hyx : inner ℝ y x = ‖x‖ * a := by
    calc
      inner ℝ y x = inner ℝ y (‖x‖ • u) :=
        congrArg (fun z : E => inner ℝ y z) hux.symm
      _ = ‖x‖ * a := by rw [inner_smul_right, hyu]
  have hd_sq : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * (‖x‖ * a) + ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, hyx]
  have hw_le : ‖w‖ ≤ ‖y - x‖ := by
    apply (sq_le_sq₀ (norm_nonneg w) (norm_nonneg (y - x))).mp
    nlinarith only [hw_sq, hd_sq, sq_nonneg (‖x‖ - a)]
  have how : inner ℝ (a • u) w = 0 := by
    dsimp only [w]
    rw [real_inner_smul_left, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, hu]
    change a * (a - a * (1 : ℝ) ^ 2) = 0
    ring
  have hau : ‖a • u‖ = a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hu, mul_one]
  have hau0 : a • u ≠ 0 := norm_ne_zero_iff.mp (by rw [hau]; exact ha.ne')
  have hy : a • u + w = y := by dsimp only [w]; abel
  have hangle : InnerProductGeometry.angle x y = Real.arctan (‖w‖ / a) := by
    calc
      InnerProductGeometry.angle x y = InnerProductGeometry.angle u y := by
        exact (InnerProductGeometry.angle_smul_left_of_pos x y (inv_pos.mpr hr)).symm
      _ = InnerProductGeometry.angle (a • u) y :=
        (InnerProductGeometry.angle_smul_left_of_pos u y ha).symm
      _ = InnerProductGeometry.angle (a • u) (a • u + w) := by rw [hy]
      _ = Real.arctan (‖w‖ / a) := by
        rw [InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero how hau0, hau]
  rw [hangle]
  calc
    Real.arctan (‖w‖ / a) ≤ ‖w‖ / a :=
      Real.arctan_le_self (div_nonneg (norm_nonneg w) ha.le)
    _ ≤ ‖y - x‖ / a := div_le_div_of_nonneg_right hw_le ha.le
    _ ≤ ‖y - x‖ / (‖x‖ - ‖y - x‖) :=
      div_le_div_of_nonneg_left (norm_nonneg (y - x)) (sub_pos.mpr hxy) ha_bound

/-- The angular lift used in the Gaussian projection proof. -/
def angularLift {n : ℕ} (g : Vector n → ℝ) (x : Vector n) : ℝ :=
  g (‖x‖⁻¹ • x)

/-- The derivative of a degree-zero homogeneous angular lift at the
origin is zero. If the lift fails to be differentiable there, this is
the convention in `fderiv`; if it is differentiable, homogeneity forces it. -/
theorem angularLift_fderiv_zero {n : ℕ} (g : Vector n → ℝ) :
    fderiv ℝ (angularLift g) 0 = 0 := by
  let F := angularLift g
  by_cases hd : DifferentiableAt ℝ F 0
  · have he : (fun z : Vector n => F ((2 : ℝ) • z)) = F := by
      funext z
      change g (NormedSpace.normalize ((2 : ℝ) • z)) = g (NormedSpace.normalize z)
      rw [NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hs : HasFDerivAt (fun z : Vector n => (2 : ℝ) • z)
        ((2 : ℝ) • ContinuousLinearMap.id ℝ (Vector n)) 0 :=
      (hasFDerivAt_id (0 : Vector n)).const_smul (2 : ℝ)
    have hd' : HasFDerivAt F (fderiv ℝ F 0) ((2 : ℝ) • (0 : Vector n)) := by
      simpa only [smul_zero] using hd.hasFDerivAt
    have hc := hd'.comp 0 hs
    change HasFDerivAt (fun z => F ((2 : ℝ) • z)) _ _ at hc
    rw [he] at hc
    have hh : HasFDerivAt F ((2 : ℝ) • fderiv ℝ F 0) 0 := by
      simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id] using hc
    have hEq := hh.fderiv
    ext z
    have hz := congrArg (fun A : Vector n →L[ℝ] ℝ => A z) hEq
    simp only [smul_apply, smul_eq_mul] at hz
    change fderiv ℝ F 0 z = 0
    linarith
  · exact fderiv_zero_of_not_differentiableAt hd

private theorem angularLift_sub_le {n : ℕ} {g : Vector n → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) (x y : Vector n)
    (hxy : ‖y - x‖ < ‖x‖) :
    |angularLift g y - angularLift g x| ≤ L * (‖y - x‖ / (‖x‖ - ‖y - x‖)) := by
  have hx : x ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg _) hxy)
  have hy : y ≠ 0 := by
    intro hy
    simp [hy] at hxy
  have hu := hg (NormedSpace.normalize y) (NormedSpace.normalize x)
    (NormedSpace.norm_normalize hy) (NormedSpace.norm_normalize hx)
  have ha : Real.arccos
      (inner ℝ (NormedSpace.normalize y) (NormedSpace.normalize x)) =
      InnerProductGeometry.angle x y := by
    calc
      _ = InnerProductGeometry.angle (NormedSpace.normalize y) (NormedSpace.normalize x) := by
        simp [InnerProductGeometry.angle, NormedSpace.norm_normalize hy,
          NormedSpace.norm_normalize hx]
      _ = InnerProductGeometry.angle y x := by simp
      _ = InnerProductGeometry.angle x y := InnerProductGeometry.angle_comm y x
  rw [ha] at hu
  exact hu.trans (mul_le_mul_of_nonneg_left (angle_le_norm_sub_div x y hxy) hL)

/-- The sharp angular-gradient bound needed for Gaussian projection.
It holds for every geodesically Lipschitz observable admitted by the
original interface, without a smoothness assumption. -/
theorem angularLift_fderiv_norm_le {n : ℕ} {g : Vector n → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) (x : Vector n) (hx : x ≠ 0) :
    ‖fderiv ℝ (angularLift g) x‖ ≤ L / ‖x‖ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hlocal (δ : ℝ) (hδ : 0 < δ) (hδr : δ < ‖x‖) :
      ‖fderiv ℝ (angularLift g) x‖ ≤ L / (‖x‖ - δ) := by
    apply norm_fderiv_le_of_lip' ℝ (div_nonneg hL (sub_pos.mpr hδr).le)
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
    have hyd : ‖y - x‖ < δ := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    rw [Real.norm_eq_abs]
    calc
      |angularLift g y - angularLift g x| ≤ L * (‖y - x‖ / (‖x‖ - ‖y - x‖)) :=
        angularLift_sub_le hL hg x y (hyd.trans hδr)
      _ ≤ L * (‖y - x‖ / (‖x‖ - δ)) := by
        apply mul_le_mul_of_nonneg_left _ hL
        exact div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hδr) (by linarith)
      _ = L / (‖x‖ - δ) * ‖y - x‖ := by ring
  have hlim : Tendsto (fun δ : ℝ => L / (‖x‖ - δ)) (𝓝[>] 0) (𝓝 (L / ‖x‖)) := by
    have hc : ContinuousAt (fun δ : ℝ => L / (‖x‖ - δ)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simpa using hr.ne')
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hr)] with δ hδ hδr
  exact hlocal δ hδ hδr

/-- The angular lift is Lipschitz outside each positive-radius ball.
This supplies actual almost-everywhere differentiability, in addition
to the sharp pointwise `fderiv` estimate. -/
theorem angularLift_lipschitzOn_away_zero {n : ℕ} {g : Vector n → ℝ} {L r : ℝ}
    (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) (hr : 0 < r) :
    LipschitzOnWith (Real.toNNReal (2 * (Real.pi + 1) * L / r))
      (angularLift g) {x : Vector n | r < ‖x‖} := by
  let C : ℝ := 2 * (Real.pi + 1) * L / r
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  change LipschitzOnWith C.toNNReal (angularLift g) _
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change r < ‖x‖ at hx
  change r < ‖y‖ at hy
  rw [Real.coe_toNNReal C hC, dist_eq_norm, Real.norm_eq_abs, dist_eq_norm]
  by_cases hd : ‖x - y‖ < r / 2
  · have hdy : ‖x - y‖ < ‖y‖ := by linarith
    have hden : r / 2 ≤ ‖y‖ - ‖x - y‖ := by linarith
    have hhalf : 0 < r / 2 := by positivity
    have hcoef : 2 * L / r ≤ C := by
      apply div_le_div_of_nonneg_right _ hr.le
      nlinarith [mul_nonneg Real.pi_pos.le hL]
    calc
      |angularLift g x - angularLift g y| ≤
          L * (‖x - y‖ / (‖y‖ - ‖x - y‖)) :=
        angularLift_sub_le hL hg y x hdy
      _ ≤ L * (‖x - y‖ / (r / 2)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (norm_nonneg _) hhalf hden) hL
      _ = (2 * L / r) * ‖x - y‖ := by field_simp [hr.ne']
      _ ≤ C * ‖x - y‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  · have hx0 : x ≠ 0 := norm_pos_iff.mp (hr.trans hx)
    have hy0 : y ≠ 0 := norm_pos_iff.mp (hr.trans hy)
    have hgeo := hg (NormedSpace.normalize x) (NormedSpace.normalize y)
      (NormedSpace.norm_normalize hx0) (NormedSpace.norm_normalize hy0)
    calc
      |angularLift g x - angularLift g y| ≤
          L * Real.arccos (inner ℝ (NormedSpace.normalize x) (NormedSpace.normalize y)) := hgeo
      _ ≤ L * Real.pi := mul_le_mul_of_nonneg_left (Real.arccos_le_pi _) hL
      _ ≤ L * (Real.pi + 1) := mul_le_mul_of_nonneg_left (by linarith) hL
      _ = C * (r / 2) := by dsimp only [C]; field_simp [hr.ne']
      _ ≤ C * ‖x - y‖ := mul_le_mul_of_nonneg_left (le_of_not_gt hd) hC

private theorem angularLift_comp_integrable {n : ℕ} (hn : 1 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hg : GeodesicLipschitz g L)
    (h : ℝ → ℝ) (hh : Continuous h) :
    Integrable (fun x => h (angularLift g x)) (stdGaussian (Vector n)) := by
  have hi := geodesic_comp_integrable hn hg h hh
  rw [unitSphereLaw_eq_normalizedGaussian hn] at hi
  exact hi.comp_measurable (by fun_prop)

private theorem gaussian_ae_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ x ∂stdGaussian (Vector n), x ≠ 0 := by
  let : NeZero n := ⟨by omega⟩
  have hac : stdGaussian (Vector n) ≪ (volume : Measure (Vector n)) := by
    rw [GaussianDensity.stdGaussian_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  apply hac.ae_le
  exact (ae_iff).mpr (by simp)

/-- Rademacher's theorem applies to the actual angular lift away from
the Gaussian-null origin. Thus its finite energy uses genuine
derivatives almost everywhere, without any smoothness assumption on `g`. -/
theorem angularLift_ae_differentiable {n : ℕ} (hn : 1 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) :
    ∀ᵐ x ∂stdGaussian (Vector n), DifferentiableAt ℝ (angularLift g) x := by
  have hdiff (k : ℕ) : ∀ᵐ x ∂(volume : Measure (Vector n)),
      1 / ((k : ℝ) + 1) < ‖x‖ → DifferentiableAt ℝ (angularLift g) x := by
    have hr : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have ho : IsOpen {x : Vector n | 1 / ((k : ℝ) + 1) < ‖x‖} :=
      isOpen_lt continuous_const continuous_norm
    filter_upwards [(angularLift_lipschitzOn_away_zero hL hg hr).ae_differentiableWithinAt_of_mem
      (μ := (volume : Measure (Vector n)))] with x hx hxmem
    exact (hx hxmem).differentiableAt (ho.mem_nhds hxmem)
  have hac : stdGaussian (Vector n) ≪ (volume : Measure (Vector n)) := by
    rw [GaussianDensity.stdGaussian_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have hall := hac.ae_le (ae_all_iff.mpr hdiff)
  filter_upwards [hall, gaussian_ae_ne_zero hn] with x hx hx0
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hx0)
  exact hx k hk

/-- The integrated angular Dirichlet energy has exactly the radial
coefficient required in `lem:ent-lsi`. Both integrability and the bound
hold for the original Lipschitz class, with no smoothness hypothesis. -/
theorem angularLift_gaussian_energy {n : ℕ} (hn : 3 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) (t : ℝ) :
    Integrable (fun x => Real.exp (t * angularLift g x) *
      ‖fderiv ℝ (angularLift g) x‖ ^ 2) (stdGaussian (Vector n)) ∧
    (∫ x, Real.exp (t * angularLift g x) * ‖fderiv ℝ (angularLift g) x‖ ^ 2
      ∂stdGaussian (Vector n)) ≤ L ^ 2 * mgf g (unitSphereLaw n) t / ((n : ℝ) - 2) := by
  have hi := (exponential_radial_energy hn hg t).1.const_mul (L ^ 2)
  have hm : AEStronglyMeasurable
      (fun x => Real.exp (t * angularLift g x) * ‖fderiv ℝ (angularLift g) x‖ ^ 2)
      (stdGaussian (Vector n)) :=
    (angularLift_comp_integrable (by omega) hg (fun z => Real.exp (t * z))
      (by fun_prop)).aestronglyMeasurable.mul
        (((measurable_fderiv ℝ (angularLift g)).norm.pow_const 2).aestronglyMeasurable)
  have hbound : ∀ᵐ x ∂stdGaussian (Vector n),
      Real.exp (t * angularLift g x) * ‖fderiv ℝ (angularLift g) x‖ ^ 2 ≤
      L ^ 2 * ((‖x‖ ^ 2)⁻¹ * Real.exp (t * angularLift g x)) := by
    filter_upwards [gaussian_ae_ne_zero (by omega : 1 ≤ n)] with x hx
    have hsq := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ (angularLift g) x))
      (angularLift_fderiv_norm_le hL hg x hx) 2
    calc
      _ ≤ Real.exp (t * angularLift g x) * (L / ‖x‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = _ := by rw [div_pow]; ring
  have henergy : Integrable (fun x => Real.exp (t * angularLift g x) *
      ‖fderiv ℝ (angularLift g) x‖ ^ 2) (stdGaussian (Vector n)) := by
    apply hi.mono' hm
    filter_upwards [hbound] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    simpa only [angularLift] using hx
  refine ⟨henergy, ?_⟩
  calc
    _ ≤ ∫ x, L ^ 2 * ((‖x‖ ^ 2)⁻¹ * Real.exp (t * angularLift g x))
        ∂stdGaussian (Vector n) := integral_mono_ae henergy hi hbound
    _ = L ^ 2 * mgf g (unitSphereLaw n) t / ((n : ℝ) - 2) := by
      rw [integral_const_mul]
      simp only [angularLift]
      rw [(exponential_radial_energy hn hg t).2]
      ring

/-- The Gaussian half-Dirichlet energy of `t*g` is bounded by the
literal right-hand side of `BakryEmerySphereLogSobolev`. The remaining
Gaussian LSI would bound exponential entropy by this half-energy. -/
theorem gaussian_half_energy_le_sphere_lsi_rhs {n : ℕ} (hn : 3 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) (t : ℝ) :
    (1 / 2 : ℝ) * (∫ x, Real.exp (t * angularLift g x) *
      ‖fderiv ℝ (fun y => t * angularLift g y) x‖ ^ 2 ∂stdGaussian (Vector n)) ≤
      (L ^ 2 * t ^ 2 / (2 * ((n : ℝ) - 2))) * mgf g (unitSphereLaw n) t := by
  have htg : GeodesicLipschitz (fun x => t * g x) (|t| * L) := by
    intro x y hx hy
    calc
      |t * g x - t * g y| = |t| * |g x - g y| := by rw [← mul_sub, abs_mul]
      _ ≤ |t| * (L * Real.arccos (inner ℝ x y)) :=
        mul_le_mul_of_nonneg_left (hg x y hx hy) (abs_nonneg t)
      _ = _ := by ring
  have he := (angularLift_gaussian_energy hn (mul_nonneg (abs_nonneg t) hL) htg 1).2
  have hfun : angularLift (fun x => t * g x) = fun y => t * angularLift g y := rfl
  rw [hfun] at he
  have he' : (∫ x, Real.exp (t * angularLift g x) *
      ‖fderiv ℝ (fun y => t * angularLift g y) x‖ ^ 2 ∂stdGaussian (Vector n)) ≤
      t ^ 2 * L ^ 2 * mgf g (unitSphereLaw n) t / ((n : ℝ) - 2) := by
    simpa only [mgf, one_mul, mul_pow, sq_abs] using he
  have hh := mul_le_mul_of_nonneg_left he' (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ ≤ (1 / 2 : ℝ) *
        (t ^ 2 * L ^ 2 * mgf g (unitSphereLaw n) t / ((n : ℝ) - 2)) := hh
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- A Gaussian-integrable singular weight that is zero at the origin
has vanishing integral over shrinking balls. This also applies to the
inverse-square radial weight, whose value at zero is zero in Lean. -/
theorem integrable_small_ball_zero {n : ℕ} {f : Vector n → ℝ}
    (hf : Integrable f (stdGaussian (Vector n))) (hzero : f 0 = 0) :
    Tendsto (fun ε : ℝ => ∫ x in {x : Vector n | ‖x‖ < ε}, f x
      ∂stdGaussian (Vector n)) (𝓝 0) (𝓝 0) := by
  have hm (ε : ℝ) : MeasurableSet {x : Vector n | ‖x‖ < ε} :=
    measurableSet_lt continuous_norm.measurable measurable_const
  simp_rw [← integral_indicator (hm _)]
  have hlim (x : Vector n) :
      Tendsto (fun ε : ℝ => ({x : Vector n | ‖x‖ < ε}).indicator f x)
        (𝓝 0) (𝓝 0) := by
    by_cases hx : x = 0
    · subst x
      have he : (fun ε : ℝ => ({x : Vector n | ‖x‖ < ε}).indicator f 0) =
          fun _ => 0 := by
        funext ε
        simp [Set.indicator, hzero]
      rw [he]
      exact tendsto_const_nhds
    · apply tendsto_const_nhds.congr'
      filter_upwards [Iio_mem_nhds (norm_pos_iff.mpr hx)] with ε hε
      simp [Set.indicator_of_notMem (show x ∉ {x : Vector n | ‖x‖ < ε} from
        not_lt_of_ge hε.le)]
  have ht := tendsto_integral_filter_of_dominated_convergence
    (fun x : Vector n => ‖f x‖)
    (Eventually.of_forall fun ε => hf.aestronglyMeasurable.indicator (hm ε))
    (Eventually.of_forall fun ε => Eventually.of_forall fun x =>
      norm_indicator_le_norm_self _ _)
    hf.norm (Eventually.of_forall hlim)
  simpa only [integral_zero] using ht

/-- The origin contributes no inverse-square Gaussian energy in the
limit. This is the integrability threshold `n ≥ 3` in radial projection. -/
theorem gaussian_inverse_radius_small_ball {n : ℕ} (hn : 3 ≤ n) :
    Tendsto (fun ε : ℝ => ∫ x in {x : Vector n | ‖x‖ < ε}, (‖x‖ ^ 2)⁻¹
      ∂stdGaussian (Vector n)) (𝓝 0) (𝓝 0) :=
  integrable_small_ball_zero (gaussian_inverse_norm_sq_integrable hn) (by simp)

/-- The full exponential radial energy also vanishes near the origin
for every observable and parameter allowed in the sphere LSI interface. -/
theorem exponential_radial_energy_small_ball {n : ℕ} (hn : 3 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hg : GeodesicLipschitz g L) (t : ℝ) :
    Tendsto (fun ε : ℝ => ∫ x in {x : Vector n | ‖x‖ < ε},
      (‖x‖ ^ 2)⁻¹ * Real.exp (t * angularLift g x)
      ∂stdGaussian (Vector n)) (𝓝 0) (𝓝 0) :=
  integrable_small_ball_zero (exponential_radial_energy hn hg t).1 (by simp)

/-- The actual angular Dirichlet energy, rather than only its radial
dominator, vanishes in shrinking neighborhoods of the singularity. -/
theorem angularLift_gaussian_energy_small_ball {n : ℕ} (hn : 3 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L) (t : ℝ) :
    Tendsto (fun ε : ℝ => ∫ x in {x : Vector n | ‖x‖ < ε},
      Real.exp (t * angularLift g x) * ‖fderiv ℝ (angularLift g) x‖ ^ 2
      ∂stdGaussian (Vector n)) (𝓝 0) (𝓝 0) :=
  integrable_small_ball_zero (angularLift_gaussian_energy hn hL hg t).1
    (by rw [angularLift_fderiv_zero]; simp)

/-- The exponentially weighted shell energy of a radial origin cutoff
vanishes. A cutoff derivative of order `1/ε` therefore contributes
vanishing energy in dimensions at least three. -/
theorem gaussian_origin_shell_energy {n : ℕ} (hn : 3 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hg : GeodesicLipschitz g L) (t : ℝ) :
    Tendsto (fun ε : ℝ => ∫ x in
      {x : Vector n | ε ≤ ‖x‖ ∧ ‖x‖ < 2 * ε},
      (ε ^ 2)⁻¹ * Real.exp (t * angularLift g x)
      ∂stdGaussian (Vector n)) (𝓝[>] 0) (𝓝 0) := by
  have hi := (exponential_radial_energy hn hg t).1
  have he := angularLift_comp_integrable (by omega : 1 ≤ n) hg
    (fun z => Real.exp (t * z)) (by fun_prop)
  have hbound (ε : ℝ) (hε : 0 < ε) :
      (∫ x in {x : Vector n | ε ≤ ‖x‖ ∧ ‖x‖ < 2 * ε},
        (ε ^ 2)⁻¹ * Real.exp (t * angularLift g x)
        ∂stdGaussian (Vector n)) ≤
      4 * (∫ x in {x : Vector n | ‖x‖ < 2 * ε},
        (‖x‖ ^ 2)⁻¹ * Real.exp (t * angularLift g x)
        ∂stdGaussian (Vector n)) := by
    have hA : MeasurableSet {x : Vector n | ε ≤ ‖x‖ ∧ ‖x‖ < 2 * ε} :=
      (measurableSet_le measurable_const continuous_norm.measurable).inter
        (measurableSet_lt continuous_norm.measurable measurable_const)
    have hpoint (x : Vector n) (hx : ε ≤ ‖x‖ ∧ ‖x‖ < 2 * ε) :
        (ε ^ 2)⁻¹ * Real.exp (t * angularLift g x) ≤
        4 * ((‖x‖ ^ 2)⁻¹ * Real.exp (t * angularLift g x)) := by
      have hxpos : 0 < ‖x‖ := hε.trans_le hx.1
      have hsq := pow_le_pow_left₀ (norm_nonneg x) hx.2.le 2
      have hinv : (ε ^ 2)⁻¹ ≤ 4 * (‖x‖ ^ 2)⁻¹ := by
        have hd : 1 / ε ^ 2 ≤ 4 / ‖x‖ ^ 2 :=
          (div_le_div_iff₀ (sq_pos_of_pos hε) (sq_pos_of_pos hxpos)).mpr
            (by nlinarith only [hsq])
        simpa only [one_div, div_eq_mul_inv, one_mul] using hd
      calc
        _ ≤ (4 * (‖x‖ ^ 2)⁻¹) * Real.exp (t * angularLift g x) :=
          mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
        _ = _ := by ring
    calc
      _ ≤ ∫ x in {x : Vector n | ε ≤ ‖x‖ ∧ ‖x‖ < 2 * ε},
          4 * ((‖x‖ ^ 2)⁻¹ * Real.exp (t * angularLift g x))
          ∂stdGaussian (Vector n) :=
        setIntegral_mono_on (he.const_mul ((ε ^ 2)⁻¹)).integrableOn
          (hi.const_mul 4).integrableOn hA hpoint
      _ ≤ ∫ x in {x : Vector n | ‖x‖ < 2 * ε},
          4 * ((‖x‖ ^ 2)⁻¹ * Real.exp (t * angularLift g x))
          ∂stdGaussian (Vector n) :=
        setIntegral_mono_set (hi.const_mul 4).integrableOn
          (Eventually.of_forall fun x => by positivity)
          (Eventually.of_forall fun x hx => hx.2)
      _ = _ := by rw [integral_const_mul]
  have hscale : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ => 2 * ε) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (exponential_radial_energy_small_ball hn hg t).comp hscale
  have hlim4 : Tendsto (fun ε : ℝ =>
      4 * (∫ x in {x : Vector n | ‖x‖ < 2 * ε},
        (‖x‖ ^ 2)⁻¹ * Real.exp (t * angularLift g x)
        ∂stdGaussian (Vector n))) (𝓝[>] 0) (𝓝 0) := by
    simpa using hlim.const_mul 4
  apply squeeze_zero'
    (Eventually.of_forall fun ε => integral_nonneg fun x => by positivity)
    ?_ hlim4
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

/-- The scalar implication at the end of the manuscript's heat-flow
argument: entropy dissipation and positive curvature control the initial
entropy by initial Fisher information, with the exact factor `1/(2ρ)`. -/
theorem entropy_le_fisher_of_decay {H I I' : ℝ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hH : ∀ t, 0 ≤ t → HasDerivAt H (-I t) t)
    (hI : ∀ t, 0 ≤ t → HasDerivAt I (I' t) t)
    (hdecay : ∀ t, 0 ≤ t → I' t ≤ -(2 * ρ) * I t)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ I t)
    (hlim : Tendsto H atTop (𝓝 0)) :
    H 0 ≤ I 0 / (2 * ρ) := by
  let F : ℝ → ℝ := fun t => H t - I t / (2 * ρ)
  have hden : 0 < 2 * ρ := by positivity
  have hF (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt F (-I t - I' t / (2 * ρ)) t :=
    (hH t ht).sub ((hI t ht).div_const (2 * ρ))
  have hderiv (t : ℝ) (ht : 0 ≤ t) : 0 ≤ deriv F t := by
    rw [(hF t ht).deriv]
    have hq : I' t / (2 * ρ) ≤ -I t :=
      (div_le_iff₀ hden).mpr (by nlinarith only [hdecay t ht])
    linarith
  have hmono : MonotoneOn F (Ici (0 : ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hF t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => hderiv t (interior_subset ht))
  have hzero : F 0 ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (hmono (by simp) ht ht).trans
      (sub_le_self _ (div_nonneg (hnonneg t ht) hden.le))
  dsimp only [F] at hzero
  linarith

end SlowEquilibration.SourceSphereLogSobolevFinal
