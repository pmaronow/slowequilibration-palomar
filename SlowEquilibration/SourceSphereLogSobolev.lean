-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceSphereSharpConcentration
public import SlowEquilibration.SpherePolarIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Foundations for the logarithmic Sobolev inequality in Section 8.
The unit-sphere probability in the concentration interface is identified
with normalized angular volume and with radial projection of a standard
Gaussian. These identifications allow exact transfer of entropy and
radially weighted integrals, without a change in normalization. The
inverse-square Gaussian radius moment is proved, including its
integrability at the origin. The remaining analytic step toward
`BakryEmerySphereLogSobolev` is the Gaussian logarithmic Sobolev inequality
with integrated gradient energy for the angular lift.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceSphereLogSobolev

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceSphereSharpConcentration
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The surface probability used by `lem:ent-lsi` is precisely the
normalized angular volume, at radius one. -/
theorem unitSphereLaw_eq_angular {n : ℕ} (hn : 1 ≤ n) :
    unitSphereLaw n =
      (SphereVolume.unitAngular (Vector n)).map
        (Subtype.val : Metric.sphere (0 : Vector n) 1 → Vector n) := by
  let : NeZero n := ⟨by omega⟩
  have hs : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))).ne'
  rw [unitSphereLaw, SphericalModel.sphereLaw, SphereVolume.sphereLaw_eq_normalized_angular n hn,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext u
  simp [smul_smul, hs]

/-- The same probability is radial projection of the actual standard
Gaussian. In particular, no asymptotic Gaussian approximation is used. -/
theorem unitSphereLaw_eq_normalizedGaussian {n : ℕ} (hn : 1 ≤ n) :
    unitSphereLaw n =
      (stdGaussian (Vector n)).map (fun x => ‖x‖⁻¹ • x) := by
  let : NeZero n := ⟨by omega⟩
  rw [unitSphereLaw_eq_angular hn]
  have he : SphereVolume.normalize (E := Vector n) 1 =
      (fun x => ‖x‖⁻¹ • x) := by
    funext x
    simp only [SphereVolume.normalize, one_div]
  rw [← he, SphereVolume.normalizedGaussian_eq_angular]
  congr 1
  funext u
  exact (one_smul ℝ (u : Vector n)).symm

/-- Exact pullback of a surface integral along Gaussian radial projection. -/
theorem integral_unitSphereLaw_eq_gaussian {n : ℕ} (hn : 1 ≤ n)
    (f : Vector n → ℝ) (hf : AEStronglyMeasurable f (unitSphereLaw n)) :
    (∫ x, f x ∂unitSphereLaw n) =
      ∫ x, f (‖x‖⁻¹ • x) ∂stdGaussian (Vector n) := by
  rw [unitSphereLaw_eq_normalizedGaussian hn] at hf ⊢
  exact integral_map (by fun_prop) hf

/-- Polar independence separates any integrable radial weight from a
surface observable. This is the exact factorization needed in the
Gaussian projection proof of the curvature constant. -/
theorem integral_radial_mul_angular {n : ℕ} (hn : 1 ≤ n)
    (w : Ioi (0 : ℝ) → ℝ) (hw : Integrable w (SphereVolume.gaussianRadius (Vector n)))
    (f : Vector n → ℝ) (hf : Integrable f (unitSphereLaw n)) :
    Integrable (fun p : Ioi (0 : ℝ) × Metric.sphere (0 : Vector n) 1 =>
      w p.1 * f p.2) ((SphereVolume.gaussianRadius (Vector n)).prod
        (SphereVolume.unitAngular (Vector n))) ∧
    (∫ p : Ioi (0 : ℝ) × Metric.sphere (0 : Vector n) 1,
      w p.1 * f p.2 ∂(SphereVolume.gaussianRadius (Vector n)).prod
        (SphereVolume.unitAngular (Vector n))) =
      (∫ r, w r ∂SphereVolume.gaussianRadius (Vector n)) *
        (∫ x, f x ∂unitSphereLaw n) := by
  let : NeZero n := ⟨by omega⟩
  have hfi : Integrable (fun u : Metric.sphere (0 : Vector n) 1 => f u)
      (SphereVolume.unitAngular (Vector n)) := by
    rw [unitSphereLaw_eq_angular hn] at hf
    exact hf.comp_measurable (by fun_prop)
  refine ⟨hw.mul_prod hfi, ?_⟩
  rw [integral_prod_mul w (fun u : Metric.sphere (0 : Vector n) 1 => f u)]
  congr 1
  have hm := hf.aestronglyMeasurable
  rw [unitSphereLaw_eq_angular hn] at hm ⊢
  exact (integral_map (by fun_prop) hm).symm

private theorem gaussian_halfline_moment_integrable (k : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2))
      (Ioi 0) := by
  simpa only [Real.rpow_natCast] using
    (integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
      (s := (k : ℝ)) (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith))

private theorem gaussian_halfline_moment_recurrence (k : ℕ) (hk : 1 ≤ k) :
    (∫ r : ℝ in Ioi 0, r ^ (k + 1) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) =
      (k : ℝ) * (∫ r : ℝ in Ioi 0,
        r ^ (k - 1) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) := by
  let F : ℝ → ℝ := fun r => r ^ k * Real.exp (-(1 / 2 : ℝ) * r ^ 2)
  let D : ℝ → ℝ := fun r =>
    (k : ℝ) * (r ^ (k - 1) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) -
      r ^ (k + 1) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)
  have hd (r : ℝ) : HasDerivAt F (D r) r := by
    dsimp only [F, D]
    convert ((hasDerivAt_pow k r).mul
      (((hasDerivAt_pow 2 r).const_mul (-(1 / 2 : ℝ))).exp)) using 1
    simp only [Nat.cast_ofNat, pow_succ]
    ring
  have hiD : IntegrableOn D (Ioi 0) :=
    ((gaussian_halfline_moment_integrable (k - 1)).const_mul (k : ℝ)).sub
      (gaussian_halfline_moment_integrable (k + 1))
  have ht : Tendsto F atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
      (fun r _ => hd r) hiD (gaussian_halfline_moment_integrable k)
  have hz := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun r _ => hd r) hiD ht
  have hz0 : (∫ r in Ioi (0 : ℝ), D r) = 0 := by
    simpa [F, show k ≠ 0 by omega] using hz
  dsimp only [D] at hz0
  rw [integral_sub ((gaussian_halfline_moment_integrable (k - 1)).const_mul (k : ℝ))
    (gaussian_halfline_moment_integrable (k + 1)), integral_const_mul] at hz0
  linarith

private theorem vector_finrank (n : ℕ) : Module.finrank ℝ (Vector n) = n := by
  simp [SphericalModel.Vector, SphericalAging.FiniteModel.Vector]

private theorem gaussian_radial_integral {n : ℕ} (hn : 1 ≤ n) (f : ℝ → ℝ) :
    (∫ x : Vector n, f ‖x‖ ∂stdGaussian (Vector n)) =
      ((n : ℝ) * (volume : Measure (Vector n)).real (Metric.ball 0 1) *
        GaussianDensity.normalizer (Vector n)) *
      ∫ r : ℝ in Ioi 0, r ^ (n - 1) *
        Real.exp (-(1 / 2 : ℝ) * r ^ 2) * f r := by
  let : NeZero n := ⟨by omega⟩
  rw [GaussianDensity.stdGaussian_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      GaussianDensity.density_continuous.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (GaussianDensity.density_pos _).le,
    smul_eq_mul]
  unfold GaussianDensity.density
  rw [integral_fun_norm_addHaar volume
    (fun r : ℝ => GaussianDensity.normalizer (Vector n) *
      Real.exp (-(1 / 2 : ℝ) * r ^ 2) * f r)]
  simp only [vector_finrank, nsmul_eq_mul, smul_eq_mul]
  have he (r : ℝ) : r ^ (n - 1) *
      (GaussianDensity.normalizer (Vector n) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) * f r) =
      GaussianDensity.normalizer (Vector n) *
        (r ^ (n - 1) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) * f r) := by ring
  simp_rw [he]
  rw [integral_const_mul]
  ring

/-- The singular radial energy of Gaussian projection is integrable
exactly in the dimensions relevant to the sphere curvature inequality. -/
theorem gaussian_inverse_norm_sq_integrable {n : ℕ} (hn : 3 ≤ n) :
    Integrable (fun x : Vector n => (‖x‖ ^ 2)⁻¹) (stdGaussian (Vector n)) := by
  let : NeZero n := ⟨by omega⟩
  rw [GaussianDensity.stdGaussian_eq_withDensity]
  apply (integrable_withDensity_iff_integrable_smul'
    GaussianDensity.density_continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simp only [ENNReal.toReal_ofReal (GaussianDensity.density_pos _).le,
    smul_eq_mul]
  unfold GaussianDensity.density
  apply (integrable_fun_norm_addHaar volume (f := fun r : ℝ =>
    GaussianDensity.normalizer (Vector n) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) *
      (r ^ 2)⁻¹)).mpr
  simp only [vector_finrank, smul_eq_mul]
  have he (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
      r ^ (n - 1) * (GaussianDensity.normalizer (Vector n) *
        Real.exp (-(1 / 2 : ℝ) * r ^ 2) * (r ^ 2)⁻¹) =
      GaussianDensity.normalizer (Vector n) *
        (r ^ (n - 3) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) := by
    rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
    field_simp [(ne_of_gt hr : r ≠ 0)]
  apply IntegrableOn.congr_fun ((gaussian_halfline_moment_integrable (n - 3)).const_mul
    (GaussianDensity.normalizer (Vector n))) _ measurableSet_Ioi
  intro r hr
  exact (he r hr).symm

/-- The exact inverse-square Gaussian radius moment. This produces the
factor `n-2`, without an estimate of the sphere area or a limiting argument. -/
theorem gaussian_inverse_norm_sq_integral {n : ℕ} (hn : 3 ≤ n) :
    (∫ x : Vector n, (‖x‖ ^ 2)⁻¹ ∂stdGaussian (Vector n)) =
      1 / ((n : ℝ) - 2) := by
  let C := (n : ℝ) * (volume : Measure (Vector n)).real (Metric.ball 0 1) *
    GaussianDensity.normalizer (Vector n)
  have hnorm : C * (∫ r : ℝ in Ioi 0,
      r ^ (n - 1) * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) = 1 := by
    have h := gaussian_radial_integral (by omega : 1 ≤ n) (fun _ => (1 : ℝ))
    simpa [C] using h.symm
  have hrec := gaussian_halfline_moment_recurrence (n - 2) (by omega)
  rw [show n - 2 + 1 = n - 1 by omega, show n - 2 - 1 = n - 3 by omega] at hrec
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_ofNat]
  rw [hcast] at hrec
  rw [gaussian_radial_integral (by omega : 1 ≤ n) (fun r => (r ^ 2)⁻¹)]
  have he : (∫ r : ℝ in Ioi 0,
      r ^ (n - 1) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) * (r ^ 2)⁻¹) =
      ∫ r : ℝ in Ioi 0, r ^ (n - 3) * Real.exp (-(1 / 2 : ℝ) * r ^ 2) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [show n - 1 = (n - 3) + 2 by omega, pow_add]
    field_simp [(ne_of_gt hr : r ≠ 0)]
  rw [he]
  change C * _ = _
  have hnpos : 0 < (n : ℝ) - 2 := by
    have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  apply (eq_div_iff hnpos.ne').mpr
  rw [hrec] at hnorm
  nlinarith only [hnorm]

/-- The inverse-square radius moment in the polar product probability,
including integrability of its singular weight. -/
theorem gaussianRadius_inverse_sq {n : ℕ} (hn : 3 ≤ n) :
    Integrable (fun r : Ioi (0 : ℝ) => ((r : ℝ) ^ 2)⁻¹)
      (SphereVolume.gaussianRadius (Vector n)) ∧
    (∫ r : Ioi (0 : ℝ), ((r : ℝ) ^ 2)⁻¹
      ∂SphereVolume.gaussianRadius (Vector n)) = 1 / ((n : ℝ) - 2) := by
  let : NeZero n := ⟨by omega⟩
  have hi : Integrable (fun r : ℝ => (r ^ 2)⁻¹)
      ((stdGaussian (Vector n)).map norm) :=
    (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
      (gaussian_inverse_norm_sq_integrable hn)
  have hir := hi
  rw [← SphereVolume.gaussianRadius_map] at hir
  refine ⟨hir.comp_measurable measurable_subtype_coe, ?_⟩
  have he : (∫ r : Ioi (0 : ℝ), ((r : ℝ) ^ 2)⁻¹
      ∂SphereVolume.gaussianRadius (Vector n)) =
      ∫ x : Vector n, (‖x‖ ^ 2)⁻¹ ∂stdGaussian (Vector n) := by
    rw [← integral_map measurable_subtype_coe.aemeasurable hir.aestronglyMeasurable,
      SphereVolume.gaussianRadius_map, integral_map (by fun_prop) hi.aestronglyMeasurable]
  exact he.trans (gaussian_inverse_norm_sq_integral hn)

/-- Exact weighted angular integral under the actual Gaussian measure.
This is the radial energy identity in the projection argument for
`lem:ent-lsi`; its coefficient is precisely `1/(n-2)`. -/
theorem gaussian_inverse_radius_mul_angular {n : ℕ} (hn : 3 ≤ n)
    (f : Vector n → ℝ) (hf : Integrable f (unitSphereLaw n)) :
    Integrable (fun x : Vector n => (‖x‖ ^ 2)⁻¹ * f (‖x‖⁻¹ • x))
      (stdGaussian (Vector n)) ∧
    (∫ x : Vector n, (‖x‖ ^ 2)⁻¹ * f (‖x‖⁻¹ • x)
      ∂stdGaussian (Vector n)) =
      (1 / ((n : ℝ) - 2)) * (∫ x, f x ∂unitSphereLaw n) := by
  let : NeZero n := ⟨by omega⟩
  have hn' : 1 ≤ n := by omega
  let F : Vector n → ℝ := fun x => (‖x‖ ^ 2)⁻¹ * f (‖x‖⁻¹ • x)
  have hfm : AEStronglyMeasurable (fun x : Vector n => f (‖x‖⁻¹ • x))
      (stdGaussian (Vector n)) := by
    rw [unitSphereLaw_eq_normalizedGaussian hn'] at hf
    exact (hf.comp_measurable (by fun_prop)).aestronglyMeasurable
  have hFm : AEStronglyMeasurable F (stdGaussian (Vector n)) :=
    (gaussian_inverse_norm_sq_integrable hn).aestronglyMeasurable.mul hfm
  have he (r : Ioi (0 : ℝ)) (u : Metric.sphere (0 : Vector n) 1) :
      F ((r : ℝ) • (u : Vector n)) = ((r : ℝ) ^ 2)⁻¹ * f u := by
    have hu : ‖(u : Vector n)‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using u.property
    simp [F, norm_smul, Real.norm_of_nonneg r.property.le, hu, smul_smul, r.property.ne']
  have hprod := (integral_radial_mul_angular hn'
    (fun r : Ioi (0 : ℝ) => ((r : ℝ) ^ 2)⁻¹)
    (gaussianRadius_inverse_sq hn).1 f hf).1
  have hFi : Integrable F (stdGaussian (Vector n)) := by
    apply (SphereVolume.gaussian_polar_preserving.integrable_comp hFm).mp
    simpa only [Function.comp_def, SphereVolume.polarMap, he] using hprod
  refine ⟨hFi, ?_⟩
  change (∫ x, F x ∂stdGaussian (Vector n)) = _
  rw [SphereVolume.gaussian_polar_integral hFi]
  simp_rw [he, integral_const_mul]
  rw [integral_mul_const, (gaussianRadius_inverse_sq hn).2]
  congr 1
  have hm := hf.aestronglyMeasurable
  rw [unitSphereLaw_eq_angular hn'] at hm ⊢
  exact (integral_map (by fun_prop) hm).symm

private theorem geodesic_continuousOn {n : ℕ} {g : Vector n → ℝ} {L : ℝ}
    (hg : GeodesicLipschitz g L) : ContinuousOn g {x | ‖x‖ = 1} := by
  intro x hx
  have hxn : ‖x‖ = 1 := hx
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh : Tendsto (fun y : Vector n => L * Real.arccos (inner ℝ y x))
      (𝓝[{x | ‖x‖ = 1}] x) (𝓝 0) := by
    have hc : Continuous (fun y : Vector n => L * Real.arccos (inner ℝ y x)) := by
      fun_prop
    simpa [real_inner_self_eq_norm_sq, hxn] using
      (hc.continuousAt (x := x)).tendsto.mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hh
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa only [Real.norm_eq_abs] using hg y x hy hx

/-- Every continuous function of a geodesically Lipschitz observable is
surface-integrable. Arbitrary values away from the sphere cause no
measurability restriction. -/
theorem geodesic_comp_integrable {n : ℕ} (hn : 1 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hg : GeodesicLipschitz g L)
    (h : ℝ → ℝ) (hh : Continuous h) :
    Integrable (fun x => h (g x)) (unitSphereLaw n) := by
  let : NeZero n := ⟨by omega⟩
  have hc : Continuous (fun u : Metric.sphere (0 : Vector n) 1 => g u) := by
    apply (geodesic_continuousOn hg).comp_continuous continuous_subtype_val
    intro u
    simpa only [mem_ofPred_eq, Metric.mem_sphere, dist_zero_right] using u.property
  have hi : Integrable (fun u : Metric.sphere (0 : Vector n) 1 => h (g u))
      (SphereVolume.unitAngular (Vector n)) :=
    (hh.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [unitSphereLaw_eq_angular hn]
  exact (MeasurableEmbedding.subtype_coe Metric.isClosed_sphere.measurableSet).integrable_map_iff.mpr hi

/-- The exponential entropy in the interface is exactly the entropy of
the angular Gaussian lift. All measurability follows from the interface's
geodesic Lipschitz condition. -/
theorem exponential_entropy_eq_gaussian {n : ℕ} (hn : 1 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hg : GeodesicLipschitz g L) (t : ℝ) :
    (∫ x, Real.exp (t * g x) * (t * g x) ∂unitSphereLaw n) -
      mgf g (unitSphereLaw n) t * Real.log (mgf g (unitSphereLaw n) t) =
    (∫ x : Vector n, Real.exp (t * g (‖x‖⁻¹ • x)) * (t * g (‖x‖⁻¹ • x))
      ∂stdGaussian (Vector n)) -
      mgf (fun x : Vector n => g (‖x‖⁻¹ • x)) (stdGaussian (Vector n)) t *
        Real.log (mgf (fun x : Vector n => g (‖x‖⁻¹ • x)) (stdGaussian (Vector n)) t) := by
  have he := integral_unitSphereLaw_eq_gaussian hn
    (fun x => Real.exp (t * g x) * (t * g x))
    (geodesic_comp_integrable hn hg (fun s => Real.exp (t * s) * (t * s))
      (by fun_prop)).aestronglyMeasurable
  have hm := integral_unitSphereLaw_eq_gaussian hn (fun x => Real.exp (t * g x))
    (geodesic_comp_integrable hn hg (fun s => Real.exp (t * s))
      (by fun_prop)).aestronglyMeasurable
  unfold mgf
  rw [he, hm]

/-- The radial factor in the projected exponential Dirichlet energy has
exactly the manuscript coefficient. This includes integrability at the
origin for every observable admitted by the concentration interface. -/
theorem exponential_radial_energy {n : ℕ} (hn : 3 ≤ n)
    {g : Vector n → ℝ} {L : ℝ} (hg : GeodesicLipschitz g L) (t : ℝ) :
    Integrable (fun x : Vector n => (‖x‖ ^ 2)⁻¹ * Real.exp (t * g (‖x‖⁻¹ • x)))
      (stdGaussian (Vector n)) ∧
    (∫ x : Vector n, (‖x‖ ^ 2)⁻¹ * Real.exp (t * g (‖x‖⁻¹ • x))
      ∂stdGaussian (Vector n)) = mgf g (unitSphereLaw n) t / ((n : ℝ) - 2) := by
  simpa [mgf, div_eq_mul_inv, mul_comm] using
    gaussian_inverse_radius_mul_angular hn (fun x => Real.exp (t * g x))
      (geodesic_comp_integrable (by omega) hg (fun s => Real.exp (t * s)) (by fun_prop))

end SlowEquilibration.SourceSphereLogSobolev
