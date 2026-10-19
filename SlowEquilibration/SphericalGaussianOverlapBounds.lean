-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianAxis

@[expose] public section

/-! # Genuine finite-dimensional central spherical overlap bounds

The reference vector may depend on the dimension. The estimates follow from
its actual unit Gaussian projection and a genuine Gaussian radial lower tail.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalBarycenter SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace NNReal ENNReal
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A dimension-independent finite scalar sixth moment of the actual N(0,1). -/
def gaussianSixthMoment : ℝ := ∫ z : ℝ, |z|^6 ∂gaussianReal 0 1

lemma gaussianSixthMoment_nonneg : 0 ≤ gaussianSixthMoment :=
  integral_nonneg fun _ => by positivity

lemma unit_projection_sixth_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (e : E) (he : ‖e‖=1) :
    Integrable (fun g : E => |inner ℝ e g|^6) (stdGaussian E) := by
  have h := (unit_gaussian_projection_hasLaw e he).memLp
    (show MemLp (id : ℝ → ℝ) (6 : ℝ≥0∞) (gaussianReal 0 1) from
      memLp_id_gaussianReal' _ (by norm_num))
  simpa only [Real.norm_eq_abs] using h.integrable_norm_pow' (p := 6)

lemma unit_projection_sixth_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (e : E) (he : ‖e‖=1) :
    (∫ g : E, |inner ℝ e g|^6 ∂stdGaussian E)=gaussianSixthMoment := by
  have hf : AEStronglyMeasurable (fun z : ℝ => |z|^6) (gaussianReal 0 1) :=
    (continuous_abs.pow 6).aestronglyMeasurable
  exact (unit_gaussian_projection_hasLaw e he).integral_comp hf

/-- Literal bad radial event used in the central overlap estimate. -/
def gaussianSmallRadius (N : ℕ) : Set (Vector N) := {g | ‖g‖^2 ≤ (N:ℝ)/4}

lemma gaussianSmallRadius_measurable (N : ℕ) : MeasurableSet (gaussianSmallRadius N) :=
  measurableSet_le (measurable_norm.pow_const 2) measurable_const

lemma gaussianSmallRadius_tail (N : ℕ) :
    (stdGaussian (Vector N)).real (gaussianSmallRadius N) ≤
      Real.exp (-(N:ℝ)*GaussianShell.rate (1/4)) := by
  have h := GaussianShell.lower_tail (E := Vector N) (a := 1/4) (by norm_num) (by norm_num)
  simpa only [gaussianSmallRadius,finrank_euclideanSpace,Fintype.card_fin,one_div,div_eq_mul_inv,
    mul_comm,one_mul] using h

private lemma ratio_square_le {N r z : ℝ} (hN : 0<N) (hr : 0<r)
    (hlarge : N/4≤r^2) : (z/r)^2≤(4/N)*z^2 := by
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  have hfactor : 1≤(4/N)*r^2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hN).mpr
    nlinarith
  nlinarith [sq_nonneg z,mul_nonneg (sq_nonneg z) (sub_nonneg.mpr hfactor)]

/-- The true normalized overlap sixth moment is O(N⁻³), uniformly over every
actual sphere reference. -/
theorem sphere_overlap_sixth_moment_le (N : ℕ) (hN : 1≤N) (x : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) :
    (∫ y : Vector N, |overlap x y|^6 ∂sphereLaw N) ≤
      (64/(N:ℝ)^3)*gaussianSixthMoment+Real.exp (-(N:ℝ)*GaussianShell.rate (1/4)) := by
  let := sphereLaw_probability N
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have he : ‖spin x‖=1 := spin_norm hN x ((onSphere_iff_norm_sq x).mpr hx)
  let B := gaussianSmallRadius N
  have hB : MeasurableSet B := gaussianSmallRadius_measurable N
  have hf : Continuous (fun y : Vector N => |overlap x y|^6) := by unfold overlap; fun_prop
  have hiSphere := integrable_sphereSupported_continuous (sphereLaw N) (sphereLaw_support hN) hf
  have hi : Integrable (fun g : Vector N => |overlap x (SphericalAging.SphereInitialLaw.normalize N g)|^6)
      (stdGaussian (Vector N)) := by
    apply (integrable_map_measure hf.aestronglyMeasurable (SphericalAging.SphereInitialLaw.normalize_measurable N).aemeasurable).mp
    exact hiSphere
  have hproj := unit_projection_sixth_integrable (spin x) he
  have hdom : Integrable (fun g : Vector N =>
      (64/(N:ℝ)^3)*|inner ℝ (spin x) g|^6+B.indicator (fun _ => (1:ℝ)) g) (stdGaussian (Vector N)) :=
    (hproj.const_mul _).add ((integrable_const 1).indicator hB)
  have hle : ∀ᵐ g : Vector N ∂stdGaussian (Vector N),
      |overlap x (SphericalAging.SphereInitialLaw.normalize N g)|^6 ≤
        (64/(N:ℝ)^3)*|inner ℝ (spin x) g|^6+B.indicator (fun _ => (1:ℝ)) g := by
    filter_upwards [SphericalAging.SphereInitialLaw.gaussian_ne_zero_ae hN] with g hg
    have hnorm : 0<‖g‖ := norm_pos_iff.mpr hg
    by_cases hb : g∈B
    · have hr := overlap_mem_Icc_of_norm_sq hN x (SphericalAging.SphereInitialLaw.normalize N g)
        hx (SphericalAging.SphereInitialLaw.normalize_norm_sq g hg)
      have habs : |overlap x (SphericalAging.SphereInitialLaw.normalize N g)|≤1 := abs_le.mpr hr
      have hpow := pow_le_pow_left₀ (abs_nonneg _) habs 6
      simp only [one_pow] at hpow
      simp only [Set.indicator_of_mem hb]
      exact hpow.trans (le_add_of_nonneg_left (by positivity))
    · have hlarge : (N:ℝ)/4≤‖g‖^2 := (lt_of_not_ge hb).le
      have hs := ratio_square_le hNp hnorm hlarge (z := inner ℝ (spin x) g)
      have hp := pow_le_pow_left₀ (sq_nonneg _) hs 3
      rw [overlap_normalize_eq N hN]
      simp only [Set.indicator_of_notMem hb,add_zero]
      convert hp using 1
      · simp only [← pow_mul]
        exact (show Even (6:ℕ) from by decide).pow_abs _
      · rw [(show Even (6:ℕ) from by decide).pow_abs]
        field_simp
        ring
  have hbound := integral_mono_ae hi hdom hle
  rw [integral_add (hproj.const_mul _) ((integrable_const 1).indicator hB),
    integral_const_mul,unit_projection_sixth_integral (spin x) he,
    integral_indicator_const _ hB,smul_eq_mul,mul_one] at hbound
  have hmap := integral_map (μ := stdGaussian (Vector N))
    (SphericalAging.SphereInitialLaw.normalize_measurable N).aemeasurable hf.aestronglyMeasurable
  change (∫ y : Vector N, |overlap x y|^6 ∂sphereLaw N)=_ at hmap
  rw [hmap]
  exact hbound.trans (add_le_add le_rfl (gaussianSmallRadius_tail N))


lemma unit_projection_exp_sq_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (e : E) (he : ‖e‖=1) {t : ℝ} (ht : t<1/2) :
    Integrable (fun g : E => Real.exp (t*(inner ℝ e g)^2)) (stdGaussian E) := by
  have hi : Integrable (fun z : ℝ => Real.exp (t*z^2)) (gaussianReal 0 1) := by
    rw [← stdGaussian_real_eq]
    simpa only [Real.norm_eq_abs,sq_abs] using GaussianShell.integrable_exp_norm_sq (E := ℝ) ht
  exact (unit_gaussian_projection_hasLaw e he).integrable_comp hi

/-- A uniform genuine spherical quadratic exponential bound for a small
fixed positive coefficient, with the actual radius-zero exception removed. -/
theorem sphere_overlap_exp_square_le (N : ℕ) (hN : 1≤N) (x : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) {t : ℝ} (ht0 : 0≤t) (ht : 4*t<1/2)
    (htrate : t≤GaussianShell.rate (1/4)) :
    (∫ y : Vector N, Real.exp (t*(N:ℝ)*(overlap x y)^2) ∂sphereLaw N) ≤
      (1-8*t)^(-(1:ℝ)/2)+1 := by
  let := sphereLaw_probability N
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have he : ‖spin x‖=1 := spin_norm hN x ((onSphere_iff_norm_sq x).mpr hx)
  let B := gaussianSmallRadius N
  have hB : MeasurableSet B := gaussianSmallRadius_measurable N
  have hf : Continuous (fun y : Vector N => Real.exp (t*(N:ℝ)*(overlap x y)^2)) := by
    unfold overlap; fun_prop
  have hiSphere := integrable_sphereSupported_continuous (sphereLaw N) (sphereLaw_support hN) hf
  have hi : Integrable (fun g : Vector N =>
      Real.exp (t*(N:ℝ)*(overlap x (SphericalAging.SphereInitialLaw.normalize N g))^2))
      (stdGaussian (Vector N)) := by
    apply (integrable_map_measure hf.aestronglyMeasurable
      (SphericalAging.SphereInitialLaw.normalize_measurable N).aemeasurable).mp
    exact hiSphere
  have hproj := unit_projection_exp_sq_integrable (spin x) he ht
  have hdom : Integrable (fun g : Vector N =>
      Real.exp ((4*t)*(inner ℝ (spin x) g)^2)+B.indicator (fun _ => Real.exp (t*N)) g)
      (stdGaussian (Vector N)) :=
    hproj.add ((integrable_const _).indicator hB)
  have hle : ∀ᵐ g : Vector N ∂stdGaussian (Vector N),
      Real.exp (t*(N:ℝ)*(overlap x (SphericalAging.SphereInitialLaw.normalize N g))^2) ≤
        Real.exp ((4*t)*(inner ℝ (spin x) g)^2)+B.indicator (fun _ => Real.exp (t*N)) g := by
    filter_upwards [SphericalAging.SphereInitialLaw.gaussian_ne_zero_ae hN] with g hg
    have hnorm : 0<‖g‖ := norm_pos_iff.mpr hg
    by_cases hb : g∈B
    · have hr := overlap_mem_Icc_of_norm_sq hN x (SphericalAging.SphereInitialLaw.normalize N g)
        hx (SphericalAging.SphereInitialLaw.normalize_norm_sq g hg)
      have habs : |overlap x (SphericalAging.SphereInitialLaw.normalize N g)|≤1 := abs_le.mpr hr
      have hpow := pow_le_pow_left₀ (abs_nonneg _) habs 2
      simp only [sq_abs,one_pow] at hpow
      have hsmall : Real.exp (t*(N:ℝ)*(overlap x (SphericalAging.SphereInitialLaw.normalize N g))^2) ≤
          Real.exp (t*N) := by
        apply Real.exp_le_exp.mpr
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow (mul_nonneg ht0 hNp.le)
      rw [Set.indicator_of_mem hb]
      exact hsmall.trans (le_add_of_nonneg_left (Real.exp_pos _).le)
    · have hlarge : (N:ℝ)/4≤‖g‖^2 := (lt_of_not_ge hb).le
      have hs := ratio_square_le hNp hnorm hlarge (z := inner ℝ (spin x) g)
      rw [overlap_normalize_eq N hN,Set.indicator_of_notMem hb,add_zero]
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg ht0 hNp.le)
      convert hm using 1
      field_simp
  have hbound := integral_mono_ae hi hdom hle
  rw [integral_add hproj ((integrable_const _).indicator hB),
    unit_gaussian_projection_exp_sq (spin x) he ht,integral_indicator_const _ hB,smul_eq_mul] at hbound
  have htail : (stdGaussian (Vector N)).real B*Real.exp (t*N) ≤ 1 := by
    calc
      _ ≤ Real.exp (-(N:ℝ)*GaussianShell.rate (1/4))*Real.exp (t*N) :=
        mul_le_mul_of_nonneg_right (gaussianSmallRadius_tail N) (Real.exp_pos _).le
      _ = Real.exp ((t-GaussianShell.rate (1/4))*N) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htrate) hNp.le)
      _ = 1 := Real.exp_zero
  have hmap := integral_map (μ := stdGaussian (Vector N))
    (SphericalAging.SphereInitialLaw.normalize_measurable N).aemeasurable hf.aestronglyMeasurable
  change (∫ y : Vector N, Real.exp (t*(N:ℝ)*(overlap x y)^2) ∂sphereLaw N)=_ at hmap
  rw [hmap]
  convert hbound.trans (add_le_add le_rfl htail) using 1
  congr 2
  ring

end
end SlowEquilibration.SphericalModel
