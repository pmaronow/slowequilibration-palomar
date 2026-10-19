-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalUniformWickMoments
public import SlowEquilibration.SphericalGaussianAxis
public import SlowEquilibration.SphericalCentralOverlapPerturbation
public import SlowEquilibration.SphericalGaussianOverlapBounds
public import SlowEquilibration.SphereSupportedIntegrals
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Sharp spherical overlap moments and the exponential-square comparison
in manuscript `lem:pc-spherical`. Gaussian radius moments are evaluated
from their exact MGF; angular/radius independence then gives the literal
finite-dimensional moment formula, including dimension one. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceSphericalSharpMoments
open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalParisiRadialIndependence SphericalUniformWickMoments
open SphericalBarycenter SphericalAging.HardSphereDynamics
open SphericalForm
open scoped Topology BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Exact rising-product normalization of the even Gaussian radius moment. -/
def radialMomentProduct (m k : ℕ) : ℝ := ∏ j ∈ Finset.range k, ((m+2*j:ℕ):ℝ)

private theorem radialMomentProduct_succ (m k : ℕ) :
    radialMomentProduct m (k+1)=radialMomentProduct m k*((m+2*k:ℕ):ℝ) := by
  exact Finset.prod_range_succ _ _

private theorem iteratedDeriv_radius_mgf {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) {t : ℝ} (ht : t < 1/2) :
    iteratedDeriv k (mgf (fun g : E => ‖g‖^2) (stdGaussian E)) t =
      radialMomentProduct (Module.finrank ℝ E) k *
        (1-2*t)^(-((Module.finrank ℝ E:ℝ)/2)-(k:ℝ)) := by
  induction k generalizing t with
  | zero => simp [mgf,radialMomentProduct,GaussianShell.integral_exp_norm_sq ht]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv k (mgf (fun g : E => ‖g‖^2) (stdGaussian E)) =ᶠ[𝓝 t]
        (fun t : ℝ => radialMomentProduct (Module.finrank ℝ E) k *
          (1-2*t)^(-((Module.finrank ℝ E:ℝ)/2)-(k:ℝ))) := by
      filter_upwards [Iio_mem_nhds ht] with u hu
      exact ih hu
    rw [heq.deriv_eq]
    have hbase : 0 < 1-2*t := by linarith
    have hd := (((hasDerivAt_const t (1:ℝ)).sub
      ((hasDerivAt_id t).const_mul 2)).rpow_const
        (p := -((Module.finrank ℝ E:ℝ)/2)-(k:ℝ))
        (Or.inl hbase.ne')).const_mul (radialMomentProduct (Module.finrank ℝ E) k)
    simp only [Pi.sub_apply,id_eq,mul_one,zero_sub] at hd
    rw [hd.deriv,radialMomentProduct_succ]
    push_cast
    rw [show -((Module.finrank ℝ E:ℝ)/2)-((k:ℝ)+1) =
      -((Module.finrank ℝ E:ℝ)/2)-(k:ℝ)-1 by ring]
    ring

/-- Exact even Gaussian radius moments, valid in every finite dimension. -/
theorem gaussian_radius_even_moment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (k : ℕ) :
    (∫ g : E, ‖g‖^(2*k) ∂stdGaussian E)=radialMomentProduct (Module.finrank ℝ E) k := by
  have hmem : (0:ℝ) ∈ interior (integrableExpSet (fun g : E => ‖g‖^2) (stdGaussian E)) := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))
    intro t ht
    exact GaussianShell.integrable_exp_norm_sq ht
  have hh := iteratedDeriv_mgf_zero hmem k
  rw [iteratedDeriv_radius_mgf k (by norm_num)] at hh
  simpa only [mul_zero,sub_zero,Real.one_rpow,mul_one,Pi.pow_apply,←pow_mul] using hh.symm

/-- Evaluation of the actual radial coefficient in the existing Wick API. -/
theorem gaussianNormMoment_even (m k : ℕ) :
    gaussianNormMoment m (2*k)=radialMomentProduct m k := by
  simpa only [gaussianNormMoment,SphericalAging.SphereInitialLaw.gaussianLaw,
    finrank_euclideanSpace,Fintype.card_fin] using
    gaussian_radius_even_moment (E := Vector m) k

private theorem radialMomentProduct_pos {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    0 < radialMomentProduct m k := by
  apply Finset.prod_pos
  intro j _
  exact_mod_cast (show 0 < m+2*j by omega)

/-- The exact even moment at any fixed physical spherical axis. This
includes `m=1` and `k=0` with no exceptional normalization. -/
theorem sphere_axis_even_moment (m : ℕ) (hm : 1 ≤ m) (k : ℕ)
    (x : Vector m) (hx : ‖x‖^2=(m:ℝ)) :
    (∫ y, (overlap x y)^(2*k) ∂sphereLaw m) =
      ∏ j ∈ Finset.range k, ((2*j+1:ℕ):ℝ)/((m+2*j:ℕ):ℝ) := by
  let ν := SphericalAging.SphereInitialLaw.gaussianLaw m
  let f : Vector m → ℝ := fun y => (overlap x y)^(2*k)
  have hf : Measurable f := by dsimp [f]; unfold overlap; fun_prop
  have hI := (normalize_independent_radius hm).comp hf
    (show Measurable (fun r : ℝ => r^(2*k)) by fun_prop)
  have hfactor := hI.integral_fun_mul_eq_mul_integral
    (hf.comp (SphericalAging.SphereInitialLaw.normalize_measurable m)).aestronglyMeasurable
    (by fun_prop)
  simp only [Function.comp_def] at hfactor
  have hprod : (fun g : Vector m =>
      f (SphericalAging.SphereInitialLaw.normalize m g)*‖g‖^(2*k)) =ᵐ[ν]
      (fun g => (inner ℝ (spin x) g)^(2*k)) := by
    filter_upwards [SphericalAging.SphereInitialLaw.gaussian_ne_zero_ae hm] with g hg
    dsimp [f]
    rw [overlap_normalize_eq m hm,div_pow,
      div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hg))]
  rw [integral_congr_ae hprod] at hfactor
  have hmap : (∫ g : Vector m, f (SphericalAging.SphereInitialLaw.normalize m g) ∂ν) =
      ∫ y, f y ∂sphereLaw m := by
    exact (integral_map (SphericalAging.SphereInitialLaw.normalize_measurable m).aemeasurable
      hf.aestronglyMeasurable).symm
  rw [hmap] at hfactor
  have hunit : ‖spin x‖=1 := spin_norm hm x ((onSphere_iff_norm_sq x).mpr hx)
  have hproj := (unit_gaussian_projection_hasLaw (spin x) hunit).integral_comp
    (show AEStronglyMeasurable (fun t : ℝ => t^(2*k)) (gaussianReal 0 1) by fun_prop)
  rw [← stdGaussian_real_eq] at hproj
  have hreal : (∫ t : ℝ, t^(2*k) ∂stdGaussian ℝ) = radialMomentProduct 1 k := by
    have hh := gaussian_radius_even_moment (E := ℝ) k
    simpa only [Module.finrank_self,Real.norm_eq_abs,
      (even_two_mul k).pow_abs] using hh
  rw [hreal] at hproj
  simp only [Function.comp_def] at hproj
  change (∫ g : Vector m, (inner ℝ (spin x) g)^(2*k) ∂ν)=radialMomentProduct 1 k at hproj
  have hrad : (∫ g : Vector m, ‖g‖^(2*k) ∂ν)=radialMomentProduct m k := by
    exact gaussianNormMoment_even m k
  rw [hproj,hrad] at hfactor
  have hquot : (∫ y, f y ∂sphereLaw m)=radialMomentProduct 1 k/radialMomentProduct m k :=
    (eq_div_iff (radialMomentProduct_pos hm k).ne').mpr hfactor.symm
  rw [hquot]
  unfold radialMomentProduct
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  congr 2
  omega

/-- Literal pair-overlap formula of manuscript `lem:pc-spherical`, with
both independent uniform spherical vectors and every dimension `m≥1`. -/
theorem sphere_pair_even_moment (m : ℕ) (hm : 1 ≤ m) (k : ℕ) :
    (∫ z : Vector m × Vector m, (overlap z.1 z.2)^(2*k)
      ∂(sphereLaw m).prod (sphereLaw m)) =
      ∏ j ∈ Finset.range k, ((2*j+1:ℕ):ℝ)/((m+2*j:ℕ):ℝ) := by
  have hi : Integrable (fun z : Vector m × Vector m => (overlap z.1 z.2)^(2*k))
      ((sphereLaw m).prod (sphereLaw m)) := by
    exact (memLp_spherePair_continuous hm (by unfold overlap; fun_prop) 1).integrable le_rfl
  rw [integral_prod _ hi]
  calc
    _ = ∫ _x : Vector m, ∏ j ∈ Finset.range k,
        ((2*j+1:ℕ):ℝ)/((m+2*j:ℕ):ℝ) ∂sphereLaw m := by
      apply integral_congr_ae
      filter_upwards [sphereLaw_support hm] with x hx
      exact sphere_axis_even_moment m hm k x hx
    _ = _ := by simp

/-- Sharp exponential-square comparison at a fixed spherical axis. The
Jensen argument allows negative `ℓ` as well as every `ℓ<m/2`. -/
theorem sphere_axis_exp_square_sharp (m : ℕ) (hm : 1 ≤ m)
    (x : Vector m) (hx : ‖x‖^2=(m:ℝ)) {ℓ : ℝ} (hℓ : ℓ < (m:ℝ)/2) :
    (∫ y, Real.exp (ℓ*(overlap x y)^2) ∂sphereLaw m) ≤
      (1-2*ℓ/(m:ℝ))^(-(1/2:ℝ)) := by
  let G := SphericalAging.SphereInitialLaw.gaussianLaw m
  let ρ := G.map (fun g : Vector m => ‖g‖)
  let τ := ℓ/(m:ℝ)
  have hmR : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hτ : τ < 1/2 := (div_lt_iff₀ hmR).mpr (by nlinarith only [hℓ])
  have hunit : ‖spin x‖=1 := spin_norm hm x ((onSphere_iff_norm_sq x).mpr hx)
  have hproj : Integrable (fun g : Vector m => Real.exp (τ*(inner ℝ (spin x) g)^2)) G :=
    unit_projection_exp_sq_integrable (spin x) hunit hτ
  let F : Vector m × ℝ → ℝ := fun z => Real.exp (τ*(overlap x z.1)^2*z.2^2)
  have hF : Measurable F := by dsimp [F]; unfold overlap; fun_prop
  have hjoint := (normalize_independent_radius hm).map_prod_eq_prod_map_map
    (SphericalAging.SphereInitialLaw.normalize_measurable m).aemeasurable
    measurable_norm.aemeasurable
  change G.map (fun g : Vector m => (SphericalAging.SphereInitialLaw.normalize m g,‖g‖)) =
    (sphereLaw m).prod ρ at hjoint
  have hjointMeas : Measurable (fun g : Vector m =>
      (SphericalAging.SphereInitialLaw.normalize m g,‖g‖)) :=
    (SphericalAging.SphereInitialLaw.normalize_measurable m).prodMk measurable_norm
  have hidentity : (fun g : Vector m => F (SphericalAging.SphereInitialLaw.normalize m g,‖g‖)) =ᵐ[G]
      (fun g => Real.exp (τ*(inner ℝ (spin x) g)^2)) := by
    filter_upwards [SphericalAging.SphereInitialLaw.gaussian_ne_zero_ae hm] with g hg
    dsimp [F]
    rw [overlap_normalize_eq m hm,div_pow]
    congr 1
    field_simp
  have hFi : Integrable F ((sphereLaw m).prod ρ) := by
    rw [← hjoint]
    apply (integrable_map_measure hF.aestronglyMeasurable hjointMeas.aemeasurable).mpr
    exact hproj.congr hidentity.symm
  have hFint : (∫ z, F z ∂(sphereLaw m).prod ρ) =
      (∫ g : Vector m, Real.exp (τ*(inner ℝ (spin x) g)^2) ∂G) := by
    rw [← hjoint,integral_map hjointMeas.aemeasurable hF.aestronglyMeasurable]
    exact integral_congr_ae hidentity
  have : IsProbabilityMeasure ρ := by dsimp [ρ]; infer_instance
  have hρ2i : Integrable (fun r : ℝ => r^2) ρ := by
    apply (integrable_map_measure (by fun_prop) measurable_norm.aemeasurable).mpr
    exact gaussian_norm_pow_integrable m 2
  have hρ2 : (∫ r : ℝ, r^2 ∂ρ)=(m:ℝ) := by
    rw [integral_map measurable_norm.aemeasurable (by fun_prop)]
    exact gaussianNormMoment_two m
  have hJensen (y : Vector m) (hy : ‖y‖^2=(m:ℝ)) :
      Real.exp (ℓ*(overlap x y)^2) ≤ ∫ r : ℝ, F (y,r) ∂ρ := by
    have hrange := overlap_mem_Icc_of_norm_sq hm x y hx hy
    have hsquare : (overlap x y)^2 ≤ 1 := by nlinarith [hrange.1,hrange.2]
    let t := τ*(overlap x y)^2
    have ht : t < 1/2 := by
      by_cases hτ0 : 0 ≤ τ
      · exact (mul_le_of_le_one_right hτ0 hsquare).trans_lt hτ
      · have hnon : t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hτ0) (sq_nonneg _)
        linarith
    have hexp : Integrable (fun r : ℝ => Real.exp (t*r^2)) ρ := by
      apply (integrable_map_measure (by fun_prop) measurable_norm.aemeasurable).mpr
      exact GaussianShell.integrable_exp_norm_sq ht
    have hh := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
      isClosed_univ (.of_forall fun _ => mem_univ _)
      (hρ2i.const_mul t) hexp
    rw [integral_const_mul,hρ2] at hh
    have hcancel : t*(m:ℝ)=ℓ*(overlap x y)^2 := by dsimp [t,τ]; field_simp
    rw [hcancel] at hh
    exact hh
  have hiSphere : Integrable (fun y : Vector m => Real.exp (ℓ*(overlap x y)^2)) (sphereLaw m) :=
    integrable_sphereSupported_continuous (sphereLaw m) (sphereLaw_support hm)
      (by unfold overlap; fun_prop)
  have hbound := integral_mono_ae hiSphere hFi.integral_prod_left (by
    filter_upwards [sphereLaw_support hm] with y hy
    exact hJensen y hy)
  rw [← integral_prod F hFi,hFint] at hbound
  have heval := unit_gaussian_projection_exp_sq (spin x) hunit hτ
  change (∫ g : Vector m, Real.exp (τ*(inner ℝ (spin x) g)^2) ∂G) = _ at heval
  rw [heval] at hbound
  convert hbound using 1
  rw [show 2*ℓ/(m:ℝ)=2*τ by dsimp [τ]; ring]
  congr 1
  ring

/-- The printed sharp MGF bound for two independent uniform spherical
vectors, for every dimension including one and every real `ℓ<m/2`. -/
theorem sphere_pair_exp_square_sharp (m : ℕ) (hm : 1 ≤ m) {ℓ : ℝ}
    (hℓ : ℓ < (m:ℝ)/2) :
    (∫ z : Vector m × Vector m, Real.exp (ℓ*(overlap z.1 z.2)^2)
      ∂(sphereLaw m).prod (sphereLaw m)) ≤
      (1-2*ℓ/(m:ℝ))^(-(1/2:ℝ)) := by
  have hi : Integrable (fun z : Vector m × Vector m => Real.exp (ℓ*(overlap z.1 z.2)^2))
      ((sphereLaw m).prod (sphereLaw m)) := by
    exact (memLp_spherePair_continuous hm (by unfold overlap; fun_prop) 1).integrable le_rfl
  rw [integral_prod _ hi]
  have hh := integral_mono_ae hi.integral_prod_left
    (integrable_const ((1-2*ℓ/(m:ℝ))^(-(1/2:ℝ)))) (by
      filter_upwards [sphereLaw_support hm] with x hx
      exact sphere_axis_exp_square_sharp m hm x hx hℓ)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

end SlowEquilibration.SourceSphericalSharpMoments
