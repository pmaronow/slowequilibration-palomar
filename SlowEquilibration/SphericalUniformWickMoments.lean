-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiRadialIndependence
public import SlowEquilibration.GaussianNormMean
public import FourPapersCommon.GaussianCovarianceWickSum
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

/-! Literal uniform-sphere tensor moments. The radial coefficient is the
actual standard Gaussian norm moment. Gaussian Wick contractions and the
proved angular/radius independence give the sphere identity without a
moment hypothesis. Jensen supplies its uniform dimensional bound. -/

@[expose] public section
namespace SlowEquilibration.SphericalUniformWickMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open SphericalParisiRadialIndependence FourPapersCommon
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def gaussianNormMoment (N p : ℕ) : ℝ := ∫ x : Vector N, ‖x‖^p ∂gaussianLaw N

theorem gaussian_norm_pow_integrable (N p : ℕ) :
    Integrable (fun x : Vector N => ‖x‖^p) (gaussianLaw N) := by
  change Integrable (fun x : Vector N => ‖x‖^p) (stdGaussian (Vector N))
  exact (IsGaussian.memLp_id (stdGaussian (Vector N)) p (by simp)).integrable_norm_pow'

theorem gaussianNormMoment_pos {N : ℕ} (hN : 1 ≤ N) (p : ℕ) :
    0 < gaussianNormMoment N p := by
  apply (integral_pos_iff_support_of_nonneg (fun x => pow_nonneg (norm_nonneg x) p)
    (gaussian_norm_pow_integrable N p)).mpr
  have hs : Function.support (fun x : Vector N => ‖x‖^p) =ᵐ[gaussianLaw N] univ := by
    filter_upwards [gaussian_ne_zero_ae hN] with x hx
    simp only [mem_support,mem_univ]
    exact eq_true (pow_ne_zero p (norm_ne_zero_iff.mpr hx))
  rw [measure_congr hs]
  simp

theorem gaussianNormMoment_zero (N : ℕ) : gaussianNormMoment N 0=1 := by
  simp [gaussianNormMoment]

theorem gaussianNormMoment_two (N : ℕ) : gaussianNormMoment N 2=N := by
  simpa only [gaussianNormMoment,gaussianLaw,finrank_euclideanSpace,Fintype.card_fin] using
    (GaussianNormMean.integral_norm_sq_stdGaussian (E := Vector N))

/-- The actual even Gaussian radial moment dominates N^j in every dimension. -/
theorem gaussianNormMoment_even_ge (N j : ℕ) : (N : ℝ)^j ≤ gaussianNormMoment N (2*j) := by
  have hi : Integrable (fun x : Vector N => (‖x‖^2)^j) (gaussianLaw N) := by
    simpa only [←pow_mul] using gaussian_norm_pow_integrable N (2*j)
  have h := (convexOn_pow (𝕜 := ℝ) j).map_integral_le
    (continuous_pow j).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun x : Vector N => sq_nonneg ‖x‖))
    (gaussian_norm_pow_integrable N 2) hi
  change (gaussianNormMoment N 2)^j ≤ _ at h
  rw [gaussianNormMoment_two] at h
  simpa only [Function.comp_def,←pow_mul,gaussianNormMoment] using h

def sphereWickCoefficient (N p : ℕ) : ℝ := (Real.sqrt N)^p/gaussianNormMoment N p

theorem sphereWickCoefficient_zero (N : ℕ) : sphereWickCoefficient N 0=1 := by
  simp only [sphereWickCoefficient,pow_zero,gaussianNormMoment_zero,div_one]

theorem sphereWickCoefficient_pos {N : ℕ} (hN : 1 ≤ N) (p : ℕ) :
    0 < sphereWickCoefficient N p :=
  div_pos (pow_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0 < N))) p)
    (gaussianNormMoment_pos hN p)

/-- Exact scalar coefficient of the uniform even tensor moment, with a
true dimension-uniform bound obtained from the actual radial law. -/
theorem sphereWickCoefficient_even_mem_unit {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    sphereWickCoefficient N (2*j) ∈ Icc 0 1 := by
  have hm := gaussianNormMoment_pos hN (2*j)
  constructor
  · exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hm.le
  · apply (div_le_one hm).mpr
    have he : (Real.sqrt N)^(2*j)=(N : ℝ)^j := by
      rw [pow_mul,Real.sq_sqrt (Nat.cast_nonneg N)]
    rw [he]
    exact gaussianNormMoment_even_ge N j

/-- Full labeled uniform-sphere Wick identity for the literal Gaussian
normalization measure. Directions may coincide; labels remain distinct. -/
theorem actual_sphere_finset_linear_product_eq_wick {N : ℕ} (hN : 1 ≤ N)
    {κ : Type} [DecidableEq κ] (I : Finset κ) (u : κ → Vector N) :
    (∫ x : Vector N, ∏ i ∈ I,inner ℝ (u i) x ∂sphereLaw N)=
      sphereWickCoefficient N I.card*covarianceWickSum (fun i j => inner ℝ (u i) (u j)) I := by
  let f : Vector N → ℝ := fun x => ∏ i ∈ I,inner ℝ (u i) x
  have hf : Measurable f := by unfold f;fun_prop
  have hI : IndepFun (fun x : Vector N => f (normalize N x))
      (fun x => ‖x‖^I.card) (gaussianLaw N) :=
    (normalize_independent_radius hN).comp hf
      (show Measurable (fun t : ℝ => t^I.card) from (continuous_id.pow I.card).measurable)
  have hfactor := hI.integral_fun_mul_eq_mul_integral
    (hf.comp (normalize_measurable N)).aestronglyMeasurable (by fun_prop)
  have he : (fun x : Vector N => f (normalize N x)*‖x‖^I.card)=ᵐ[gaussianLaw N]
      (fun x => (Real.sqrt N)^I.card*f x) := by
    filter_upwards [gaussian_ne_zero_ae hN] with x hx
    have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
    dsimp only [f,SphericalAging.SphereInitialLaw.normalize]
    simp only [real_inner_smul_right,Finset.prod_mul_distrib,Finset.prod_const,
      div_pow]
    field_simp [hn]
  rw [integral_congr_ae he,integral_const_mul] at hfactor
  have hmap : (∫ x,f (normalize N x) ∂gaussianLaw N)=∫ x,f x ∂sphereLaw N := by
    rw [sphereLaw,integral_map (normalize_measurable N).aemeasurable hf.aestronglyMeasurable]
  have hwick : (∫ x,f x ∂gaussianLaw N)=
      covarianceWickSum (fun i j => inner ℝ (u i) (u j)) I := by
    rw [gaussianLaw]
    exact (integral_gaussian_linear_product_eq_wick I u).trans
      (gaussianLinearWickSum_eq_covariance u I)
  rw [hmap,hwick] at hfactor
  have hm : gaussianNormMoment N I.card≠0 := (gaussianNormMoment_pos hN I.card).ne'
  change (Real.sqrt N)^I.card*covarianceWickSum (fun i j => inner ℝ (u i) (u j)) I=
    (∫ x,f x ∂sphereLaw N)*gaussianNormMoment N I.card at hfactor
  change (∫ x,f x ∂sphereLaw N)=_
  unfold sphereWickCoefficient
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hm).mpr
  exact hfactor.symm

/-- Dimension-uniform full ordered tensor form of the sphere identity. -/
theorem actual_sphere_linear_product_eq_wick {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    (u : Fin p → Vector N) :
    (∫ x : Vector N, ∏ i : Fin p,inner ℝ (u i) x ∂sphereLaw N)=
      sphereWickCoefficient N p*covarianceWickSum (fun i j => inner ℝ (u i) (u j)) Finset.univ := by
  simpa only [Finset.card_univ,Fintype.card_fin] using
    actual_sphere_finset_linear_product_eq_wick hN Finset.univ u

/-- Every literal spherical tensor product is integrable under its true law. -/
theorem sphere_finset_linear_product_integrable {N : ℕ} (hN : 1 ≤ N)
    {κ : Type} [DecidableEq κ] (I : Finset κ) (u : κ → Vector N) :
    Integrable (fun x : Vector N => ∏ i ∈ I,inner ℝ (u i) x) (sphereLaw N) := by
  apply Integrable.of_bound (by fun_prop) ((∏ i ∈ I,‖u i‖)*(Real.sqrt N)^I.card)
  filter_upwards [sphereLaw_norm_ae hN] with x hx
  rw [Real.norm_eq_abs,Finset.abs_prod]
  calc
    _ ≤ ∏ i ∈ I,‖u i‖*Real.sqrt N :=
      Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => by
        simpa only [hx] using abs_real_inner_le_norm (u i) x)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]

/-- Odd uniform tensor moments vanish by the actual antipodal symmetry. -/
theorem actual_sphere_finset_linear_product_odd_zero {N : ℕ}
    {κ : Type} [DecidableEq κ] (I : Finset κ) (hI : Odd I.card) (u : κ → Vector N) :
    (∫ x : Vector N,∏ i ∈ I,inner ℝ (u i) x ∂sphereLaw N)=0 := by
  let f : Vector N → ℝ := fun x => ∏ i ∈ I,inner ℝ (u i) x
  have he (x : Vector N) : f (-x)=-f x := by
    dsimp only [f]
    simp only [inner_neg_right]
    rw [Finset.prod_neg, hI.neg_one_pow, neg_one_mul]
  have hmap := sphereLaw_rotation_invariant (N := N) (LinearIsometryEquiv.neg ℝ)
  have hh := congrArg (fun ν : Measure (Vector N) => ∫ x,f x ∂ν) hmap
  rw [integral_map (by fun_prop) (by unfold f;fun_prop)] at hh
  change (∫ x,f (-x) ∂sphereLaw N)=∫ x,f x ∂sphereLaw N at hh
  simp_rw [he] at hh
  rw [integral_neg] at hh
  change (∫ x,f x ∂sphereLaw N)=0
  linarith

/-- Every odd Gram Wick contraction vanishes, proved from the true spherical
moment and its positive actual radial coefficient. -/
theorem covarianceWickSum_odd_gram_zero {N : ℕ} (hN : 1 ≤ N)
    {κ : Type} [DecidableEq κ] (I : Finset κ) (hI : Odd I.card) (u : κ → Vector N) :
    covarianceWickSum (fun i j => inner ℝ (u i) (u j)) I=0 := by
  have h := actual_sphere_finset_linear_product_odd_zero I hI u
  rw [actual_sphere_finset_linear_product_eq_wick hN] at h
  exact (mul_eq_zero.mp h).resolve_left (sphereWickCoefficient_pos hN I.card).ne'

end
end SlowEquilibration.SphericalUniformWickMoments
