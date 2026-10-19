-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeTangentObservable
public import SlowEquilibration.SphericalLatitudeTensorMoments
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Actual radial derivative of the latitude field and its literal tangent
observable. The mean derivative is proved under the genuine regular
ordered-tensor event by locally dominated differentiation of the actual
sphere integral; no conditional mean identity is assumed. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm
open scoped RealInnerProductSpace Topology
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The true latitude scale derivative, retaining the finite-dimensional
ambient/tangent normalization. -/
theorem latitudeScale_hasDerivAt {n : ℕ} (hn : 1 ≤ n) {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    HasDerivAt (SphericalLatitudeTensorMoments.latitudeScale n)
      (-r*SphericalLatitudeTensorMoments.latitudeScale n r/(1-r^2)) r := by
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : 0 < 1-r^2 := by nlinarith [hr.1,hr.2]
  have hk : 0 < ((n+1 : ℕ) : ℝ)/(n : ℝ) := div_pos (by positivity) hnr
  have hf := (((hasDerivAt_id r).pow 2).const_sub 1).const_mul (((n+1 : ℕ) : ℝ)/(n : ℝ))
  have hd := hf.sqrt (mul_pos hk hs).ne'
  have hsq := Real.sq_sqrt (mul_pos hk hs).le
  have hsqrt : Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))≠0 :=
    (Real.sqrt_pos.mpr (mul_pos hk hs)).ne'
  have hd' : HasDerivAt (fun t : ℝ => Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-t^2)))
      ((((n+1 : ℕ) : ℝ)/(n : ℝ))*(-(2*r))/(2*Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2)))) r := by
    simpa only [id_eq,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] using hd
  unfold SphericalLatitudeTensorMoments.latitudeScale
  apply hd'.congr_deriv
  apply (div_eq_div_iff (mul_ne_zero (by norm_num) hsqrt) hs.ne').mpr
  nlinarith [congrArg (fun z : ℝ => r*z) hsq]

/-- Every actual latitude curve has the spherical tangent velocity
Π_v u/(1-r²); this is a pointwise equality before integration. -/
theorem latitudeMap_radial_hasDerivAt {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y,inner ℝ (e y) u=0)
    {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) (y : Vector n) :
    HasDerivAt (fun t => latitudeMap u e t y)
      ((1-r^2)⁻¹ • tangentProjection (latitudeMap u e r y) u) r := by
  have hs : 1-r^2≠0 := (show 0 < 1-r^2 by nlinarith [hr.1,hr.2]).ne'
  have hd := ((hasDerivAt_id r).smul_const u).add
    ((latitudeScale_hasDerivAt hn hr).smul_const (e y))
  have ho := overlap_latitude_center u hu e he r y
  have hp : tangentProjection (latitudeMap u e r y) u=u-r•latitudeMap u e r y := by
    rw [SphericalForm.tangentProjection_apply,SphericalAging.HardSphereDynamics.projection]
    exact congrArg (fun s : ℝ => u-s•latitudeMap u e r y) ho
  have hfun : ((fun t : ℝ => id t•u)+fun t =>
      SphericalLatitudeTensorMoments.latitudeScale n t•e y)=(fun t => latitudeMap u e t y) := by
    funext t
    rfl
  rw [hfun] at hd
  simp only [one_smul] at hd
  apply hd.congr_deriv
  symm
  rw [hp,latitudeMap]
  unfold SphericalLatitudeTensorMoments.latitudeScale
  simp only [smul_sub,smul_add,smul_smul,div_eq_mul_inv]
  have hunit : (1-r^2)⁻¹-r*(r*(1-r^2)⁻¹)=1 := by field_simp [hs]
  calc
    _=((1-r^2)⁻¹-r*(r*(1-r^2)⁻¹))•u+
        (-r*Real.sqrt (((n+1 : ℕ) : ℝ)*(n : ℝ)⁻¹*(1-r^2))*(1-r^2)⁻¹)•e y := by module
    _=_ := by rw [hunit,one_smul]

/-- Literal source tangent-gradient/radial-derivative identity for the
original mixed ordered tensor field, at every latitude point. -/
theorem actual_latitude_field_radial_hasDerivAt {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y,inner ℝ (e y) u=0)
    {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) (y : Vector n) :
    HasDerivAt (fun t => field c J (latitudeMap u e t y))
      (Real.sqrt ((n+1 : ℕ) : ℝ)/(1-r^2)*observable c J u (latitudeMap u e r y)) r := by
  have hd := ((field_contDiff c J).differentiable (by simp)
    (latitudeMap u e r y)).hasFDerivAt.comp_hasDerivAt r
      (latitudeMap_radial_hasDerivAt hn u hu e he hr y)
  have hs : Real.sqrt ((n+1 : ℕ) : ℝ)≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  change HasDerivAt (fun t => field c J (latitudeMap u e t y)) _ r at hd
  apply hd.congr_deriv
  rw [map_smul,←inner_surfaceGradient]
  unfold observable
  simp only [smul_eq_mul]
  field_simp [hs]

def latitudeFieldMean {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (r : ℝ) : ℝ :=
  ∫ v,field c J v ∂latitudeLaw u e r

def latitudeObservableMean {n P : ℕ} (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (r : ℝ) : ℝ :=
  ∫ v,observable c J u v ∂latitudeLaw u e r

/-- Differentiation of the actual latitude mean is justified by the true
ordered tensor regularity event and the genuine fixed sphere seed measure. -/
theorem actual_latitudeFieldMean_hasDerivAt {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y,inner ℝ (e y) u=0)
    {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    HasDerivAt (latitudeFieldMean c J u e)
      (Real.sqrt ((n+1 : ℕ) : ℝ)/(1-r^2)*latitudeObservableMean c J u e r) r := by
  let R : ℝ := (1+|r|)/2
  have hrabs : |r| < 1 := abs_lt.mpr hr
  have hR0 : 0 < R := by dsimp [R];linarith [abs_nonneg r]
  have hR1 : R < 1 := by dsimp [R];linarith
  have hrR : |r| < R := by dsimp [R];linarith
  have hden : 0 < 1-R^2 := by nlinarith
  let F : ℝ → Vector n → ℝ := fun t y => field c J (latitudeMap u e t y)
  let D : ℝ → Vector n → ℝ := fun t y =>
    Real.sqrt ((n+1 : ℕ) : ℝ)/(1-t^2)*observable c J u (latitudeMap u e t y)
  let B : ℝ := derivativeConstant c*((n+1 : ℕ) : ℝ)/(1-R^2)
  have ht (t : ℝ) (h : t∈Ioo (-R) R) : t∈Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [h.1,h.2]
  have hsphere : ∀ᵐ y ∂sphereLaw n,‖y‖^2=(n : ℝ) := sphereLaw_support hn
  have hFint : Integrable (F r) (sphereLaw n) := by
    apply Integrable.of_bound (((field_contDiff c J).continuous.comp
      (latitudeMap_continuous u e r)).aestronglyMeasurable) (derivativeConstant c*((n+1 : ℕ) : ℝ))
    filter_upwards [hsphere] with y hy
    have hv := latitudeMap_norm_sq hn u hu e he hrabs.le y hy
    exact (field_regularDisorder_ball_bounds (by omega) c J hJ _
      (SphericalAging.LandscapeDerivatives.sphere_norm _ hv).le).1
  have hb : ∀ᵐ y ∂sphereLaw n,∀ t∈Ioo (-R) R,‖D t y‖ ≤ B := by
    filter_upwards [hsphere] with y hy
    intro t htr
    have htr' := ht t htr
    have hdt : 0 < 1-t^2 := by nlinarith [htr'.1,htr'.2]
    have hsq : t^2 ≤ R^2 := by nlinarith [htr.1,htr.2]
    have hv := latitudeMap_norm_sq hn u hu e he (abs_lt.mpr htr').le y hy
    have ho := observable_abs_le (by omega) c J hJ u _ hu hv
    dsimp only [D,B]
    rw [Real.norm_eq_abs,abs_mul,abs_div,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos hdt]
    calc
      _ ≤ Real.sqrt ((n+1 : ℕ) : ℝ)/(1-t^2)*(derivativeConstant c*Real.sqrt ((n+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left ho (by positivity)
      _ = derivativeConstant c*((n+1 : ℕ) : ℝ)/(1-t^2) := by
        rw [div_mul_eq_mul_div]
        congr 1
        calc
          _=derivativeConstant c*(Real.sqrt ((n+1 : ℕ) : ℝ))^2 := by ring
          _=_ := by rw [Real.sq_sqrt (by positivity)]
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (derivativeConstant_pos c).le (Nat.cast_nonneg _)) hden (by linarith)
  have hd : ∀ᵐ y ∂sphereLaw n,∀ t∈Ioo (-R) R,HasDerivAt (fun z => F z y) (D t y) t :=
    Filter.Eventually.of_forall (fun y t htr => actual_latitude_field_radial_hasDerivAt hn c J u hu e he (ht t htr) y)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (isOpen_Ioo.mem_nhds (abs_lt.mp hrR))
    (Filter.Eventually.of_forall (fun t => ((field_contDiff c J).continuous.comp
      (latitudeMap_continuous u e t)).aestronglyMeasurable)) hFint
    (by dsimp [D];exact (((observable_continuous c J u).comp
      (latitudeMap_continuous u e r)).aestronglyMeasurable).const_mul _) hb
    (integrable_const B) hd
  have hmean (t : ℝ) : (∫ y,F t y ∂sphereLaw n)=latitudeFieldMean c J u e t := by
    rw [latitudeFieldMean,latitudeLaw,integral_map
      (latitudeMap_continuous u e t).measurable.aemeasurable (field_contDiff c J).continuous.aestronglyMeasurable]
  have hobs : (∫ y,D r y ∂sphereLaw n)=
      Real.sqrt ((n+1 : ℕ) : ℝ)/(1-r^2)*latitudeObservableMean c J u e r := by
    dsimp only [D]
    rw [integral_const_mul,latitudeObservableMean,latitudeLaw,integral_map
      (latitudeMap_continuous u e r).measurable.aemeasurable (observable_continuous c J u).aestronglyMeasurable]
  have hfun : (fun t => ∫ y,F t y ∂sphereLaw n)=latitudeFieldMean c J u e := by
    funext t
    exact hmean t
  have hdmean := h.2
  change HasDerivAt (fun t => ∫ y,F t y ∂sphereLaw n) (∫ y,D r y ∂sphereLaw n) r at hdmean
  rw [hfun,hobs] at hdmean
  exact hdmean

/-- Exact source radial-mean representation of the true latitude average
of the sampled field's own tangent observable. -/
theorem actual_latitudeObservableMean_eq_radial_derivative {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n+1) P) (hJ : J∈regularDisorder)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y,inner ℝ (e y) u=0)
    {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    latitudeObservableMean c J u e r=(1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*
      deriv (latitudeFieldMean c J u e) r := by
  rw [(actual_latitudeFieldMean_hasDerivAt hn c J hJ u hu e he hr).deriv]
  have hs : 1-r^2≠0 := (show 0 < 1-r^2 by nlinarith [hr.1,hr.2]).ne'
  have hnz : Real.sqrt ((n+1 : ℕ) : ℝ)≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hs,hnz]

end
end SlowEquilibration.EntranceLatitudeTangentObservable
