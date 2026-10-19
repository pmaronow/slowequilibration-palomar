-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeRadialMean

/-! The actual latitude mean derivative holds for every finite ordered
disorder sample, including literal posterior samples. A genuine finite
sample jet bound proves dominated differentiation; regular-disorder
membership is not needed for this calculus identity. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm
open scoped RealInnerProductSpace Topology BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def sampleDerivativeConstant {N P : ℕ} (c : Degree P→ℝ) (J : Disorder N P) : ℝ :=
  1+∑ p : Degree P,Real.sqrt (c p)*((p.val.val : ℝ)+1)*
    SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p)

theorem sampleDerivativeConstant_pos {N P : ℕ} (c : Degree P→ℝ) (J : Disorder N P) :
    0< sampleDerivativeConstant c J := by
  have hs : 0≤∑ p : Degree P,Real.sqrt (c p)*((p.val.val : ℝ)+1)*
      SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p) := by
    apply Finset.sum_nonneg
    intro p hp
    exact mul_nonneg (by positivity) (SphericalAging.GaussianLandscape.landscapeNorm_nonnegative _ _ _)
  unfold sampleDerivativeConstant
  linarith

/-- Explicit finite actual-sample field and gradient bounds. -/
theorem field_sample_ball_bounds {N P : ℕ} (hN : 1≤ N) (c : Degree P→ℝ) (J : Disorder N P)
    (x : Vector N) (hx : ‖x‖≤ Real.sqrt N) :
    |field c J x|≤ sampleDerivativeConstant c J*(N : ℝ) ∧
      ‖gradient (field c J) x‖≤ sampleDerivativeConstant c J*Real.sqrt N := by
  have hs : 0< Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hsum {a : Degree P→ℝ} (ha : ∀ p,a p≤(p.val.val : ℝ)+1) :
      (∑ p : Degree P,Real.sqrt (c p)*a p*
        SphericalAging.GaussianLandscape.landscapeNorm N p.val.val (J p))≤ sampleDerivativeConstant c J := by
    apply le_trans (Finset.sum_le_sum (fun p hp =>
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ha p) (Real.sqrt_nonneg _))
        (SphericalAging.GaussianLandscape.landscapeNorm_nonnegative _ _ _)))
    unfold sampleDerivativeConstant
    linarith
  have hzero := field_iteratedFDeriv_ball_bound hN c J x hx 0
  have hone := field_iteratedFDeriv_ball_bound hN c J x hx 1
  simp only [pow_zero,one_mul,norm_iteratedFDeriv_zero,Real.norm_eq_abs,
    Nat.descFactorial_zero,Nat.cast_one,mul_one] at hzero
  simp only [pow_one,Nat.descFactorial_one] at hone
  have hsz := hsum (a := fun _ => 1) (fun p => by
    have hp : (0 : ℝ)≤p.val.val := Nat.cast_nonneg _
    linarith)
  simp only [mul_one] at hsz
  constructor
  · exact hzero.trans (by
      rw [mul_comm (sampleDerivativeConstant c J)]
      exact mul_le_mul_of_nonneg_left hsz (Nat.cast_nonneg N))
  · have hgrad : ‖gradient (field c J) x‖=‖iteratedFDeriv ℝ 1 (field c J) x‖ := by
      rw [gradient,LinearIsometryEquiv.norm_map,norm_iteratedFDeriv_one]
    rw [hgrad]
    apply (mul_le_mul_iff_right₀ hs).mp
    apply (hone.trans (mul_le_mul_of_nonneg_left
      (hsum (a := fun p => (p.val.val : ℝ)) (fun p => by linarith)) (Nat.cast_nonneg N))).trans_eq
    calc
      _=(Real.sqrt N)^2*sampleDerivativeConstant c J := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]
      _=_ := by ring

theorem observable_sample_abs_le {N P : ℕ} (hN : 1≤ N) (c : Degree P→ℝ) (J : Disorder N P)
    (x u : Vector N) (hx : ‖x‖^2=(N : ℝ)) (hu : ‖u‖^2=(N : ℝ)) :
    |observable c J x u|≤ sampleDerivativeConstant c J*Real.sqrt N := by
  have hs : 0< Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hxn := SphericalAging.LandscapeDerivatives.sphere_norm x hx
  have hun := SphericalAging.LandscapeDerivatives.sphere_norm u hu
  have hgrad := (field_sample_ball_bounds hN c J u hun.le).2
  have hproj : ‖surfaceGradient (field c J) u‖≤‖gradient (field c J) u‖ := by
    unfold surfaceGradient
    apply ((tangentProjection u).le_opNorm _).trans
    have hp := tangentProjection_norm_le (show N≠0 by omega) u ((SphericalAging.HardSphereDynamics.onSphere_iff_norm_sq u).mpr hu)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp (norm_nonneg (gradient (field c J) u))
  unfold observable
  rw [abs_mul,abs_inv,abs_of_pos hs]
  calc
    _≤(Real.sqrt (N : ℝ))⁻¹*(sampleDerivativeConstant c J*Real.sqrt N*Real.sqrt N) := by
      apply mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans _) (inv_nonneg.mpr hs.le)
      rw [hxn]
      exact mul_le_mul_of_nonneg_right (hproj.trans hgrad) hs.le
    _=_ := by field_simp

theorem actual_latitudeFieldMean_allDisorder_hasDerivAt {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
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
  let B : ℝ := sampleDerivativeConstant c J*((n+1 : ℕ) : ℝ)/(1-R^2)
  have ht (t : ℝ) (h : t∈Ioo (-R) R) : t∈Ioo (-1 : ℝ) 1 := by
    constructor <;> linarith [h.1,h.2]
  have hsphere : ∀ᵐ y ∂sphereLaw n,‖y‖^2=(n : ℝ) := sphereLaw_support hn
  have hFint : Integrable (F r) (sphereLaw n) := by
    apply Integrable.of_bound (((field_contDiff c J).continuous.comp
      (latitudeMap_continuous u e r)).aestronglyMeasurable) (sampleDerivativeConstant c J*((n+1 : ℕ) : ℝ))
    filter_upwards [hsphere] with y hy
    have hv := latitudeMap_norm_sq hn u hu e he hrabs.le y hy
    exact (field_sample_ball_bounds (by omega) c J _
      (SphericalAging.LandscapeDerivatives.sphere_norm _ hv).le).1
  have hb : ∀ᵐ y ∂sphereLaw n,∀ t∈Ioo (-R) R,‖D t y‖ ≤ B := by
    filter_upwards [hsphere] with y hy
    intro t htr
    have htr' := ht t htr
    have hdt : 0 < 1-t^2 := by nlinarith [htr'.1,htr'.2]
    have hsq : t^2 ≤ R^2 := by nlinarith [htr.1,htr.2]
    have hv := latitudeMap_norm_sq hn u hu e he (abs_lt.mpr htr').le y hy
    have ho := observable_sample_abs_le (by omega) c J u _ hu hv
    dsimp only [D,B]
    rw [Real.norm_eq_abs,abs_mul,abs_div,abs_of_nonneg (Real.sqrt_nonneg _),abs_of_pos hdt]
    calc
      _ ≤ Real.sqrt ((n+1 : ℕ) : ℝ)/(1-t^2)*(sampleDerivativeConstant c J*Real.sqrt ((n+1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left ho (by positivity)
      _ = sampleDerivativeConstant c J*((n+1 : ℕ) : ℝ)/(1-t^2) := by
        rw [div_mul_eq_mul_div]
        congr 1
        calc
          _=sampleDerivativeConstant c J*(Real.sqrt ((n+1 : ℕ) : ℝ))^2 := by ring
          _=_ := by rw [Real.sq_sqrt (by positivity)]
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (sampleDerivativeConstant_pos c J).le (Nat.cast_nonneg _)) hden (by linarith)
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
theorem actual_latitudeObservableMean_allDisorder_eq_radial_derivative {n P : ℕ} (hn : 1 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y,inner ℝ (e y) u=0)
    {r : ℝ} (hr : r∈Ioo (-1 : ℝ) 1) :
    latitudeObservableMean c J u e r=(1-r^2)/Real.sqrt ((n+1 : ℕ) : ℝ)*
      deriv (latitudeFieldMean c J u e) r := by
  rw [(actual_latitudeFieldMean_allDisorder_hasDerivAt hn c J u hu e he hr).deriv]
  have hs : 1-r^2≠0 := (show 0 < 1-r^2 by nlinarith [hr.1,hr.2]).ne'
  have hnz : Real.sqrt ((n+1 : ℕ) : ℝ)≠0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hs,hnz]


end
end SlowEquilibration.EntranceLatitudeTangentObservable
