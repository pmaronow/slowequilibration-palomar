-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianOverlapBounds
public import SlowEquilibration.SpherePolarIntegral
public import SlowEquilibration.SphericalLinearEndpoint

@[expose] public section

/-! Sharp subcritical spherical overlap moments from the genuine independent
Gaussian radius and angular law. The radius restriction costs only its actual
probability; there is no artificial exceptional-radius exponential term. -/

noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open SphereVolume SphericalAging.HardSphereDynamics
open scoped Topology RealInnerProductSpace ENNReal
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem angular_exp_square_integrable {N : ℕ} [NeZero N] (e : Vector N)
    (he : ‖e‖=1) (b : ℝ) :
    Integrable (fun u : Metric.sphere (0 : Vector N) 1 =>
      Real.exp (b*(inner ℝ e (u : Vector N))^2)) (unitAngular (Vector N)) := by
  apply (integrable_const (Real.exp |b|)).mono' (by fun_prop)
  filter_upwards [] with u
  have hu : ‖(u : Vector N)‖=1 := by simp
  have hi : |inner ℝ e (u : Vector N)|≤1 := by
    simpa [he,hu] using abs_real_inner_le_norm e (u : Vector N)
  have hi2 : (inner ℝ e (u : Vector N))^2≤1 := by
    nlinarith [abs_nonneg (inner ℝ e (u : Vector N)),sq_abs (inner ℝ e (u : Vector N))]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ |b| * (inner ℝ e (u : Vector N))^2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)
    _ ≤ |b| * 1 := mul_le_mul_of_nonneg_left hi2 (abs_nonneg _)
    _ = _ := mul_one _

private theorem gaussian_projection_exp_square_integral {N : ℕ}
    (e : Vector N) (he : ‖e‖=1) {b : ℝ} (hb : b<1/2) :
    (∫g : Vector N,Real.exp (b*(inner ℝ e g)^2) ∂stdGaussian (Vector N))=
      (1-2*b)^(-(1:ℝ)/2) := by
  have h := (unit_gaussian_projection_hasLaw e he).integral_comp
    (show AEStronglyMeasurable (fun z : ℝ => Real.exp (b*z^2)) (gaussianReal 0 1) by fun_prop)
  dsimp only [Function.comp_apply] at h
  rw [h,← stdGaussian_real_eq]
  simpa only [Real.norm_eq_abs,sq_abs,Module.finrank_self,Nat.cast_one,neg_div] using
    GaussianShell.integral_exp_norm_sq (E := ℝ) hb

/-- Finite-dimensional bound on the literal sphere overlap. The only displayed
radius premise is an actual finite Gaussian-shell mass, eliminated in the next
uniform eventual theorem. -/
theorem sphere_overlap_exp_square_shell_le {N : ℕ} (hN : 1≤N)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) {b r : ℝ}
    (hb : 0≤b) (hr : 0<r) (hsub : b/r^2<1/2)
    (hmass : (1/2:ℝ)≤(gaussianRadius (Vector N)).real
      {s : Ioi (0:ℝ) | r*Real.sqrt (N:ℝ)≤(s:ℝ) ∧ (s:ℝ)≤2*Real.sqrt (N:ℝ)}) :
    (∫y : Vector N,Real.exp (b*(N:ℝ)*(overlap x y)^2) ∂sphereLaw N)≤
      2*(1-2*(b/r^2))^(-(1:ℝ)/2) := by
  let : NeZero N := ⟨by omega⟩
  have hNp : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  let e := SphericalBarycenter.spin x
  have he : ‖e‖=1 := SphericalBarycenter.spin_norm hN x
    ((onSphere_iff_norm_sq x).mpr hx)
  let I : ℝ := ∫u : Metric.sphere (0 : Vector N) 1,
    Real.exp (b*(N:ℝ)*(inner ℝ e (u : Vector N))^2) ∂unitAngular (Vector N)
  let F := fun s : Ioi (0:ℝ) => ∫u : Metric.sphere (0 : Vector N) 1,
    Real.exp ((b/r^2)*(inner ℝ e ((s:ℝ) • (u : Vector N)))^2) ∂unitAngular (Vector N)
  let S : Set (Ioi (0:ℝ)) := {s | r*Real.sqrt (N:ℝ)≤(s:ℝ) ∧ (s:ℝ)≤2*Real.sqrt (N:ℝ)}
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_subtype_coe).inter
      (measurableSet_le measurable_subtype_coe measurable_const)
  have hIi := angular_exp_square_integrable e he (b*N)
  have hFi : Integrable F (gaussianRadius (Vector N)) :=
    gaussian_polar_integrable_inner (E := Vector N)
      (f := fun g : Vector N => Real.exp ((b/r^2)*(inner ℝ e g)^2))
      (unit_projection_exp_sq_integrable e he hsub)
  have hI0 : 0≤I := integral_nonneg fun _ => (Real.exp_pos _).le
  have hF0 : ∀s,0≤F s := fun s => integral_nonneg fun _ => (Real.exp_pos _).le
  have hmono (s : Ioi (0:ℝ)) (hs : s∈S) : I≤F s := by
    have hUi : Integrable (fun u : Metric.sphere (0 : Vector N) 1 =>
        Real.exp ((b/r^2)*(inner ℝ e ((s:ℝ) • (u : Vector N)))^2))
        (unitAngular (Vector N)) := by
      convert angular_exp_square_integrable e he ((b/r^2)*(s:ℝ)^2) using 1
      funext u
      simp only [real_inner_smul_right,mul_pow]
      congr 1
      ring
    apply integral_mono hIi hUi
    intro u
    apply Real.exp_le_exp.mpr
    have hs2 : r^2*(N:ℝ)≤(s:ℝ)^2 := by
      have hh := (sq_le_sq₀ (mul_nonneg hr.le (Real.sqrt_nonneg _)) s.property.le).mpr hs.1
      simpa only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)] using hh
    have hd : b*(N:ℝ)≤(b/r^2)*(s:ℝ)^2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hs2 hb]
    simpa only [real_inner_smul_right,mul_pow,mul_assoc] using
      mul_le_mul_of_nonneg_right hd (sq_nonneg (inner ℝ e (u : Vector N)))
  have hbound : (1/2:ℝ)*I≤(1-2*(b/r^2))^(-(1:ℝ)/2) := by
    calc
      _ ≤ (gaussianRadius (Vector N)).real S*I := mul_le_mul_of_nonneg_right hmass hI0
      _ = ∫_ in S,I ∂gaussianRadius (Vector N) := by simp [Measure.real]
      _ ≤ ∫s in S,F s ∂gaussianRadius (Vector N) :=
        setIntegral_mono_on (integrable_const _) hFi.integrableOn hS hmono
      _ ≤ ∫s,F s ∂gaussianRadius (Vector N) :=
        setIntegral_le_integral hFi (Filter.Eventually.of_forall hF0)
      _ = ∫g : Vector N,Real.exp ((b/r^2)*(inner ℝ e g)^2) ∂stdGaussian (Vector N) :=
        (gaussian_polar_integral (E := Vector N)
          (f := fun g : Vector N => Real.exp ((b/r^2)*(inner ℝ e g)^2))
          (unit_projection_exp_sq_integrable e he hsub)).symm
      _ = _ := gaussian_projection_exp_square_integral e he hsub
  have hmap : (∫y : Vector N,Real.exp (b*(N:ℝ)*(overlap x y)^2) ∂sphereLaw N)=I := by
    rw [sphereLaw,sphereLaw_eq_normalized_angular N hN,integral_map (by fun_prop) (by unfold overlap; fun_prop)]
    apply integral_congr_ae
    exact .of_forall fun u => by
      dsimp [overlap,e,SphericalBarycenter.spin]
      simp only [real_inner_smul_left,real_inner_smul_right]
      have hs : (Real.sqrt (N:ℝ))^2=(N:ℝ) := Real.sq_sqrt hNp.le
      have hs0 : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr hNp).ne'
      field_simp
      rw [hs]
  rw [hmap]
  linarith

/-- Full subcritical range, with every shell-mass input proved internally.
The constant and dimension cutoff are independent of the spherical center. -/
theorem sphere_overlap_exp_square_eventually_bounded {b : ℝ}
    (hb : 0≤b) (hsub : b<1/2) :
    ∃C>0,∀ᶠ N : ℕ in atTop,∀x : Vector N,‖x‖^2=(N:ℝ) →
      (∫y : Vector N,Real.exp (b*(N:ℝ)*(overlap x y)^2) ∂sphereLaw N)≤C := by
  let r := Real.sqrt ((1+2*b)/2)
  have hr : 0<r := Real.sqrt_pos.mpr (by linarith)
  have hrsq : r^2=(1+2*b)/2 := Real.sq_sqrt (by linarith)
  have hr1 : r<1 := by nlinarith [Real.sqrt_nonneg ((1+2*b)/2)]
  have hd : b/r^2<1/2 := by rw [hrsq]; apply (div_lt_iff₀ (by linarith)).mpr; linarith
  have hbase : 0 < 1-2*(b/r^2) := by linarith
  refine ⟨2*(1-2*(b/r^2))^(-(1:ℝ)/2),
    mul_pos (by norm_num) (Real.rpow_pos_of_pos hbase _),?_⟩
  filter_upwards [radial_shell_mass_eventually hr hr1 (show (1:ℝ)<2 by norm_num),
    eventually_ge_atTop 1] with N hm hN
  exact fun x hx => sphere_overlap_exp_square_shell_le hN x hx hb hr hd hm

end SlowEquilibration.SphericalModel
