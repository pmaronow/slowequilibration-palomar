-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SmoothSwitch
public import SlowEquilibration.SphericalGibbsMass
public import SlowEquilibration.SphericalObservableDisplacement
public import SlowEquilibration.C1SphericalGraph
public import SlowEquilibration.BumpDifferential

/-! Literal smooth cap cutoffs and their genuine spherical energy.
The switch is constructed in `SmoothSwitch`; the exact collar coefficient
4/(N(q₂−q₁)²) follows from its proved derivative bound and true projection. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalCapCutoff

open MeasureTheory Set Filter
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

def cutoff (q₁ q₂ r : ℝ) : ℝ := SmoothSwitch.switch ((r - q₁) / (q₂ - q₁))
def capTrial (q₁ q₂ : ℝ) (u x : Vector N) : ℝ := cutoff q₁ q₂ (overlap x u)
def collarCoefficient (N : ℕ) (q₁ q₂ : ℝ) : ℝ := 4 / ((N : ℝ) * (q₂ - q₁)^2)

lemma cutoff_contDiff (q₁ q₂ : ℝ) : ContDiff ℝ ∞ (cutoff q₁ q₂) :=
  SmoothSwitch.contDiff_switch.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma capTrial_joint_contDiff (q₁ q₂ : ℝ) :
    ContDiff ℝ ∞ (fun z : Vector N × Vector N => capTrial q₁ q₂ z.1 z.2) :=
  (cutoff_contDiff q₁ q₂).comp ((contDiff_snd.inner ℝ contDiff_fst).div_const _)

lemma capTrial_contDiff (q₁ q₂ : ℝ) (u : Vector N) : ContDiff ℝ ∞ (capTrial q₁ q₂ u) := by
  change ContDiff ℝ ∞ (fun x : Vector N => cutoff q₁ q₂ (inner ℝ x u / (N : ℝ)))
  have hR : ContDiff ℝ ∞ (fun x : Vector N => inner ℝ x u / (N : ℝ)) :=
    (contDiff_id.inner ℝ contDiff_const).div_const _
  exact (cutoff_contDiff q₁ q₂).comp hR

lemma cutoff_nonneg (q₁ q₂ r : ℝ) : 0 ≤ cutoff q₁ q₂ r := SmoothSwitch.nonneg _
lemma cutoff_le_one (q₁ q₂ r : ℝ) : cutoff q₁ q₂ r ≤ 1 := SmoothSwitch.le_one _

lemma cutoff_zero {q₁ q₂ r : ℝ} (hq : q₁ < q₂) (hr : r ≤ q₁) : cutoff q₁ q₂ r = 0 :=
  SmoothSwitch.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) (sub_pos.mpr hq).le)

lemma cutoff_one {q₁ q₂ r : ℝ} (hq : q₁ < q₂) (hr : q₂ ≤ r) : cutoff q₁ q₂ r = 1 :=
  SmoothSwitch.one_of_one_le ((one_le_div (sub_pos.mpr hq)).mpr (by linarith))

lemma cutoff_hasDerivAt (q₁ q₂ r : ℝ) :
    HasDerivAt (cutoff q₁ q₂)
      (deriv SmoothSwitch.switch ((r-q₁)/(q₂-q₁)) / (q₂-q₁)) r := by
  convert ((SmoothSwitch.hasDerivAt_switch ((r-q₁)/(q₂-q₁))).comp r
    (((hasDerivAt_id r).sub_const q₁).div_const (q₂-q₁))) using 1
  · rfl
  · rw [SmoothSwitch.deriv_switch]
    simp only [one_div]
    ring

lemma cutoff_abs_deriv {q₁ q₂ : ℝ} (hq : q₁ < q₂) (r : ℝ) :
    |deriv (cutoff q₁ q₂) r| ≤ 2 / (q₂-q₁) := by
  rw [(cutoff_hasDerivAt q₁ q₂ r).deriv, abs_div, abs_of_pos (sub_pos.mpr hq)]
  exact div_le_div_of_nonneg_right (SmoothSwitch.abs_deriv_le_two _) (sub_pos.mpr hq).le

lemma cutoff_deriv_zero_left {q₁ q₂ r : ℝ} (hq : q₁ < q₂) (hr : r < q₁) :
    deriv (cutoff q₁ q₂) r = 0 := by
  have heq : cutoff q₁ q₂ =ᶠ[𝓝 r] (fun _ => (0 : ℝ)) :=
    (eventually_lt_nhds hr).mono (fun s hs => cutoff_zero hq hs.le)
  exact (heq.deriv_eq).trans (deriv_const r (0 : ℝ))

lemma cutoff_deriv_zero_right {q₁ q₂ r : ℝ} (hq : q₁ < q₂) (hr : q₂ < r) :
    deriv (cutoff q₁ q₂) r = 0 := by
  have heq : cutoff q₁ q₂ =ᶠ[𝓝 r] (fun _ => (1 : ℝ)) :=
    (eventually_gt_nhds hr).mono (fun s hs => cutoff_one hq hs.le)
  exact (heq.deriv_eq).trans (deriv_const r (1 : ℝ))

lemma capTrial_gradient (hN : 1 ≤ N) (q₁ q₂ : ℝ) (u x : Vector N) :
    gradient (capTrial q₁ q₂ u) x = ((deriv (cutoff q₁ q₂) (overlap x u)) / (N : ℝ)) • u := by
  have hR : HasFDerivAt (fun y : Vector N => overlap y u) ((N : ℝ)⁻¹ • innerSL ℝ u) x := by
    have hd := ((innerSL ℝ u).hasFDerivAt (x := x)).const_mul (N : ℝ)⁻¹
    convert hd using 1
    · funext y
      simp only [overlap, div_eq_inv_mul]
      rw [real_inner_comm]
      rfl
  have hd := (((cutoff_contDiff q₁ q₂).differentiable (by simp)) (overlap x u)).hasDerivAt.comp_hasFDerivAt x hR
  have hg : HasGradientAt (capTrial q₁ q₂ u)
      (((deriv (cutoff q₁ q₂) (overlap x u)) / (N : ℝ)) • u) x := by
    apply hd.congr_fderiv
    ext v
    simp only [_root_.smul_apply, smul_eq_mul, InnerProductSpace.toDual_apply_apply,
      real_inner_smul_left, innerSL_apply_apply, div_eq_mul_inv]
    ring
  exact hg.gradient

lemma capTrial_surfaceGradient (hN : 1 ≤ N) (q₁ q₂ : ℝ) (u x : Vector N) :
    surfaceGradient (capTrial q₁ q₂ u) x =
      ((deriv (cutoff q₁ q₂) (overlap x u)) / (N : ℝ)) • tangentProjection x u := by
  rw [surfaceGradient, capTrial_gradient hN, map_smul]

/-- The genuine squared tangent gradient, localized to the literal collar. -/
theorem capTrial_gradient_sq_le (hN : 1 ≤ N) {q₁ q₂ : ℝ} (hq : q₁ < q₂)
    (u x : Vector N) (hu : OnSphere u) (hx : OnSphere x) :
    ‖surfaceGradient (capTrial q₁ q₂ u) x‖^2 ≤
      collarCoefficient N q₁ q₂ * (collar u q₁ q₂).indicator (fun _ => (1 : ℝ)) x := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  rw [capTrial_surfaceGradient hN]
  by_cases hxc : x ∈ collar u q₁ q₂
  · rw [indicator_of_mem hxc]
    have hp : ‖tangentProjection x u‖ ≤ ‖u‖ :=
      ((tangentProjection x).le_opNorm u).trans (by
        simpa using mul_le_mul_of_nonneg_right (tangentProjection_norm_le (by omega) x hx) (norm_nonneg u))
    have hd := cutoff_abs_deriv hq (overlap x u)
    rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hNp, mul_pow]
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp
    rw [(onSphere_iff_norm_sq u).mp hu] at hs
    have hs' := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 / (q₂-q₁))).mpr hd
    have hprod := mul_le_mul hs' hs (sq_nonneg _) (by positivity : 0 ≤ (2 / (q₂-q₁))^2)
    rw [div_pow]
    have hdiv := div_le_div_of_nonneg_right hprod (sq_nonneg (N : ℝ))
    convert hdiv using 1 <;> try simp only [collarCoefficient, mul_one]
    all_goals
      field_simp [hNp.ne', (sub_pos.mpr hq).ne'] <;> ring
  · have hnot : overlap x u < q₁ ∨ q₂ < overlap x u := by
      have hc : ¬(q₁ ≤ overlap x u ∧ overlap x u ≤ q₂) := by
        intro hc
        apply hxc
        simp only [SphericalModel.collar, mem_ofPred_eq]
        exact hc
      exact not_and_or.mp hc |>.imp lt_of_not_ge lt_of_not_ge
    have hz : deriv (cutoff q₁ q₂) (overlap x u) = 0 := hnot.elim
      (cutoff_deriv_zero_left hq) (cutoff_deriv_zero_right hq)
    simp [hz, indicator_of_notMem hxc]

/-- Actual cap cutoff row mass is bounded by the outer cap mass. -/
theorem capTrial_row_le (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H)
    {q₁ q₂ : ℝ} (hq : q₁ < q₂) (u : Vector N) :
    (∫ x, capTrial q₁ q₂ u x ∂gibbsLaw N β H) ≤ (gibbsLaw N β H).real (cap u q₁) := by
  let _ := gibbsLaw_probability hN β hH
  have hf := integrable_gibbs_of_continuous hN β hH (capTrial_contDiff q₁ q₂ u).continuous
  have hi : Integrable ((cap u q₁).indicator (fun _ => (1 : ℝ))) (gibbsLaw N β H) :=
    (integrable_const _).indicator (cap_measurable u q₁)
  have hm := integral_mono_ae hf hi (ae_of_all _ (fun x => by
    by_cases hx : x ∈ cap u q₁
    · rw [indicator_of_mem hx]
      exact cutoff_le_one q₁ q₂ (overlap x u)
    · have hr : overlap x u ≤ q₁ := le_of_lt (lt_of_not_ge hx)
      simp only [capTrial, cutoff_zero hq hr, indicator_of_notMem hx, le_refl]))
  rw [integral_indicator_const _ (cap_measurable u q₁)] at hm
  simpa only [smul_eq_mul, mul_one] using hm

/-- Actual squared cutoff mass captures the entire inner cap. -/
theorem capTrial_square_mass_lower (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {q₁ q₂ : ℝ} (hq : q₁ < q₂) (u : Vector N) :
    (gibbsLaw N β H).real (cap u q₂) ≤ ∫ x, (capTrial q₁ q₂ u x)^2 ∂gibbsLaw N β H := by
  let _ := gibbsLaw_probability hN β hH
  have hc : Continuous (fun x => (capTrial q₁ q₂ u x)^2) := by
    have hh := (capTrial_contDiff q₁ q₂ u).continuous
    fun_prop
  have hf : Integrable (fun x => (capTrial q₁ q₂ u x)^2) (gibbsLaw N β H) :=
    integrable_gibbs_of_continuous hN β hH hc
  have hi : Integrable ((cap u q₂).indicator (fun _ => (1 : ℝ))) (gibbsLaw N β H) :=
    (integrable_const _).indicator (cap_measurable u q₂)
  have hm := integral_mono_ae hi hf (ae_of_all _ (fun x => by
    by_cases hx : x ∈ cap u q₂
    · simp only [indicator_of_mem hx, capTrial, cutoff_one hq hx, one_pow, le_refl]
    · simpa only [indicator_of_notMem hx] using sq_nonneg (capTrial q₁ q₂ u x)))
  rw [integral_indicator_const _ (cap_measurable u q₂)] at hm
  simpa only [smul_eq_mul, mul_one] using hm

/-- The source localized energy inequality uses the true Gibbs form and
the literal collar mass, with its exact numerical prefactor. -/
theorem capTrial_energy_le_collar (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {q₁ q₂ : ℝ} (hq : q₁ < q₂)
    (u : Vector N) (hu : OnSphere u) :
    dirichletEnergy N β H (capTrial q₁ q₂ u) ≤
      collarCoefficient N q₁ q₂ * (gibbsLaw N β H).real (collar u q₁ q₂) := by
  let _ := gibbsLaw_probability hN β hH
  rw [dirichletEnergy_eq_integral_norm_sq]
  have hf := integrable_gibbs_of_continuous hN β hH
    ((surfaceGradient_continuous ((capTrial_contDiff q₁ q₂ u).of_le (by simp))).norm.pow 2)
  have hi : Integrable ((collar u q₁ q₂).indicator (fun _ => collarCoefficient N q₁ q₂))
      (gibbsLaw N β H) := (integrable_const _).indicator (collar_measurable u q₁ q₂)
  have hm := integral_mono_ae hf hi (by
    filter_upwards [gibbsLaw_support hN β H] with x hx
    have he := capTrial_gradient_sq_le hN hq u x hu ((onSphere_iff_norm_sq x).mpr hx)
    by_cases hc : x ∈ collar u q₁ q₂ <;> simpa [hc] using he)
  rw [integral_indicator_const _ (collar_measurable u q₁ q₂), smul_eq_mul] at hm
  simpa only [mul_comm, Pi.pow_apply] using hm

end SlowEquilibration.SphericalCapCutoff
