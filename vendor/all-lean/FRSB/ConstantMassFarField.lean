module
public import FRSB.ConstantMassParity
public import Paper.HeatGrowth

@[expose] public section

/-! Far-field limits and the exact magnetization range of the actual Parisi solution. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper
open scoped Topology
namespace FRSB

lemma norm_heatLogCosh_sub_le (ell x : ℝ) :
    ‖heatSemigroup ell (fun y => Real.log (Real.cosh y)) x - Real.log (Real.cosh x)‖ ≤
      Real.sqrt ell * gaussianAbsMoment := by
  have hi := integrable_gaussian_logcosh_affine x (Real.sqrt ell)
  have hc : (∫ z : ℝ, Real.log (Real.cosh x) ∂gaussianReal 0 1) = Real.log (Real.cosh x) := by simp
  unfold heatSemigroup gaussianExpectation
  rw [← hc, ← integral_sub hi (integrable_const _)]
  calc
    _ ≤ ∫ z, ‖Real.log (Real.cosh (x + Real.sqrt ell * z)) - Real.log (Real.cosh x)‖ ∂gaussianReal 0 1 :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, Real.sqrt ell * ‖z‖ ∂gaussianReal 0 1 := integral_mono
      (hi.sub (integrable_const _)).norm (integrable_standardGaussian_id.norm.const_mul (Real.sqrt ell)) (fun z => by
        have hh := lipschitzWith_logcosh.dist_le_mul (x + Real.sqrt ell * z) x
        simpa only [dist_eq_norm, NNReal.coe_one, one_mul, add_sub_cancel_left,
          norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg ell)] using hh)
    _ = _ := integral_const_mul _ _

/-- The difference from log cosh is bounded uniformly in the field. -/
theorem parisiPotential_logCosh_distance_bound (β : ℝ) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖parisiPotential β μ (t, x) - Real.log (Real.cosh x)‖ ≤
      β ^ 2 / 2 + |β| * gaussianAbsMoment := by
  rw [parisiPotential_eq_duhamel β μ t x ht.2]
  unfold parisiDuhamelPotential
  have hh := norm_heatLogCosh_sub_le (β ^ 2 * (1 - t)) x
  have hc := norm_parisiDuhamelCorrection_le β μ (parisiGradient β μ) 1 (norm_parisiGradient_le_one β μ) 1 t x ht.2
  have hsqrt : Real.sqrt (β ^ 2 * (1 - t)) ≤ |β| := by
    have hh' := Real.sqrt_le_sqrt (show β ^ 2 * (1 - t) ≤ β ^ 2 by nlinarith [sq_nonneg β, ht.1])
    simpa only [Real.sqrt_sq_eq_abs] using hh'
  have hgauss := gaussianAbsMoment_nonneg
  calc
    _ ≤ ‖heatSemigroup (β ^ 2 * (1 - t)) (fun y => Real.log (Real.cosh y)) x - Real.log (Real.cosh x)‖ +
        ‖parisiDuhamelCorrection β μ (parisiGradient β μ) 1 t x‖ := by
      convert norm_add_le (heatSemigroup (β ^ 2 * (1 - t)) (fun y => Real.log (Real.cosh y)) x - Real.log (Real.cosh x))
        (parisiDuhamelCorrection β μ (parisiGradient β μ) 1 t x) using 1 <;> congr 1 <;> ring
    _ ≤ Real.sqrt (β ^ 2 * (1 - t)) * gaussianAbsMoment + β ^ 2 / 2 * (1 - t) * 1 ^ 2 := add_le_add hh hc
    _ ≤ _ := by
      have hh' := mul_le_mul_of_nonneg_right hsqrt hgauss
      nlinarith [sq_nonneg β, ht.1]

lemma logCosh_ge_linear (x : ℝ) : x - Real.log 2 ≤ Real.log (Real.cosh x) := by
  have hc : Real.exp x ≤ 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-x)]
  have hp : 0 < 2 * Real.cosh x := by positivity
  have hh := (Real.le_log_iff_exp_le hp).mpr hc
  rw [Real.log_mul (by norm_num) (Real.cosh_pos x).ne'] at hh
  linarith

theorem parisiGradient_strictMono (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    StrictMono (fun x => parisiGradient β μ (t, x)) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(hasDerivAt_parisiGradient_spatial_all β μ t x).deriv]
  exact parisiHessian_pos β hβ μ t x ht

lemma parisiGradient_secant_bound (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) {x : ℝ} (hx : 0 ≤ x) :
    parisiPotential β μ (t, x) - parisiPotential β μ (t, 0) ≤ x * parisiGradient β μ (t, x) := by
  have hmono := (parisiGradient_strictMono β hβ μ t ht).monotone
  have hi := ((continuous_parisiGradient β μ).comp (by fun_prop : Continuous (fun y : ℝ => (t, y)))).intervalIntegrable (μ := volume) (a := (0 : ℝ)) (b := x)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hasDerivAt_parisiPotential_spatial_all β μ t y ht) hi
  rw [← hFTC]
  have hh := intervalIntegral.integral_mono_on hx hi (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => parisiGradient β μ (t, x)) volume 0 x)
    (fun y hy => hmono hy.2)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, Function.comp_def] using hh

/-- The actual magnetization reaches the limiting values required for
its inverse coordinate, for every probability measure. -/
theorem tendsto_parisiGradient_atTop (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun x => parisiGradient β μ (t, x)) atTop (𝓝 1) := by
  let C := β ^ 2 / 2 + |β| * gaussianAbsMoment
  let D := C + |Real.log 2| + |parisiPotential β μ (t, 0)|
  have hD : 0 ≤ D := by dsimp only [D, C]; have hh := gaussianAbsMoment_nonneg; positivity
  have hbound : ∀ x : ℝ, 0 < x → ‖parisiGradient β μ (t, x) - 1‖ ≤ D / x := by
    intro x hx
    have hu := parisiPotential_logCosh_distance_bound β μ t x ht
    rw [Real.norm_eq_abs] at hu
    have hu' := (abs_le.mp hu).1
    have hl := logCosh_ge_linear x
    have hs := parisiGradient_secant_bound β hβ μ t ht hx.le
    have hG := norm_parisiGradient_le_one β μ (t, x)
    rw [Real.norm_eq_abs] at hG
    have hG1 := (abs_le.mp hG).2
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    apply (le_div_iff₀ hx).mpr
    dsimp only [D, C]
    linarith [le_abs_self (Real.log 2), le_abs_self (parisiPotential β μ (t, 0))]
  have hlim : Tendsto (fun x : ℝ => D / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => D) atTop (𝓝 D)).mul
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero' (.of_forall fun x => norm_nonneg _) (by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact hbound x hx) hlim

theorem tendsto_parisiGradient_atBot (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun x => parisiGradient β μ (t, x)) atBot (𝓝 (-1)) := by
  have hh := (tendsto_parisiGradient_atTop β hβ μ t ht).comp tendsto_neg_atBot_atTop
  have hn := hh.neg
  simpa only [Function.comp_def, parisiGradient_odd β hβ μ t _ ht, neg_neg] using hn

/-- The spatial gradient stays strictly inside its limiting endpoints. -/
theorem parisiGradient_mem_Ioo (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : parisiGradient β μ (t, x) ∈ Ioo (-1 : ℝ) 1 := by
  have hm := parisiGradient_strictMono β hβ μ t ht
  have hlow := norm_parisiGradient_le_one β μ (t, x - 1)
  have hup := norm_parisiGradient_le_one β μ (t, x + 1)
  rw [Real.norm_eq_abs] at hlow hup
  constructor
  · have hh := hm (show x - 1 < x by linarith)
    linarith [(abs_le.mp hlow).1]
  · have hh := hm (show x < x + 1 by linarith)
    linarith [(abs_le.mp hup).2]

/-- The magnetization coordinate has exactly the range (-1,1). -/
theorem parisiGradient_range (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    range (fun x => parisiGradient β μ (t, x)) = Ioo (-1 : ℝ) 1 := by
  apply subset_antisymm
  · rintro z ⟨x, rfl⟩
    exact parisiGradient_mem_Ioo β hβ μ t x ht
  · have hh := isPreconnected_univ.intermediate_value_Ioo
      (show (atBot : Filter ℝ) ≤ 𝓟 (univ : Set ℝ) by simp)
      (show (atTop : Filter ℝ) ≤ 𝓟 (univ : Set ℝ) by simp)
      (((continuous_parisiGradient β μ).comp (by fun_prop : Continuous (fun x : ℝ => (t, x)))).continuousOn)
      (tendsto_parisiGradient_atBot β hβ μ t ht) (tendsto_parisiGradient_atTop β hβ μ t ht)
    simpa only [image_univ, Function.comp_def] using hh

end FRSB
