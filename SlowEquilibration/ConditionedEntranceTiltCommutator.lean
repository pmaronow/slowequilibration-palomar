module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

@[expose] public section

/-!
# The exact weak commutator under a genuine exponential tilt

The measure in this file is the literal normalized `withDensity` measure,
not a substitute expectation functional. The weak integration-by-parts
identity is used only under the reference measure. The perturbation `w`
needs no derivative. This proves `eq:ent-commutator` at the level of its
actual integrals and supplies its cancellation for the entropy-resolvent
comparison.
-/

namespace SlowEquilibration.ConditionedEntrance
noncomputable section
open MeasureTheory

variable {E : Type*} [MeasurableSpace E]

/-- A genuine exponentially tilted measure with prescribed normalization. -/
def normalizedTilt (μ : Measure E) (w : E → ℝ) (M : ℝ) : Measure E :=
  μ.withDensity (fun x => ENNReal.ofReal (Real.exp (w x) / M))

/-- The literal multiplier `k=1-exp(-w)` in the source commutator. -/
def tiltDefect (w : E → ℝ) (x : E) : ℝ := 1 - Real.exp (-w x)

omit [MeasurableSpace E] in
lemma exp_mul_one_sub_tiltDefect (w : E → ℝ) (x : E) :
    Real.exp (w x) * (1 - tiltDefect w x) = 1 := by
  simp only [tiltDefect, sub_sub_cancel, ← Real.exp_add, add_neg_cancel, Real.exp_zero]

omit [MeasurableSpace E] in
lemma exp_mul_tiltDefect (w : E → ℝ) (x : E) :
    Real.exp (w x) * tiltDefect w x = Real.exp (w x) - 1 := by
  have he := exp_mul_one_sub_tiltDefect w x
  nlinarith

/-- Change of measure for every real function, with no hidden integrability
premise because both sides use the ordinary totalized Bochner integral. -/
theorem integral_normalizedTilt (μ : Measure E) (w : E → ℝ)
    (hw : Measurable w) {M : ℝ} (hM : 0 < M) (f : E → ℝ) :
    (∫ x, f x ∂normalizedTilt μ w M) =
      (∫ x, Real.exp (w x) * f x ∂μ) / M := by
  rw [normalizedTilt, integral_withDensity_eq_integral_toReal_smul
    (hw.exp.div_const M).ennreal_ofReal (Filter.Eventually.of_forall
      fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ Real.exp (w _) / M by positivity), smul_eq_mul]
  have he : (fun x => Real.exp (w x) / M * f x) =
      fun x => (Real.exp (w x) * f x) / M := by funext x; ring
  rw [he, integral_div]

/-- Cancellation of the factor `1-k` is proved against the actual tilted
measure, including the exact factor `M⁻¹`. -/
theorem integral_one_sub_tiltDefect (μ : Measure E) (w : E → ℝ)
    (hw : Measurable w) {M : ℝ} (hM : 0 < M) (f : E → ℝ) :
    (∫ x, (1 - tiltDefect w x) * f x ∂normalizedTilt μ w M) =
      (∫ x, f x ∂μ) / M := by
  rw [integral_normalizedTilt μ w hw hM]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change Real.exp (w x) * ((1 - tiltDefect w x) * f x) = f x
    rw [← mul_assoc, exp_mul_one_sub_tiltDefect, one_mul]

/-- The genuine weak commutator. Here `Γ` is the actual gradient pairing
and `G` the actual `(A₀g)v`; the only identity supplied is reference-measure
integration by parts. In particular no integration by parts is assumed
under the perturbed measure and no regularity of the density is used. -/
theorem exponential_tilt_weak_commutator (μ : Measure E) (w : E → ℝ)
    (hw : Measurable w) {M : ℝ} (hM : 0 < M) (Γ G : E → ℝ)
    (hΓ : Integrable Γ μ)
    (heΓ : Integrable (fun x => Real.exp (w x) * Γ x) μ)
    (hIBP : (∫ x, G x ∂μ) = ∫ x, Γ x ∂μ) :
    (∫ x, Γ x ∂normalizedTilt μ w M) =
      (∫ x, (1 - tiltDefect w x) * G x ∂normalizedTilt μ w M) +
      ∫ x, tiltDefect w x * Γ x ∂normalizedTilt μ w M := by
  rw [integral_one_sub_tiltDefect μ w hw hM, hIBP,
    integral_normalizedTilt μ w hw hM,
    integral_normalizedTilt μ w hw hM]
  have he : (fun x => Real.exp (w x) * (tiltDefect w x * Γ x)) =
      fun x => Real.exp (w x) * Γ x - Γ x := by
    funext x
    rw [← mul_assoc, exp_mul_tiltDefect]
    ring
  rw [he, integral_sub heΓ hΓ]
  ring

/-- If `M` is the actual finite exponential mass, the tilted measure is an
actual probability measure. Normalization is a conclusion. -/
theorem normalizedTilt_probability (μ : Measure E) (w : E → ℝ)
    {M : ℝ} (hM : 0 < M) (he : Integrable (fun x => Real.exp (w x)) μ)
    (hMass : (∫ x, Real.exp (w x) ∂μ) = M) :
    IsProbabilityMeasure (normalizedTilt μ w M) := by
  constructor
  rw [normalizedTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (he.div_const M)
      (Filter.Eventually.of_forall fun x => by positivity), integral_div, hMass,
    div_self hM.ne']
  norm_num

variable {U : Type*} [MeasurableSpace U]

/-- Genuine axis integration, valid on arbitrary sigma-finite product
spaces. The function `Γ` is frozen in the label, as in (D4). -/
theorem weighted_frozen_axis_integral_bound (θ : Measure U) (μ : Measure E)
    [SFinite θ] [SFinite μ] (a : U × E → ℝ) (Γ : E → ℝ) {K : ℝ}
    (hΓ : Integrable Γ μ) (hΓpos : ∀ᵐ x ∂μ, 0 ≤ Γ x)
    (haΓ : Integrable (fun p => a p * Γ p.2) (θ.prod μ))
    (haxis : ∀ᵐ x ∂μ, (∫ u, a (u, x) ∂θ) ≤ K) :
    (∫ p, a p * Γ p.2 ∂θ.prod μ) ≤ K * ∫ x, Γ x ∂μ := by
  have hi := haΓ.integral_prod_right
  have he : (fun x => ∫ u, a (u, x) * Γ x ∂θ) =
      fun x => (∫ u, a (u, x) ∂θ) * Γ x := by
    funext x
    exact integral_mul_const _ _
  rw [integral_prod_symm _ haΓ, he]
  have hm : (∫ x, (∫ u, a (u, x) ∂θ) * Γ x ∂μ) ≤
      ∫ x, K * Γ x ∂μ := by
    apply integral_mono_ae (he ▸ hi) (hΓ.const_mul K)
    filter_upwards [hΓpos, haxis] with x hx ha
    exact mul_le_mul_of_nonneg_right ha hx
  exact hm.trans_eq (integral_const_mul _ _)

/-- The actual normalization is close to one as a consequence of the
source first axis moment. Neither a normalization bound nor a Gibbs mass
estimate is supplied as a hypothesis. -/
theorem exponential_mass_close_one (θ : Measure U) (μ : Measure E)
    [IsProbabilityMeasure θ] [IsProbabilityMeasure μ] (w : U × E → ℝ)
    (he : Integrable (fun p => Real.exp (w p)) (θ.prod μ)) {η M : ℝ}
    (hMass : (∫ p, Real.exp (w p) ∂θ.prod μ) = M)
    (haxis : ∀ᵐ x ∂μ, (∫ u, |Real.exp (w (u, x)) - 1| ∂θ) ≤ η) :
    |M - 1| ≤ η := by
  have hd := he.sub (integrable_const (μ := θ.prod μ) (1 : ℝ))
  have hdi := hd.abs
  have hprod := integral_prod_symm (fun p => |Real.exp (w p) - 1|) hdi
  have hbound : (∫ p, |Real.exp (w p) - 1| ∂θ.prod μ) ≤ η := by
    rw [hprod]
    have hh := integral_mono_ae hdi.integral_prod_right
      (integrable_const (μ := μ) η) haxis
    simpa [Pi.sub_apply] using hh
  have habs := abs_integral_le_integral_abs
    (μ := θ.prod μ) (f := fun p => Real.exp (w p) - 1)
  have hsub := integral_sub he (integrable_const (μ := θ.prod μ) (1 : ℝ))
  change (∫ p, Real.exp (w p) - 1 ∂θ.prod μ) =
    (∫ p, Real.exp (w p) ∂θ.prod μ) - (∫ _ : U × E, (1 : ℝ) ∂θ.prod μ) at hsub
  rw [hsub, hMass] at habs
  simpa using habs.trans hbound

/-- The source first moment also controls the plain exponential axis mean.
This discharges the first-moment premise of the frozen projection above. -/
theorem axis_exponential_mean_le (θ : Measure U) (μ : Measure E)
    [IsProbabilityMeasure θ] [IsProbabilityMeasure μ] (w : U × E → ℝ)
    (he : Integrable (fun p => Real.exp (w p)) (θ.prod μ)) {η : ℝ}
    (haxis : ∀ᵐ x ∂μ, (∫ u, |Real.exp (w (u, x)) - 1| ∂θ) ≤ η) :
    ∀ᵐ x ∂μ, (∫ u, Real.exp (w (u, x)) ∂θ) ≤ 1 + η := by
  filter_upwards [he.prod_left_ae, haxis] with x hx hax
  have ha := abs_integral_le_integral_abs
    (μ := θ) (f := fun u => Real.exp (w (u, x)) - 1)
  rw [integral_sub hx (integrable_const (μ := θ) (1 : ℝ))] at ha
  simp only [integral_const, probReal_univ, one_smul] at ha
  have hb := (le_abs_self ((∫ u, Real.exp (w (u, x)) ∂θ) - 1)).trans (ha.trans hax)
  linarith

/-- Exact squared-defect projection `eq:ent-k-square`, including the
normalization constant `2`. The hypotheses are the source axis moment,
not the asserted weighted bound. -/
theorem tiltDefect_square_projection (θ : Measure U) (μ : Measure E)
    [SFinite θ] [SFinite μ] (w : U × E → ℝ) (hw : Measurable w)
    {M ε : ℝ} (hM : (1 / 2 : ℝ) ≤ M) (hε : 0 ≤ ε)
    (Γ : E → ℝ) (hΓ : Integrable Γ μ) (hΓpos : ∀ᵐ x ∂μ, 0 ≤ Γ x)
    (haΓ : Integrable (fun p => Real.exp (w p) * (tiltDefect w p) ^ 2 * Γ p.2)
      (θ.prod μ))
    (haxis : ∀ᵐ x ∂μ,
      (∫ u, Real.exp (w (u, x)) * (tiltDefect w (u, x)) ^ 2 ∂θ) ≤ ε) :
    (∫ p, (tiltDefect w p) ^ 2 * Γ p.2 ∂normalizedTilt (θ.prod μ) w M) ≤
      2 * ε * ∫ x, Γ x ∂μ := by
  have hMp : 0 < M := by linarith
  rw [integral_normalizedTilt _ _ hw hMp]
  have hb := weighted_frozen_axis_integral_bound θ μ
    (fun p => Real.exp (w p) * (tiltDefect w p) ^ 2) Γ hΓ hΓpos haΓ haxis
  have hb' : (∫ p, Real.exp (w p) * ((tiltDefect w p) ^ 2 * Γ p.2)
      ∂θ.prod μ) ≤ ε * ∫ x, Γ x ∂μ := by
    convert hb using 1
    simp only [mul_assoc]
  have hGi : 0 ≤ ∫ x, Γ x ∂μ := integral_nonneg_of_ae hΓpos
  apply (div_le_iff₀ hMp).2
  have hc : ε * (∫ x, Γ x ∂μ) ≤ (2 * ε * ∫ x, Γ x ∂μ) * M := by
    have hh := mul_le_mul_of_nonneg_left hM
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε) hGi)
    nlinarith
  exact hb'.trans hc

/-- The complementary frozen-axis projection, including the source
constant `3` and its uniform dependence on the first moment. -/
theorem exponential_tilt_frozen_projection (θ : Measure U) (μ : Measure E)
    [SFinite θ] [SFinite μ] (w : U × E → ℝ) (hw : Measurable w)
    {M η : ℝ} (_hη : 0 ≤ η) (hηhalf : η ≤ 1 / 2) (hM : 1 - η ≤ M)
    (Γ : E → ℝ) (hΓ : Integrable Γ μ) (hΓpos : ∀ᵐ x ∂μ, 0 ≤ Γ x)
    (heΓ : Integrable (fun p => Real.exp (w p) * Γ p.2) (θ.prod μ))
    (haxis : ∀ᵐ x ∂μ, (∫ u, Real.exp (w (u, x)) ∂θ) ≤ 1 + η) :
    (∫ p, Γ p.2 ∂normalizedTilt (θ.prod μ) w M) ≤
      3 * ∫ x, Γ x ∂μ := by
  have hMp : 0 < M := by linarith
  rw [integral_normalizedTilt _ _ hw hMp]
  have hb := weighted_frozen_axis_integral_bound θ μ
    (fun p => Real.exp (w p)) Γ hΓ hΓpos heΓ haxis
  have hGi : 0 ≤ ∫ x, Γ x ∂μ := integral_nonneg_of_ae hΓpos
  apply (div_le_iff₀ hMp).2
  have hc : (1 + η) * (∫ x, Γ x ∂μ) ≤ (3 * ∫ x, Γ x ∂μ) * M := by
    have hh := mul_le_mul_of_nonneg_left hM (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) hGi)
    have hh2 := mul_le_mul_of_nonneg_right hηhalf hGi
    nlinarith
  exact hb.trans hc

end
end SlowEquilibration.ConditionedEntrance
