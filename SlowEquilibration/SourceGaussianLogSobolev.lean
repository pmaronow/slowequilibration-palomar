-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceSphereLogSobolevProof
public import SlowEquilibration.SourceEntranceHarmonicSectors
public import SlowEquilibration.SourceEntranceFullEvent
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Rademacher

/-! Further analytic reduction of Gross's Gaussian logarithmic Sobolev
inequality. The averaging operator below is the actual finite-dimensional
Mehler integral, applied to the positive density `exp f`. We prove its
initial value, entropy continuity and relaxation, gradient commutation for
bounded globally Lipschitz functions, Gaussian invariance, and sharp
integrated Fisher decay. Thus the exact Gross interface, and its sphere and
latitude consequences, reduce to de Bruijn's identity alone. That identity
remains an explicit premise: this file does not prove Gross's inequality
unconditionally. The constants and the integrated derivative energy are
exactly those of `SourceSphereLogSobolevProof`.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceGaussianLogSobolev

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceSphereSharpConcentration SourceSphereLogSobolevProof
open scoped Topology RealInnerProductSpace NNReal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The density evolved by the standard Gaussian Ornstein--Uhlenbeck flow. -/
def mehlerExponential {n : ℕ} (f : Vector n → ℝ) (t : ℝ) (x : Vector n) : ℝ :=
  ∫ y, Real.exp (f (Real.exp (-t) • x +
    Real.sqrt (1 - Real.exp (-t) ^ 2) • y)) ∂stdGaussian (Vector n)

/-- Entropy of the actual Mehler density, with its actual integral as mass. -/
def mehlerEntropy {n : ℕ} (f : Vector n → ℝ) (t : ℝ) : ℝ :=
  (∫ x, mehlerExponential f t x * Real.log (mehlerExponential f t x)
    ∂stdGaussian (Vector n)) -
  (∫ x, mehlerExponential f t x ∂stdGaussian (Vector n)) *
    Real.log (∫ x, mehlerExponential f t x ∂stdGaussian (Vector n))

/-- Fisher information of the positive Mehler density. -/
def mehlerFisher {n : ℕ} (f : Vector n → ℝ) (t : ℝ) : ℝ :=
  ∫ x, ‖fderiv ℝ (mehlerExponential f t) x‖ ^ 2 / mehlerExponential f t x
    ∂stdGaussian (Vector n)

private theorem bounded_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → E} (hm : AEStronglyMeasurable f μ) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B) : Integrable f μ :=
  Integrable.of_bound hm B (Eventually.of_forall hb)

private theorem exp_comp_integrable {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B)
    (a b : ℝ) (x : Vector n) :
    Integrable (fun y => Real.exp (f (a • x + b • y))) (stdGaussian (Vector n)) := by
  apply bounded_integrable (by fun_prop) (B := Real.exp B)
  intro y
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb _))

private theorem mehler_bounds {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (t : ℝ) (x : Vector n) :
    Real.exp (-B) ≤ mehlerExponential f t x ∧ mehlerExponential f t x ≤ Real.exp B := by
  have hi := exp_comp_integrable hf hb (Real.exp (-t))
    (Real.sqrt (1 - Real.exp (-t) ^ 2)) x
  constructor
  · simpa only [mehlerExponential, integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono (integrable_const (Real.exp (-B))) hi
        (fun y => Real.exp_le_exp.mpr (abs_le.mp (hb _)).1)
  · simpa only [mehlerExponential, integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono hi (integrable_const (Real.exp B))
        (fun y => Real.exp_le_exp.mpr (abs_le.mp (hb _)).2)

private theorem mehler_continuous {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) :
    Continuous (fun p : ℝ × Vector n => mehlerExponential f p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp B)
  · exact Eventually.of_forall fun q => (exp_comp_integrable hf hb _ _ q.2).aestronglyMeasurable
  · apply Eventually.of_forall
    intro q
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb _))
  · exact integrable_const _
  · apply Eventually.of_forall
    intro y
    have hc : Continuous (fun q : ℝ × Vector n =>
        Real.exp (f (Real.exp (-q.1) • q.2 +
          Real.sqrt (1 - Real.exp (-q.1) ^ 2) • y))) := by fun_prop
    exact hc.continuousAt

private theorem mehler_pos {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (t : ℝ) (x : Vector n) :
    0 < mehlerExponential f t x :=
  (Real.exp_pos (-B)).trans_le (mehler_bounds hf hb t x).1

private theorem mehler_log_bound {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (t : ℝ) (x : Vector n) :
    |Real.log (mehlerExponential f t x)| ≤ B := by
  have hp := mehler_pos hf hb t x
  obtain ⟨hl, hu⟩ := mehler_bounds hf hb t x
  apply abs_le.mpr
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hl
  · simpa only [Real.log_exp] using Real.log_le_log hp hu

private theorem mehler_integrable {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (t : ℝ) :
    Integrable (mehlerExponential f t) (stdGaussian (Vector n)) := by
  apply bounded_integrable (B := Real.exp B)
    (((mehler_continuous hf hb).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  intro x
  change ‖mehlerExponential f t x‖ ≤ Real.exp B
  rw [Real.norm_eq_abs, abs_of_pos (mehler_pos hf hb t x)]
  exact (mehler_bounds hf hb t x).2

private theorem mehler_entropy_integrable {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (t : ℝ) :
    Integrable (fun x => mehlerExponential f t x * Real.log (mehlerExponential f t x))
      (stdGaussian (Vector n)) := by
  have hc : Continuous (mehlerExponential f t) :=
    (mehler_continuous hf hb).comp (continuous_const.prodMk continuous_id)
  apply bounded_integrable (hc.mul (hc.log (fun x => (mehler_pos hf hb t x).ne'))
    |>.aestronglyMeasurable) (B := Real.exp B * B)
  intro x
  change ‖mehlerExponential f t x * Real.log (mehlerExponential f t x)‖ ≤ Real.exp B * B
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mehler_pos hf hb t x)]
  exact mul_le_mul (mehler_bounds hf hb t x).2 (mehler_log_bound hf hb t x)
    (abs_nonneg _) (Real.exp_pos _).le

private theorem mehler_zero {n : ℕ} (f : Vector n → ℝ) (x : Vector n) :
    mehlerExponential f 0 x = Real.exp (f x) := by
  simp [mehlerExponential]

private theorem mehler_entropy_zero {n : ℕ} (f : Vector n → ℝ) :
    mehlerEntropy f 0 = gaussianEntropy f := by
  simp only [mehlerEntropy, mehler_zero, Real.log_exp, gaussianEntropy]

/-- Entropy is continuous all the way to the unsmoothed initial datum.
No differentiability of the bounded Lipschitz function is needed here. -/
theorem mehler_entropy_continuous {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    Continuous (mehlerEntropy f) := by
  obtain ⟨B, hB⟩ := hb
  have hc := mehler_continuous hf.continuous hB
  have hpos := mehler_pos hf.continuous hB
  have hmass : Continuous (fun t => ∫ x, mehlerExponential f t x
      ∂stdGaussian (Vector n)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp B)
    · exact Eventually.of_forall fun s => (mehler_integrable hf.continuous hB s).aestronglyMeasurable
    · exact Eventually.of_forall fun s => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (hpos s x)]
        exact (mehler_bounds hf.continuous hB s x).2
    · exact integrable_const _
    · exact Eventually.of_forall fun x =>
        (hc.comp (continuous_id.prodMk continuous_const)).continuousAt
  have hfirst : Continuous (fun t => ∫ x,
      mehlerExponential f t x * Real.log (mehlerExponential f t x)
      ∂stdGaussian (Vector n)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp B * B)
    · exact Eventually.of_forall fun s =>
        (mehler_entropy_integrable hf.continuous hB s).aestronglyMeasurable
    · exact Eventually.of_forall fun s => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hpos s x)]
        exact mul_le_mul (mehler_bounds hf.continuous hB s x).2
          (mehler_log_bound hf.continuous hB s x) (abs_nonneg _) (Real.exp_pos _).le
    · exact integrable_const _
    · apply Eventually.of_forall
      intro x
      have hx := hc.comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => x)))
      exact (hx.mul (hx.log (fun s => (hpos s x).ne'))).continuousAt
  have hmasspos (t : ℝ) : 0 < ∫ x, mehlerExponential f t x ∂stdGaussian (Vector n) := by
    have hh := integral_mono (integrable_const (Real.exp (-B)))
      (mehler_integrable hf.continuous hB t) (fun x => (mehler_bounds hf.continuous hB t x).1)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
    exact (Real.exp_pos (-B)).trans_le hh
  exact hfirst.sub (hmass.mul (hmass.log (fun t => (hmasspos t).ne')))

private theorem mehler_tendsto_mean {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (x : Vector n) :
    Tendsto (fun t => mehlerExponential f t x) atTop
      (𝓝 (∫ y, Real.exp (f y) ∂stdGaussian (Vector n))) := by
  have ha : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hb' : Tendsto (fun t : ℝ => Real.sqrt (1 - Real.exp (-t) ^ 2)) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
      (ha.pow 2)).sqrt
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp B)
  · exact Eventually.of_forall fun t => (exp_comp_integrable hf hb _ _ x).aestronglyMeasurable
  · exact Eventually.of_forall fun t => Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb _))
  · exact integrable_const _
  · apply Eventually.of_forall
    intro y
    have harg : Tendsto (fun t => Real.exp (-t) • x +
        Real.sqrt (1 - Real.exp (-t) ^ 2) • y) atTop (𝓝 y) := by
      simpa using (ha.smul_const x).add (hb'.smul_const y)
    exact (Real.continuous_exp.comp hf).continuousAt.tendsto.comp harg

/-- The actual Mehler entropy relaxes to zero. Both integrals in its
definition converge by domination; invariance is not assumed to get this limit. -/
theorem mehler_entropy_tendsto_zero {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    Tendsto (mehlerEntropy f) atTop (𝓝 0) := by
  obtain ⟨B, hB⟩ := hb
  let m := ∫ y, Real.exp (f y) ∂stdGaussian (Vector n)
  have hm : 0 < m := integral_exp_pos (by
    simpa using exp_comp_integrable hf.continuous hB 0 1 (0 : Vector n))
  have hlim := mehler_tendsto_mean hf.continuous hB
  have hmass : Tendsto (fun t => ∫ x, mehlerExponential f t x
      ∂stdGaussian (Vector n)) atTop (𝓝 m) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp B)
      (Eventually.of_forall fun t => (mehler_integrable hf.continuous hB t).aestronglyMeasurable)
      (Eventually.of_forall fun t => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (mehler_pos hf.continuous hB t x)]
        exact (mehler_bounds hf.continuous hB t x).2)
      (integrable_const _) (Eventually.of_forall hlim)
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  have hfirst : Tendsto (fun t => ∫ x, mehlerExponential f t x *
      Real.log (mehlerExponential f t x) ∂stdGaussian (Vector n)) atTop
      (𝓝 (m * Real.log m)) := by
    have hh := tendsto_integral_filter_of_dominated_convergence (fun _ => Real.exp B * B)
      (Eventually.of_forall fun t =>
        (mehler_entropy_integrable hf.continuous hB t).aestronglyMeasurable)
      (Eventually.of_forall fun t => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (mehler_pos hf.continuous hB t x)]
        exact mul_le_mul (mehler_bounds hf.continuous hB t x).2
          (mehler_log_bound hf.continuous hB t x) (abs_nonneg _) (Real.exp_pos _).le)
      (integrable_const _) (Eventually.of_forall fun x => (hlim x).mul ((hlim x).log hm.ne'))
    simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using hh
  change Tendsto (fun t => mehlerEntropy f t) atTop (𝓝 0)
  simpa only [mehlerEntropy, sub_self] using hfirst.sub (hmass.mul (hmass.log hm.ne'))

private theorem gaussian_mix_map {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((stdGaussian (Vector n)).prod (stdGaussian (Vector n))).map
      (fun p : Vector n × Vector n => a • p.1 + b • p.2) = stdGaussian (Vector n) := by
  let A : Vector n × Vector n →L[ℝ] Vector n :=
    a • ContinuousLinearMap.fst ℝ (Vector n) (Vector n) +
      b • ContinuousLinearMap.snd ℝ (Vector n) (Vector n)
  change ((stdGaussian (Vector n)).prod (stdGaussian (Vector n))).map A = _
  apply Measure.ext_of_charFunDual
  funext L
  have hleft : (L.comp A).comp (ContinuousLinearMap.inl ℝ (Vector n) (Vector n)) = a • L := by
    ext x
    simp [A]
  have hright : (L.comp A).comp (ContinuousLinearMap.inr ℝ (Vector n) (Vector n)) = b • L := by
    ext x
    simp [A]
  rw [charFunDual_map, charFunDual_prod, hleft, hright,
    charFunDual_stdGaussian, charFunDual_stdGaussian, charFunDual_stdGaussian,
    ← Complex.exp_add]
  congr 1
  simp only [norm_smul, Real.norm_eq_abs]
  have hh : -(a ^ 2 * ‖L‖ ^ 2) / 2 + -(b ^ 2 * ‖L‖ ^ 2) / 2 = -‖L‖ ^ 2 / 2 := by
    nlinarith only [congrArg (fun r : ℝ => r * ‖L‖ ^ 2) hab]
  norm_cast
  simpa only [mul_pow, sq_abs] using hh

private theorem integral_gaussian_mix {n : ℕ} (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1)
    {h : Vector n → ℝ} (hm : Measurable h) {C : ℝ} (hb : ∀ x, |h x| ≤ C) :
    (∫ x, ∫ y, h (a • x + b • y) ∂stdGaussian (Vector n)
      ∂stdGaussian (Vector n)) = ∫ x, h x ∂stdGaussian (Vector n) := by
  have hi : Integrable (fun p : Vector n × Vector n => h (a • p.1 + b • p.2))
      ((stdGaussian (Vector n)).prod (stdGaussian (Vector n))) := by
    apply bounded_integrable (hm.comp (by fun_prop)).aestronglyMeasurable
    intro p
    exact hb (a • p.1 + b • p.2)
  rw [← integral_prod _ hi]
  have hh := integral_map (μ := (stdGaussian (Vector n)).prod (stdGaussian (Vector n)))
    (by fun_prop : Measurable (fun p : Vector n × Vector n =>
      a • p.1 + b • p.2)).aemeasurable hm.aestronglyMeasurable
  rw [gaussian_mix_map a b hab] at hh
  exact hh.symm

private theorem mehler_coefficients {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) ^ 2 + Real.sqrt (1 - Real.exp (-t) ^ 2) ^ 2 = 1 := by
  have ha : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hasq : Real.exp (-t) ^ 2 ≤ 1 := by nlinarith [Real.exp_pos (-t)]
  rw [Real.sq_sqrt (by linarith : 0 ≤ 1 - Real.exp (-t) ^ 2)]
  ring

private theorem gaussian_absolutelyContinuous_volume (n : ℕ) :
    stdGaussian (Vector n) ≪ (volume : Measure (Vector n)) := by
  rw [GaussianDensity.stdGaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

private theorem exp_lipschitz_bound {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (x y : Vector n) :
    ‖Real.exp (f x) - Real.exp (f y)‖ ≤ Real.exp B * K * ‖x - y‖ := by
  have he : ‖Real.exp (f x) - Real.exp (f y)‖ ≤ Real.exp B * ‖f x - f y‖ := by
    apply Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z (_ : z ∈ Iic B) => Real.differentiableAt_exp)
      (fun z hz => ?_) (convex_Iic B)
      ((le_abs_self _).trans (hb y)) ((le_abs_self _).trans (hb x))
    rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hz
  exact he.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hf.norm_sub_le x y) (Real.exp_pos B).le)

/-- Gradient commutation for the actual Mehler integral, for the exact
bounded globally Lipschitz class in the target. Rademacher and differentiation
under the integral are sufficient; smooth approximation is unnecessary. -/
theorem mehler_fderiv_commutation {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 < t) (x : Vector n) :
    HasFDerivAt (mehlerExponential f t)
      (Real.exp (-t) • (∫ y, Real.exp (f (Real.exp (-t) • x +
        Real.sqrt (1 - Real.exp (-t) ^ 2) • y)) •
          fderiv ℝ f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)
        ∂stdGaussian (Vector n))) x := by
  obtain ⟨B, hB⟩ := hb
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - a ^ 2)
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by nlinarith)
  have hd : ∀ᵐ y ∂stdGaussian (Vector n), DifferentiableAt ℝ f (a • x + b • y) := by
    apply (gaussian_absolutelyContinuous_volume n).ae_le
    exact ((quasiMeasurePreserving_add_left (volume : Measure (Vector n)) (a • x)).comp
      (Measure.quasiMeasurePreserving_smul (volume : Measure (Vector n)) hbpos.ne')).ae
        hf.ae_differentiableAt
  let D : Vector n → Vector n →L[ℝ] ℝ :=
    fun y => a • (Real.exp (f (a • x + b • y)) • fderiv ℝ f (a • x + b • y))
  have hD : AEStronglyMeasurable D (stdGaussian (Vector n)) := by
    have hm : Measurable (fun y : Vector n => a • x + b • y) := by fun_prop
    apply Measurable.aestronglyMeasurable
    dsimp only [D]
    exact (measurable_const (a := a)).smul (((hf.continuous.measurable.comp hm).exp).smul
      ((measurable_fderiv ℝ f).comp hm))
  have hdiff : ∀ᵐ y ∂stdGaussian (Vector n),
      HasFDerivAt (fun z => Real.exp (f (a • z + b • y))) (D y) x := by
    filter_upwards [hd] with y hy
    have hinner : HasFDerivAt (fun z : Vector n => a • z + b • y)
        (a • ContinuousLinearMap.id ℝ (Vector n)) x :=
      ((hasFDerivAt_id x).const_smul a).add_const _
    have hh := (hy.hasFDerivAt.comp x hinner).exp
    convert! hh using 1
    ext v
    simp only [D, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_eq_mul, Function.comp_apply]
    ring
  have hbound (y z : Vector n) :
      ‖Real.exp (f (a • z + b • y)) - Real.exp (f (a • x + b • y))‖ ≤
        (Real.exp B * K * a) * ‖z - x‖ := by
    have hh := exp_lipschitz_bound hf hB (a • z + b • y) (a • x + b • y)
    simpa only [add_sub_add_right_eq_sub, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos ha, mul_assoc, mul_left_comm, mul_comm] using hh
  have hresult := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (s := univ) (bound := fun _ : Vector n => Real.exp B * K * a) (F' := D)
    (show univ ∈ 𝓝 x from univ_mem)
    (fun z _ => (exp_comp_integrable hf.continuous hB a b z).aestronglyMeasurable)
    (exp_comp_integrable hf.continuous hB a b x) hD
    (Eventually.of_forall fun y z _ => hbound y z) (integrable_const _) hdiff
  convert! hresult.2 using 1
  simp only [D, integral_smul, a, b]

private theorem weighted_norm_integral_sq_le {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {w : Ω → ℝ} {v : Ω → E} (hw : Measurable w) (hv : Measurable v)
    {W V : ℝ} (hwpos : ∀ x, 0 < w x) (hwB : ∀ x, w x ≤ W) (hvB : ∀ x, ‖v x‖ ≤ V) :
    ‖∫ x, w x • v x ∂μ‖ ^ 2 ≤
      (∫ x, w x ∂μ) * ∫ x, w x * ‖v x‖ ^ 2 ∂μ := by
  have hiw : Integrable w μ := bounded_integrable hw.aestronglyMeasurable
    (fun x => by simpa only [Real.norm_eq_abs, abs_of_pos (hwpos x)] using hwB x)
  have hiu : Integrable (fun x => w x * ‖v x‖) μ := by
    apply bounded_integrable (hw.mul hv.norm).aestronglyMeasurable (B := W * V)
    intro x
    change ‖w x * ‖v x‖‖ ≤ W * V
    rw [Real.norm_of_nonneg (mul_nonneg (hwpos x).le (norm_nonneg _))]
    exact mul_le_mul (hwB x) (hvB x) (norm_nonneg _) ((hwpos x).le.trans (hwB x))
  have hie : Integrable (fun x => w x * ‖v x‖ ^ 2) μ := by
    apply bounded_integrable (hw.mul (hv.norm.pow_const 2)).aestronglyMeasurable (B := W * V ^ 2)
    intro x
    change ‖w x * ‖v x‖ ^ 2‖ ≤ W * V ^ 2
    rw [Real.norm_of_nonneg (mul_nonneg (hwpos x).le (sq_nonneg _))]
    exact mul_le_mul (hwB x) (pow_le_pow_left₀ (norm_nonneg _) (hvB x) 2)
      (sq_nonneg _) ((hwpos x).le.trans (hwB x))
  let m := ∫ x, w x ∂μ
  let p := ∫ x, w x * ‖v x‖ ∂μ
  have hm : 0 < m := (integral_pos_iff_support_of_nonneg (fun x => (hwpos x).le) hiw).mpr (by
    simp [Function.support, (hwpos _).ne'])
  have hn : 0 ≤ ∫ x, w x * (‖v x‖ - p / m) ^ 2 ∂μ :=
    integral_nonneg fun x => mul_nonneg (hwpos x).le (sq_nonneg _)
  have heq : (∫ x, w x * (‖v x‖ - p / m) ^ 2 ∂μ) =
      (∫ x, w x * ‖v x‖ ^ 2 ∂μ) - 2 * (p / m) * p + (p / m) ^ 2 * m := by
    simp_rw [show ∀ x, w x * (‖v x‖ - p / m) ^ 2 =
      w x * ‖v x‖ ^ 2 - (2 * (p / m)) * (w x * ‖v x‖) + (p / m) ^ 2 * w x by
        intro x; ring]
    rw [integral_add (f := fun x => w x * ‖v x‖ ^ 2 - (2 * (p / m)) * (w x * ‖v x‖))
      (g := fun x => (p / m) ^ 2 * w x) (hie.sub (hiu.const_mul _)) (hiw.const_mul _),
      integral_sub (f := fun x => w x * ‖v x‖ ^ 2)
        (g := fun x => (2 * (p / m)) * (w x * ‖v x‖)) hie (hiu.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [heq] at hn
  have hcs : p ^ 2 ≤ m * ∫ x, w x * ‖v x‖ ^ 2 ∂μ := by
    have hm0 := hm.ne'
    have hh : (∫ x, w x * ‖v x‖ ^ 2 ∂μ) - 2 * (p / m) * p + (p / m) ^ 2 * m =
        ((∫ x, w x * ‖v x‖ ^ 2 ∂μ) * m - p ^ 2) / m := by field_simp; ring
    rw [hh] at hn
    have hh' := (le_div_iff₀ hm).mp hn
    nlinarith only [hh']
  have hnorm : ‖∫ x, w x • v x ∂μ‖ ≤ p := by
    have hh := norm_integral_le_integral_norm (fun x => w x • v x) (μ := μ)
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (hwpos _)] using hh
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs

private theorem energy_integrand_measurable {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) :
    Measurable (fun x => Real.exp (f x) * ‖fderiv ℝ f x‖ ^ 2) :=
  hf.measurable.exp.mul ((measurable_fderiv ℝ f).norm.pow_const 2)

private theorem energy_integrand_bound {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (x : Vector n) :
    |Real.exp (f x) * ‖fderiv ℝ f x‖ ^ 2| ≤ Real.exp B * (K : ℝ) ^ 2 := by
  rw [abs_of_nonneg (by positivity)]
  exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self _).trans (hb x)))
    (pow_le_pow_left₀ (norm_nonneg _) (norm_fderiv_le_of_lipschitz ℝ hf) 2)
    (sq_nonneg _) (Real.exp_pos _).le

private def mehlerEnergy {n : ℕ} (f : Vector n → ℝ) (t : ℝ) (x : Vector n) : ℝ :=
  ∫ y, Real.exp (f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)) *
    ‖fderiv ℝ f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)‖ ^ 2
    ∂stdGaussian (Vector n)

private theorem mehler_energy_bound {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (t : ℝ) (x : Vector n) :
    |mehlerEnergy f t x| ≤ Real.exp B * (K : ℝ) ^ 2 := by
  have hm : Measurable (fun y : Vector n =>
      Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y) := by fun_prop
  have hi := bounded_integrable (μ := stdGaussian (Vector n))
    ((energy_integrand_measurable hf.continuous).comp hm).aestronglyMeasurable
    (fun y => energy_integrand_bound hf hb (Real.exp (-t) • x +
      Real.sqrt (1 - Real.exp (-t) ^ 2) • y))
  apply abs_le.mpr
  constructor
  · have hn : 0 ≤ mehlerEnergy f t x := integral_nonneg fun y => by positivity
    have hconst : 0 ≤ Real.exp B * (K : ℝ) ^ 2 := by positivity
    linarith
  · simpa only [mehlerEnergy, Function.comp_def, integral_const, probReal_univ, smul_eq_mul, one_mul] using
      integral_mono hi (integrable_const (Real.exp B * (K : ℝ) ^ 2))
        (fun y => (le_abs_self _).trans (energy_integrand_bound hf hb _))

private theorem mehler_energy_integrable {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {B : ℝ} (hb : ∀ x, |f x| ≤ B) (t : ℝ) :
    Integrable (mehlerEnergy f t) (stdGaussian (Vector n)) := by
  have hm : Measurable (fun p : Vector n × Vector n =>
      Real.exp (f (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-t) ^ 2) • p.2)) *
        ‖fderiv ℝ f (Real.exp (-t) • p.1 +
          Real.sqrt (1 - Real.exp (-t) ^ 2) • p.2)‖ ^ 2) :=
    (energy_integrand_measurable hf.continuous).comp (by fun_prop)
  exact bounded_integrable hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    (fun x => mehler_energy_bound hf hb t x)

private theorem mehler_fisher_pointwise {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {B : ℝ} (hb : ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 < t) (x : Vector n) :
    ‖fderiv ℝ (mehlerExponential f t) x‖ ^ 2 / mehlerExponential f t x ≤
      Real.exp (-t) ^ 2 * mehlerEnergy f t x := by
  let z : Vector n → Vector n :=
    fun y => Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y
  have hz : Measurable z := by fun_prop
  have hcs : ‖∫ y, Real.exp (f (z y)) • fderiv ℝ f (z y)
      ∂stdGaussian (Vector n)‖ ^ 2 ≤ mehlerExponential f t x * mehlerEnergy f t x := by
    exact weighted_norm_integral_sq_le (μ := stdGaussian (Vector n))
      (w := fun y => Real.exp (f (z y))) (v := fun y => fderiv ℝ f (z y))
      (W := Real.exp B) (V := (K : ℝ))
      ((hf.continuous.measurable.comp hz).exp) ((measurable_fderiv ℝ f).comp hz)
      (fun y => Real.exp_pos (f (z y)))
      (fun y => Real.exp_le_exp.mpr ((le_abs_self _).trans (hb (z y))))
      (fun y => norm_fderiv_le_of_lipschitz ℝ hf (x₀ := z y))
  have hnorm : ‖fderiv ℝ (mehlerExponential f t) x‖ ^ 2 =
      Real.exp (-t) ^ 2 * ‖∫ y, Real.exp (f (z y)) • fderiv ℝ f (z y)
        ∂stdGaussian (Vector n)‖ ^ 2 := by
    rw [(mehler_fderiv_commutation hf ⟨B, hb⟩ ht x).fderiv, norm_smul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  rw [hnorm]
  apply (div_le_iff₀ (mehler_pos hf.continuous hb t x)).mpr
  calc
    _ ≤ Real.exp (-t) ^ 2 * (mehlerExponential f t x * mehlerEnergy f t x) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg (Real.exp (-t)))
    _ = _ := by ring

/-- The sharp integrated Fisher decay, proved from gradient commutation,
weighted Cauchy--Schwarz, and Gaussian invariance. The energy is exactly
the derivative energy in the target, rather than a uniform Lipschitz bound. -/
theorem mehler_fisher_decay {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 < t) :
    mehlerFisher f t ≤ Real.exp (-2 * t) * gaussianEnergy f := by
  obtain ⟨B, hB⟩ := hb
  have hden : Continuous (mehlerExponential f t) :=
    (mehler_continuous hf.continuous hB).comp (continuous_const.prodMk continuous_id)
  have hm : AEStronglyMeasurable (fun x =>
      ‖fderiv ℝ (mehlerExponential f t) x‖ ^ 2 / mehlerExponential f t x)
      (stdGaussian (Vector n)) :=
    (((measurable_fderiv ℝ (mehlerExponential f t)).norm.pow_const 2).div
      hden.measurable).aestronglyMeasurable
  have hiE := (mehler_energy_integrable hf hB t).const_mul (Real.exp (-t) ^ 2)
  have hiF : Integrable (fun x => ‖fderiv ℝ (mehlerExponential f t) x‖ ^ 2 /
      mehlerExponential f t x) (stdGaussian (Vector n)) := by
    apply hiE.mono' hm
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _)
      (mehler_pos hf.continuous hB t x).le)]
    exact mehler_fisher_pointwise hf hB ht x
  have he : (∫ x, mehlerEnergy f t x ∂stdGaussian (Vector n)) = gaussianEnergy f :=
    integral_gaussian_mix _ _ (mehler_coefficients ht.le)
      (energy_integrand_measurable hf.continuous) (energy_integrand_bound hf hB)
  have ha : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ ∫ x, Real.exp (-t) ^ 2 * mehlerEnergy f t x ∂stdGaussian (Vector n) :=
      integral_mono hiF hiE (mehler_fisher_pointwise hf hB ht)
    _ = _ := by rw [integral_const_mul, he, ha]

private theorem entropy_le_half_energy_of_dissipation {H I : ℝ → ℝ} {E : ℝ}
    (hc : Continuous H) (hd : ∀ t, 0 < t → HasDerivAt H (-I t) t)
    (hi : ∀ t, 0 < t → I t ≤ Real.exp (-2 * t) * E)
    (hl : Tendsto H atTop (𝓝 0)) : H 0 ≤ (1 / 2 : ℝ) * E := by
  let F : ℝ → ℝ := fun t => H t - (E / 2) * Real.exp (-2 * t)
  have hF (t : ℝ) (ht : 0 < t) :
      HasDerivAt F (-I t + E * Real.exp (-2 * t)) t := by
    convert! (hd t ht).sub ((((hasDerivAt_id t).const_mul (-2)).exp).const_mul (E / 2)) using 1
    simp only [id_eq]
    ring
  have hcont : Continuous F := hc.sub (by fun_prop)
  have hmono : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont.continuousOn
    · intro t ht
      exact (hF t (by simpa only [interior_Ici, mem_Ioi] using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      rw [(hF t ht').deriv]
      linarith [hi t ht']
  have he : Tendsto (fun t : ℝ => Real.exp (-2 * t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0))
  have hFlim : Tendsto F atTop (𝓝 0) := by
    simpa only [mul_zero, sub_zero] using hl.sub (he.const_mul (E / 2))
  have hzero : F 0 ≤ 0 := by
    apply ge_of_tendsto hFlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hmono (by simp) ht ht
  simp only [F, mul_zero, Real.exp_zero, mul_one] at hzero
  linarith

/-- The sole remaining analytic identity in this reduction: de Bruijn's
formula for the concrete Mehler entropy and Fisher information above.
Only positive times are included; initial continuity is already proved. -/
def MehlerEntropyDissipation : Prop :=
  ∀ (n : ℕ) (f : Vector n → ℝ) (K : ℝ≥0), LipschitzWith K f →
    (∃ B : ℝ, ∀ x, |f x| ≤ B) → ∀ t : ℝ, 0 < t →
      HasDerivAt (mehlerEntropy f) (-mehlerFisher f t) t

/-- Gross's exact bounded globally Lipschitz interface follows from
de Bruijn's identity alone. Gradient commutation, integrated Fisher decay,
initial continuity, and relaxation introduce no additional premises. -/
theorem bounded_lipschitz_gaussian_logSobolev_reduced2
    (hOU : MehlerEntropyDissipation) : BoundedLipschitzGaussianLogSobolev := by
  intro n f K hf hb
  rw [← mehler_entropy_zero]
  exact entropy_le_half_energy_of_dissipation (mehler_entropy_continuous hf hb)
    (hOU n f K hf hb) (fun t ht => mehler_fisher_decay hf hb ht)
    (mehler_entropy_tendsto_zero hf hb)

/-- The exact sphere interface, reduced further to the concrete de Bruijn
identity. This remains a conditional theorem, not a proof of that identity. -/
theorem bakryEmerySphereLogSobolev_reduced2
    (hOU : MehlerEntropyDissipation) : BakryEmerySphereLogSobolev :=
  bakryEmerySphereLogSobolev_of_bounded_lipschitz_gaussian
    (bounded_lipschitz_gaussian_logSobolev_reduced2 hOU)

/-- `lem:ent-lsi`, with the sole unresolved premise made explicit. -/
theorem geodesic_lipschitz_centered_mgf_reduced2
    (hOU : MehlerEntropyDissipation) {m : ℕ} (hm : 2 ≤ m)
    (g : Vector (m+1) → ℝ) {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L)
    (t : ℝ) :
    (∫ x, Real.exp (t * (g x - ∫ y, g y ∂unitSphereLaw (m+1)))
      ∂unitSphereLaw (m+1)) ≤ Real.exp (L ^ 2 * t ^ 2 / (2 * ((m : ℝ) - 1))) :=
  geodesic_lipschitz_centered_mgf (bakryEmerySphereLogSobolev_reduced2 hOU) hm g hL hg t

open SphericalGaussianJet EntranceLatitudeTangentObservable

/-- The sharp latitude MGF under the further analytic reduction. -/
theorem observable_centered_mgf_le_sharp_reduced2
    (hOU : MehlerEntropyDissipation) {n P : ℕ} (hn : 3 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n+1) P) (hJ : J ∈ regularDisorder)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y, inner ℝ (e y) x = 0)
    {r : ℝ} (hr : |r| ≤ 1) (t : ℝ) :
    mgf (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (latitudeLaw x e r) t ≤
      Real.exp (9 * (derivativeConstant c) ^ 2 * ((n+1 : ℕ) : ℝ) * t ^ 2 /
        (2 * ((n : ℝ) - 2))) :=
  observable_centered_mgf_le_sharp (bakryEmerySphereLogSobolev_reduced2 hOU)
    hn c J hJ x hx e he hr t

/-- The genuine sub-Gaussian predicate under the same single premise. -/
theorem observable_hasSubgaussianMGF_reduced2 (hOU : MehlerEntropyDissipation)
    {n P : ℕ} (hn : 5 ≤ n) (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (hJ : J ∈ regularDisorder) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y, inner ℝ (e y) x = 0)
    {r : ℝ} (hr : |r| ≤ 1) :
    HasSubgaussianMGF
      (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (18 * (derivativeConstant c) ^ 2).toNNReal (latitudeLaw x e r) :=
  observable_hasSubgaussianMGF (bakryEmerySphereLogSobolev_reduced2 hOU)
    hn c J hJ x hx e he hr

/-- Both clauses of `lem:ent-latitude` on the original Gaussian-bank event. -/
theorem center_latitude_mean_and_mgf_reduced2
    (hOU : MehlerEntropyDissipation) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) :=
  center_latitude_mean_and_mgf (bakryEmerySphereLogSobolev_reduced2 hOU) μ hQ

/-- Both latitude clauses on the constant-completed entrance event. -/
theorem constant_completed_center_latitude_mean_and_mgf_reduced2
    (hOU : MehlerEntropyDissipation) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree),
        J ∈ SourceEntranceFullEvent.constantCompletedEntranceEvent n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) :=
  SourceEntranceFullEvent.constant_completed_center_latitude_mean_and_mgf
    (bakryEmerySphereLogSobolev_reduced2 hOU) μ hQ

/-- The full-event `lem:ent-latitude`, reduced to de Bruijn's identity alone. -/
theorem full_center_latitude_mean_and_mgf_reduced2
    (hOU : MehlerEntropyDissipation) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree),
        J ∈ SourceEntranceHarmonicSectors.FullEvent.fullEntranceEvent n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) :=
  SourceEntranceHarmonicSectors.FullEvent.full_center_latitude_mean_and_mgf
    (bakryEmerySphereLogSobolev_reduced2 hOU) μ hQ

end SlowEquilibration.SourceGaussianLogSobolev
