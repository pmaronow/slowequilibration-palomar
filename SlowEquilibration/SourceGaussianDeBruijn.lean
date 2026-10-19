-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceGaussianLogSobolev
public import SlowEquilibration.Upstream.OAI.Probability.SKGap.Gaussian.StandardGaussianProduct

/-! The de Bruijn identity and Gaussian logarithmic Sobolev inequality for
Section 8. We differentiate the actual Mehler integral and its entropy for
bounded globally Lipschitz data. Rademacher's theorem is used at each fixed
positive time with an integrable local difference-quotient envelope.

Scalar Gaussian integration by parts is lifted through an orthonormal basis.
Differentiating product Gaussian rotation invariance then identifies entropy
dissipation with minus the actual integrated Fisher information, using only
first derivatives. The existing reductions yield Gross's exact interface,
the sphere logarithmic Sobolev inequality, and the full-event latitude MGF
without any logarithmic Sobolev or de Bruijn hypothesis.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceGaussianDeBruijn

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SourceGaussianLogSobolev SourceSphereLogSobolevProof
open scoped Topology RealInnerProductSpace NNReal

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exp_comp_integrable {n : ℕ} {f : Vector n → ℝ}
    (hf : Continuous f) {B : ℝ} (hb : ∀ x, |f x| ≤ B)
    (a b : ℝ) (x : Vector n) :
    Integrable (fun y => Real.exp (f (a • x + b • y))) (stdGaussian (Vector n)) := by
  apply Integrable.of_bound (by fun_prop) (Real.exp B)
  exact Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb _))

private theorem bounded_integrable {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → E} (hm : AEStronglyMeasurable f μ) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B) : Integrable f μ :=
  Integrable.of_bound hm B (Eventually.of_forall hb)

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

private theorem hasDerivAt_integral_of_anchored_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : ℝ → Ω → ℝ} {D bound : Ω → ℝ} {t : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 t) (hm : ∀ r ∈ s, AEStronglyMeasurable (F r) μ)
    (hi : Integrable (F t) μ) (hD : AEStronglyMeasurable D μ)
    (hl : ∀ᵐ y ∂μ, ∀ r ∈ s, ‖F r y - F t y‖ ≤ bound y * ‖r - t‖)
    (hb : Integrable bound μ) (hd : ∀ᵐ y ∂μ, HasDerivAt (fun r => F r y) (D y) t) :
    Integrable D μ ∧ HasDerivAt (fun r => ∫ y, F r y ∂μ) (∫ y, D y ∂μ) t := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1
  have hDm : AEStronglyMeasurable (fun y => L (D y)) μ :=
    L.continuous.comp_aestronglyMeasurable hD
  have hh := hasFDerivAt_integral_of_dominated_loc_of_lip' hs hm hi hDm hl hb
    (hd.mono fun y hy => hy.hasFDerivAt)
  have hiD : Integrable D μ := by
    apply (integrable_norm_iff hD).mp
    simpa [L] using hh.1.norm
  refine ⟨hiD, ?_⟩
  convert hh.2.hasDerivAt using 1
  rw [ContinuousLinearMap.integral_apply hh.1]
  simp [L]

/-- A Gaussian affine average may be differentiated through the integral
for bounded Lipschitz data. The nonzero noise coefficient transfers
Rademacher's almost everywhere differentiability to the sampling measure. -/
private theorem gaussian_affine_average_hasDerivAt {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    {a b : ℝ → ℝ} {a' b' t : ℝ} (ha : HasDerivAt a a' t)
    (hb' : HasDerivAt b b' t) (hbt : b t ≠ 0) (x : Vector n) :
    HasDerivAt (fun r => ∫ y, Real.exp (f (a r • x + b r • y))
        ∂stdGaussian (Vector n))
      (∫ y, Real.exp (f (a t • x + b t • y)) *
        fderiv ℝ f (a t • x + b t • y) (a' • x + b' • y)
        ∂stdGaussian (Vector n)) t := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨Ca, hCa⟩ := ha.isBigO_sub.exists_nonneg
  obtain ⟨Cb, hCb⟩ := hb'.isBigO_sub.exists_nonneg
  rcases hCa with ⟨hCa, hla⟩
  rcases hCb with ⟨hCb, hlb⟩
  let s := {r : ℝ | ‖a r - a t‖ ≤ Ca * ‖r - t‖ ∧ ‖b r - b t‖ ≤ Cb * ‖r - t‖}
  have hs : s ∈ 𝓝 t := hla.bound.and hlb.bound
  let D : Vector n → ℝ := fun y => Real.exp (f (a t • x + b t • y)) *
    fderiv ℝ f (a t • x + b t • y) (a' • x + b' • y)
  have hDm : Measurable D := by
    dsimp only [D]
    exact ((hf.continuous.measurable.comp (by fun_prop)).exp).mul
      (isBoundedBilinearMap_apply.continuous.measurable.comp
        (((measurable_fderiv ℝ f).comp
          (by fun_prop : Measurable (fun y : Vector n => a t • x + b t • y))).prodMk
          (by fun_prop : Measurable (fun y : Vector n => a' • x + b' • y))))
  have hd : ∀ᵐ y ∂stdGaussian (Vector n),
      HasDerivAt (fun r => Real.exp (f (a r • x + b r • y))) (D y) t := by
    have hac : stdGaussian (Vector n) ≪ (volume : Measure (Vector n)) := by
      rw [GaussianDensity.stdGaussian_eq_withDensity]
      exact withDensity_absolutelyContinuous _ _
    have hdf : ∀ᵐ y ∂stdGaussian (Vector n),
        DifferentiableAt ℝ f (a t • x + b t • y) := by
      apply hac.ae_le
      exact ((quasiMeasurePreserving_add_left (volume : Measure (Vector n)) (a t • x)).comp
        (Measure.quasiMeasurePreserving_smul (volume : Measure (Vector n)) hbt)).ae
          hf.ae_differentiableAt
    filter_upwards [hdf] with y hy
    exact (hy.hasFDerivAt.comp_hasDerivAt t
      ((ha.smul_const x).add (hb'.smul_const y))).exp
  let bound : Vector n → ℝ := fun y => Real.exp B * K * (Ca * ‖x‖ + Cb * ‖y‖)
  have hi : Integrable bound (stdGaussian (Vector n)) :=
    ((integrable_const (Ca * ‖x‖)).add
      ((IsGaussian.integrable_id (μ := stdGaussian (Vector n))).norm.const_mul Cb)).const_mul _
  apply (hasDerivAt_integral_of_anchored_bound hs
    (fun r _ => (exp_comp_integrable hf.continuous hB _ _ x).aestronglyMeasurable)
    (exp_comp_integrable hf.continuous hB _ _ x) hDm.aestronglyMeasurable
    (Eventually.of_forall fun y r hr => ?_) hi hd).2
  calc
    _ ≤ Real.exp B * K * ‖(a r • x + b r • y) - (a t • x + b t • y)‖ :=
      exp_lipschitz_bound hf hB _ _
    _ ≤ Real.exp B * K * ((Ca * ‖x‖ + Cb * ‖y‖) * ‖r - t‖) := by
      gcongr
      calc
        _ = ‖(a r - a t) • x + (b r - b t) • y‖ := by congr 1; module
        _ ≤ ‖(a r - a t) • x‖ + ‖(b r - b t) • y‖ := norm_add_le _ _
        _ ≤ (Ca * ‖x‖ + Cb * ‖y‖) * ‖r - t‖ := by
          simp only [norm_smul]
          calc
            _ ≤ Ca * ‖r - t‖ * ‖x‖ + Cb * ‖r - t‖ * ‖y‖ := by
              gcongr
              exact hr.1
              exact hr.2
            _ = _ := by ring
    _ = _ := by dsimp [bound]; ring

/-- The explicit velocity of the actual Mehler density. -/
private def mehlerVelocity {n : ℕ} (f : Vector n → ℝ) (t : ℝ) (x : Vector n) : ℝ :=
  ∫ y, Real.exp (f (Real.exp (-t) • x +
    Real.sqrt (1 - Real.exp (-t) ^ 2) • y)) *
      fderiv ℝ f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)
        (-Real.exp (-t) • x +
          (Real.exp (-t) ^ 2 / Real.sqrt (1 - Real.exp (-t) ^ 2)) • y)
    ∂stdGaussian (Vector n)

private theorem mehler_noise_pos {t : ℝ} (ht : 0 < t) :
    0 < 1 - Real.exp (-t) ^ 2 := by
  have ha : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  nlinarith [Real.exp_pos (-t)]

private theorem mehler_drift_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
  simpa using (hasDerivAt_neg t).exp

private theorem mehler_noise_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => Real.sqrt (1 - Real.exp (-s) ^ 2))
      (Real.exp (-t) ^ 2 / Real.sqrt (1 - Real.exp (-t) ^ 2)) t := by
  convert (((mehler_drift_hasDerivAt t).pow 2).const_sub 1).sqrt
    (ne_of_gt (mehler_noise_pos ht)) using 1
  simp only [Pi.pow_apply]
  ring

/-- The time derivative exists at every positive time and every spatial
point for the exact bounded Lipschitz class in `MehlerEntropyDissipation`. -/
private theorem mehler_exponential_hasDerivAt {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 < t) (x : Vector n) :
    HasDerivAt (fun s => mehlerExponential f s x) (mehlerVelocity f t x) t :=
  gaussian_affine_average_hasDerivAt hf hb (mehler_drift_hasDerivAt t)
    (mehler_noise_hasDerivAt ht) (Real.sqrt_pos.mpr (mehler_noise_pos ht)).ne' x

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


/-- Gaussian mass is preserved by the actual Mehler density. -/
private theorem mehler_mass {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x, mehlerExponential f t x ∂stdGaussian (Vector n)) =
      ∫ x, Real.exp (f x) ∂stdGaussian (Vector n) := by
  obtain ⟨B, hB⟩ := hb
  exact integral_gaussian_mix _ _ (mehler_coefficients ht) hf.continuous.measurable.exp
    (fun x => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB x)))

private theorem mehler_local_integrable_bound {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {B : ℝ} (hB : ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 < t) :
    ∃ s ∈ 𝓝 t, ∃ G : Vector n → ℝ, Integrable G (stdGaussian (Vector n)) ∧
      ∀ x, ∀ r ∈ s, ‖mehlerExponential f r x - mehlerExponential f t x‖ ≤
        G x * ‖r - t‖ := by
  obtain ⟨Ca, hCa, hla⟩ := (mehler_drift_hasDerivAt t).isBigO_sub.exists_nonneg
  obtain ⟨Cb, hCb, hlb⟩ := (mehler_noise_hasDerivAt ht).isBigO_sub.exists_nonneg
  let s := {r : ℝ | ‖Real.exp (-r) - Real.exp (-t)‖ ≤ Ca * ‖r - t‖ ∧
    ‖Real.sqrt (1 - Real.exp (-r) ^ 2) - Real.sqrt (1 - Real.exp (-t) ^ 2)‖ ≤ Cb * ‖r - t‖}
  let m := ∫ y : Vector n, ‖y‖ ∂stdGaussian (Vector n)
  let G : Vector n → ℝ := fun x => Real.exp B * K * (Ca * ‖x‖ + Cb * m)
  have hn : Integrable (fun y : Vector n => ‖y‖) (stdGaussian (Vector n)) :=
    (IsGaussian.integrable_id (μ := stdGaussian (Vector n))).norm
  refine ⟨s, hla.bound.and hlb.bound, G,
    ((hn.const_mul Ca).add (integrable_const (Cb * m))).const_mul _, ?_⟩
  intro x r hr
  let H : Vector n → ℝ := fun y => Real.exp B * K * (Ca * ‖x‖ + Cb * ‖y‖)
  have hiH : Integrable H (stdGaussian (Vector n)) :=
    ((integrable_const (Ca * ‖x‖)).add (hn.const_mul Cb)).const_mul _
  have hi (r : ℝ) := exp_comp_integrable hf.continuous hB (Real.exp (-r))
    (Real.sqrt (1 - Real.exp (-r) ^ 2)) x
  rw [mehlerExponential, mehlerExponential, ← integral_sub (hi r) (hi t)]
  calc
    _ ≤ ∫ y, H y * ‖r - t‖ ∂stdGaussian (Vector n) := by
      apply norm_integral_le_of_norm_le (hiH.mul_const _)
      apply Eventually.of_forall
      intro y
      calc
        _ ≤ Real.exp B * K *
            ‖(Real.exp (-r) • x + Real.sqrt (1 - Real.exp (-r) ^ 2) • y) -
              (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)‖ :=
          exp_lipschitz_bound hf hB _ _
        _ ≤ Real.exp B * K * ((Ca * ‖x‖ + Cb * ‖y‖) * ‖r - t‖) := by
          gcongr
          calc
            _ = ‖(Real.exp (-r) - Real.exp (-t)) • x +
                (Real.sqrt (1 - Real.exp (-r) ^ 2) -
                  Real.sqrt (1 - Real.exp (-t) ^ 2)) • y‖ := by congr 1; module
            _ ≤ ‖(Real.exp (-r) - Real.exp (-t)) • x‖ +
                ‖(Real.sqrt (1 - Real.exp (-r) ^ 2) -
                  Real.sqrt (1 - Real.exp (-t) ^ 2)) • y‖ := norm_add_le _ _
            _ ≤ (Ca * ‖x‖ + Cb * ‖y‖) * ‖r - t‖ := by
              simp only [norm_smul]
              calc
                _ ≤ Ca * ‖r - t‖ * ‖x‖ + Cb * ‖r - t‖ * ‖y‖ := by
                  gcongr
                  exact hr.1
                  exact hr.2
                _ = _ := by ring
        _ = H y * ‖r - t‖ := by dsimp [H]; ring
    _ = G x * ‖r - t‖ := by
      rw [integral_mul_const]
      congr 1
      dsimp [H, G, m]
      rw [integral_const_mul, integral_add (integrable_const _) (hn.const_mul Cb),
        integral_const_mul, integral_const]
      simp [integral_const_mul]

private theorem entropy_density_lipschitz {B u v : ℝ}
    (_hB : 0 ≤ B) (hu : Real.exp (-B) ≤ u ∧ u ≤ Real.exp B)
    (hv : Real.exp (-B) ≤ v ∧ v ≤ Real.exp B) :
    ‖u * Real.log u - v * Real.log v‖ ≤ (B + 1) * ‖u - v‖ := by
  have hd (z : ℝ) (hz : z ∈ Icc (Real.exp (-B)) (Real.exp B)) :
      HasDerivAt (fun z => z * Real.log z) (Real.log z + 1) z := by
    have hp : 0 < z := (Real.exp_pos (-B)).trans_le hz.1
    have he : (1 : ℝ) * Real.log z + z * z⁻¹ = Real.log z + 1 := by
      rw [one_mul, mul_inv_cancel₀ hp.ne']
    exact he ▸ (hasDerivAt_id z).mul (Real.hasDerivAt_log hp.ne')
  apply Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hd z hz).differentiableAt) (fun z hz => ?_)
    (convex_Icc _ _) hv hu
  rw [(hd z hz).deriv, Real.norm_eq_abs]
  have hp : 0 < z := (Real.exp_pos (-B)).trans_le hz.1
  have hl : -B ≤ Real.log z := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hz.1
  have hh : Real.log z ≤ B := by
    simpa only [Real.log_exp] using Real.log_le_log hp hz.2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Entropy differentiation is justified by an integrable local envelope;
only the Gaussian integration-by-parts evaluation of this integral remains. -/
private theorem mehler_entropy_hasDerivAt {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (mehlerEntropy f)
      (∫ x, (1 + Real.log (mehlerExponential f t x)) * mehlerVelocity f t x
        ∂stdGaussian (Vector n)) t := by
  obtain ⟨B, hB⟩ := hb
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0)
  obtain ⟨s, hs, G, hGi, hG⟩ := mehler_local_integrable_bound hf hB ht
  let D : Vector n → ℝ := fun x =>
    (1 + Real.log (mehlerExponential f t x)) * mehlerVelocity f t x
  have hvel : Measurable (mehlerVelocity f t) := by
    have hh : Measurable (fun p : Vector n × Vector n =>
        Real.exp (f (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-t) ^ 2) • p.2)) *
          fderiv ℝ f (Real.exp (-t) • p.1 + Real.sqrt (1 - Real.exp (-t) ^ 2) • p.2)
            (-Real.exp (-t) • p.1 +
              (Real.exp (-t) ^ 2 / Real.sqrt (1 - Real.exp (-t) ^ 2)) • p.2)) := by
      exact ((hf.continuous.measurable.comp (by fun_prop)).exp).mul
        (isBoundedBilinearMap_apply.continuous.measurable.comp
          (((measurable_fderiv ℝ f).comp (by fun_prop)).prodMk (by fun_prop)))
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  have hct : Continuous (mehlerExponential f t) :=
    (mehler_continuous hf.continuous hB).comp (continuous_const.prodMk continuous_id)
  have hD : AEStronglyMeasurable D (stdGaussian (Vector n)) :=
    ((measurable_const.add hct.measurable.log).mul hvel).aestronglyMeasurable
  have hder : ∀ x, HasDerivAt
      (fun s => mehlerExponential f s x * Real.log (mehlerExponential f s x)) (D x) t := by
    intro x
    have hu := mehler_exponential_hasDerivAt hf ⟨B, hB⟩ ht x
    have hp := (mehler_pos hf.continuous hB t x).ne'
    convert hu.mul (hu.log hp) using 1
    dsimp [D]
    field_simp
    ring
  have hh := hasDerivAt_integral_of_anchored_bound hs
    (fun r _ => (mehler_entropy_integrable hf.continuous hB r).aestronglyMeasurable)
    (mehler_entropy_integrable hf.continuous hB t) hD
    (Eventually.of_forall fun x r hr =>
      (entropy_density_lipschitz hB0 (mehler_bounds hf.continuous hB r x)
        (mehler_bounds hf.continuous hB t x)).trans (by
          calc
            _ ≤ (B + 1) * (G x * ‖r - t‖) :=
              mul_le_mul_of_nonneg_left (hG x r hr) (by positivity)
            _ = ((B + 1) * G x) * ‖r - t‖ := by ring))
    (hGi.const_mul (B + 1)) (Eventually.of_forall hder)
  have hsub := hh.2.sub_const
    ((∫ x, Real.exp (f x) ∂stdGaussian (Vector n)) *
      Real.log (∫ x, Real.exp (f x) ∂stdGaussian (Vector n)))
  apply hsub.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with r hr
  simp only [mehlerEntropy, mehler_mass hf ⟨B, hB⟩ hr.le]

private theorem gaussianProduct_coordinate_IBP_ae {n : ℕ} (i : Fin (n+1))
    {f df : (Fin (n+1) → ℝ) → ℝ} {K : ℝ≥0} {C D : ℝ}
    (hf : Continuous f) (hdf : AEStronglyMeasurable df (OAI.SKGap.standardGaussianProduct (n+1)))
    (hfbound : ∀ x, ‖f x‖ ≤ C) (hdfbound : ∀ x, ‖df x‖ ≤ D)
    (hLip : ∀ u : Fin n → ℝ, LipschitzWith K (fun z => f (i.insertNth z u)))
    (hder : ∀ᵐ u ∂OAI.SKGap.standardGaussianProduct n, ∀ᵐ z ∂gaussianReal 0 1,
      HasDerivAt (fun z => f (i.insertNth z u)) (df (i.insertNth z u)) z) :
    (∫ x, x i * f x ∂OAI.SKGap.standardGaussianProduct (n+1)) =
      ∫ x, df x ∂OAI.SKGap.standardGaussianProduct (n+1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
  have hp : MeasurePreserving e.symm
      ((gaussianReal 0 1).prod (OAI.SKGap.standardGaussianProduct n))
      (OAI.SKGap.standardGaussianProduct (n+1)) :=
    (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) i).symm
  have hi : Integrable (fun x : Fin (n+1) → ℝ => x i * f x)
      (OAI.SKGap.standardGaussianProduct (n+1)) := by
    simpa only [mul_comm, OAI.SKGap.standardGaussianProduct] using
      (integrable_eval (i := i) IsGaussian.integrable_id).bdd_mul
        hf.aestronglyMeasurable (ae_of_all _ hfbound)
  have hi' : Integrable df (OAI.SKGap.standardGaussianProduct (n+1)) :=
    Integrable.of_bound hdf D (ae_of_all _ hdfbound)
  have hsplit (g : (Fin (n+1) → ℝ) → ℝ)
      (hg : Integrable g (OAI.SKGap.standardGaussianProduct (n+1))) :
      (∫ x, g x ∂OAI.SKGap.standardGaussianProduct (n+1)) =
        ∫ u, ∫ z, g (i.insertNth z u) ∂gaussianReal 0 1
          ∂OAI.SKGap.standardGaussianProduct n := by
    have hi2 : Integrable (fun x => g (e.symm x))
        ((gaussianReal 0 1).prod (OAI.SKGap.standardGaussianProduct n)) :=
      hp.integrable_comp_of_integrable hg
    rw [← hp.integral_comp' g, integral_prod _ hi2, integral_integral_swap hi2]
    rfl
  rw [hsplit _ hi, hsplit _ hi']
  apply integral_congr_ae
  filter_upwards [hder] with u hu
  simp only [Fin.insertNth_apply_same]
  have hscalar := OAI.SKGap.gaussian_lipschitz_IBP
    (d := 0) (s := 1) (by norm_num : (0 : ℝ≥0) < 1)
    (hLip u) (fun z => hfbound (i.insertNth z u))
  simp only [sub_zero, NNReal.coe_one, one_mul] at hscalar
  rw [hscalar]
  exact integral_congr_ae (hu.mono fun z hz => hz.deriv)

set_option maxHeartbeats 2400000 in
/-- First-order Gaussian integration by parts for bounded globally Lipschitz
functions, with the actual almost everywhere Fréchet derivative. -/
private theorem stdGaussian_directional_IBP {n : ℕ} {F : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K F) (hb : ∃ C : ℝ, ∀ x, |F x| ≤ C)
    (v : Vector n) :
    (∫ x, inner ℝ v x * F x ∂stdGaussian (Vector n)) =
      ∫ x, fderiv ℝ F x v ∂stdGaussian (Vector n) := by
  classical
  obtain ⟨C, hC⟩ := hb
  cases n with
  | zero =>
      have hv : v = 0 := by
        ext i
        exact Fin.elim0 i
      simp [hv]
  | succ n =>
      let b := EuclideanSpace.basisFun (Fin (n+1)) ℝ
      let A : (Fin (n+1) → ℝ) → Vector (n+1) := fun q => ∑ j, q j • b j
      have hAm : Measurable A := by fun_prop
      have hmap : (OAI.SKGap.standardGaussianProduct (n+1)).map A =
          stdGaussian (Vector (n+1)) := by
        simpa only [OAI.SKGap.standardGaussianProduct] using
          (stdGaussian_eq_map_pi_orthonormalBasis b).symm
      have hAi (i : Fin (n+1)) (q : Fin (n+1) → ℝ) :
          inner ℝ (b i) (A q) = q i := by
        dsimp [A]
        simp only [inner_sum, inner_smul_right, b.inner_eq_ite]
        simp
      have hmD (w : Vector (n+1)) :
          Measurable (fun x : Vector (n+1) => fderiv ℝ F x w) :=
        (measurable_fderiv ℝ F).apply_continuousLinearMap w
      have hBD (w x : Vector (n+1)) : ‖fderiv ℝ F x w‖ ≤ (K : ℝ) * ‖w‖ := by
        exact ((fderiv ℝ F x).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
      have hiD (w : Vector (n+1)) :
          Integrable (fun x => fderiv ℝ F x w) (stdGaussian (Vector (n+1))) :=
        Integrable.of_bound (hmD w).aestronglyMeasurable ((K : ℝ) * ‖w‖)
          (Eventually.of_forall (hBD w))
      have hiL (w : Vector (n+1)) :
          Integrable (fun x => inner ℝ w x * F x) (stdGaussian (Vector (n+1))) := by
        have hh : Integrable (fun x => F x * inner ℝ w x)
            (stdGaussian (Vector (n+1))) :=
          (IsGaussian.integrable_dual (stdGaussian (Vector (n+1))) (innerSL ℝ w)).bdd_mul
            hf.continuous.aestronglyMeasurable
              (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)
        simpa only [mul_comm] using hh
      have hγac : stdGaussian (Vector (n+1)) ≪ (volume : Measure (Vector (n+1))) := by
        rw [GaussianDensity.stdGaussian_eq_withDensity]
        exact withDensity_absolutelyContinuous _ _
      have hdγ : ∀ᵐ x ∂stdGaussian (Vector (n+1)), DifferentiableAt ℝ F x :=
        hγac.ae_le hf.ae_differentiableAt
      have hdA : ∀ᵐ q ∂OAI.SKGap.standardGaussianProduct (n+1),
          DifferentiableAt ℝ F (A q) := by
        rw [← hmap] at hdγ
        exact ae_of_ae_map hAm.aemeasurable hdγ
      have hcoord (i : Fin (n+1)) :
          (∫ x, inner ℝ (b i) x * F x ∂stdGaussian (Vector (n+1))) =
            ∫ x, fderiv ℝ F x (b i) ∂stdGaussian (Vector (n+1)) := by
        let g : (Fin (n+1) → ℝ) → ℝ := fun q => F (A q)
        let dg : (Fin (n+1) → ℝ) → ℝ := fun q => fderiv ℝ F (A q) (b i)
        have hg : Continuous g := hf.continuous.comp (by fun_prop : Continuous A)
        have hdg : Measurable dg := (hmD (b i)).comp hAm
        have hAinsert (u : Fin n → ℝ) (z : ℝ) :
            A (i.insertNth z u) = z • b i + ∑ j, u j • b (i.succAbove j) := by
          dsimp [A]
          rw [Fin.sum_univ_succAbove _ i]
          simp
        have hcurve (u : Fin n → ℝ) (z : ℝ) :
            HasDerivAt (fun z => A (i.insertNth z u)) (b i) z := by
          simp_rw [hAinsert]
          simpa using ((hasDerivAt_id z).smul_const (b i)).add_const
            (∑ j, u j • b (i.succAbove j))
        have hLip (u : Fin n → ℝ) : LipschitzWith K (fun z => g (i.insertNth z u)) := by
          apply LipschitzWith.of_dist_le_mul
          intro z w
          have he : A (i.insertNth z u) - A (i.insertNth w u) = (z-w) • b i := by
            simp only [hAinsert, add_sub_add_right_eq_sub, sub_smul]
          simpa only [g, dist_eq_norm, he, norm_smul, b.norm_eq_one i,
            Real.norm_eq_abs, mul_one] using
            hf.norm_sub_le (A (i.insertNth z u)) (A (i.insertNth w u))
        let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i
        have hp : MeasurePreserving e.symm
            ((gaussianReal 0 1).prod (OAI.SKGap.standardGaussianProduct n))
            (OAI.SKGap.standardGaussianProduct (n+1)) :=
          (measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) i).symm
        have hslices : ∀ᵐ u ∂OAI.SKGap.standardGaussianProduct n,
            ∀ᵐ z ∂gaussianReal 0 1, DifferentiableAt ℝ F (A (i.insertNth z u)) :=
          Measure.ae_ae_of_ae_prod
            ((hp.comp (Measure.measurePreserving_swap)).quasiMeasurePreserving.ae hdA)
        have hder : ∀ᵐ u ∂OAI.SKGap.standardGaussianProduct n,
            ∀ᵐ z ∂gaussianReal 0 1,
              HasDerivAt (fun z => g (i.insertNth z u)) (dg (i.insertNth z u)) z := by
          filter_upwards [hslices] with u hu
          filter_upwards [hu] with z hz
          exact hz.hasFDerivAt.comp_hasDerivAt z (hcurve u z)
        have hprod := gaussianProduct_coordinate_IBP_ae i hg hdg.aestronglyMeasurable
          (fun q => by simpa only [g, Real.norm_eq_abs] using hC (A q))
          (D := (K : ℝ))
          (fun q => by simpa only [dg, b.norm_eq_one i, mul_one] using hBD (b i) (A q))
          hLip hder
        have hleft :
            (∫ x, inner ℝ (b i) x * F x ∂stdGaussian (Vector (n+1))) =
              ∫ q, q i * g q ∂OAI.SKGap.standardGaussianProduct (n+1) := by
          have hm : AEStronglyMeasurable
              (fun x : Vector (n+1) => inner ℝ (b i) x * F x)
              ((OAI.SKGap.standardGaussianProduct (n+1)).map A) := by
            rw [hmap]
            exact (hiL (b i)).aestronglyMeasurable
          rw [← hmap, integral_map hAm.aemeasurable hm]
          simp only [hAi, g]
        have hright :
            (∫ x, fderiv ℝ F x (b i) ∂stdGaussian (Vector (n+1))) =
              ∫ q, dg q ∂OAI.SKGap.standardGaussianProduct (n+1) := by
          rw [← hmap, integral_map hAm.aemeasurable (hmD (b i)).aestronglyMeasurable]
        exact hleft.trans (hprod.trans hright.symm)
      have hleft (x : Vector (n+1)) : inner ℝ v x * F x =
          ∑ i, inner ℝ (b i) v * (inner ℝ (b i) x * F x) := by
        calc
          _ = inner ℝ (∑ i, inner ℝ (b i) v • b i) x * F x := by rw [b.sum_repr']
          _ = _ := by simp only [sum_inner, real_inner_smul_left, Finset.sum_mul, mul_assoc]
      have hright (x : Vector (n+1)) : fderiv ℝ F x v =
          ∑ i, inner ℝ (b i) v * fderiv ℝ F x (b i) := by
        calc
          _ = fderiv ℝ F x (∑ i, inner ℝ (b i) v • b i) := by rw [b.sum_repr']
          _ = _ := by simp only [map_sum, map_smul, smul_eq_mul]
      calc
        _ = ∫ x, ∑ i, inner ℝ (b i) v * (inner ℝ (b i) x * F x)
            ∂stdGaussian (Vector (n+1)) :=
          integral_congr_ae (Eventually.of_forall hleft)
        _ = ∑ i, inner ℝ (b i) v *
            (∫ x, inner ℝ (b i) x * F x ∂stdGaussian (Vector (n+1))) := by
          rw [integral_finsetSum Finset.univ (fun i _ => (hiL (b i)).const_mul _)]
          simp only [integral_const_mul]
        _ = ∑ i, inner ℝ (b i) v *
            (∫ x, fderiv ℝ F x (b i) ∂stdGaussian (Vector (n+1))) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hcoord i]
        _ = ∫ x, ∑ i, inner ℝ (b i) v * fderiv ℝ F x (b i)
            ∂stdGaussian (Vector (n+1)) := by
          rw [integral_finsetSum Finset.univ (fun i _ => (hiD (b i)).const_mul _)]
          simp only [integral_const_mul]
        _ = _ := integral_congr_ae (Eventually.of_forall fun x => (hright x).symm)

/-- The Gaussian score identity for the affine exponential kernel, using
only the almost everywhere derivative of the bounded Lipschitz datum. -/
private theorem gaussian_affine_score {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    (a b : ℝ) (hb0 : b ≠ 0) (x v : Vector n) :
    (∫ y, Real.exp (f (a • x + b • y)) * inner ℝ v y ∂stdGaussian (Vector n)) =
      b * ∫ y, Real.exp (f (a • x + b • y)) *
        fderiv ℝ f (a • x + b • y) v ∂stdGaussian (Vector n) := by
  obtain ⟨B, hB⟩ := hb
  let F : Vector n → ℝ := fun y => Real.exp (f (a • x + b • y))
  let C : ℝ≥0 := ⟨Real.exp B * K * |b|, by positivity⟩
  have hF : LipschitzWith C F := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    change ‖F y - F z‖ ≤ (Real.exp B * (K : ℝ) * |b|) * ‖y - z‖
    have hh := exp_lipschitz_bound hf hB (a • x + b • y) (a • x + b • z)
    simpa only [F, add_sub_add_left_eq_sub, ← smul_sub,
      norm_smul, Real.norm_eq_abs, mul_assoc] using hh
  have hFb : ∃ D : ℝ, ∀ y, |F y| ≤ D := by
    refine ⟨Real.exp B, fun y => ?_⟩
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB _))
  have hstein := stdGaussian_directional_IBP hF hFb v
  have hac : stdGaussian (Vector n) ≪ (volume : Measure (Vector n)) := by
    rw [GaussianDensity.stdGaussian_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have hdf : ∀ᵐ y ∂stdGaussian (Vector n), DifferentiableAt ℝ f (a • x + b • y) := by
    apply hac.ae_le
    exact ((quasiMeasurePreserving_add_left (volume : Measure (Vector n)) (a • x)).comp
      (Measure.quasiMeasurePreserving_smul (volume : Measure (Vector n)) hb0)).ae
        hf.ae_differentiableAt
  calc
    _ = ∫ y, fderiv ℝ F y v ∂stdGaussian (Vector n) := by
      simpa only [F, mul_comm] using hstein
    _ = ∫ y, b * (Real.exp (f (a • x + b • y)) *
        fderiv ℝ f (a • x + b • y) v) ∂stdGaussian (Vector n) := by
      apply integral_congr_ae
      filter_upwards [hdf] with y hy
      have hinner : HasFDerivAt (fun y : Vector n => a • x + b • y)
          (b • ContinuousLinearMap.id ℝ (Vector n)) y :=
        ((hasFDerivAt_id y).const_smul b).const_add _
      rw [show fderiv ℝ F y = _ from ((hy.hasFDerivAt.comp y hinner).exp).fderiv]
      simp only [smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, Function.comp_apply]
      ring
    _ = _ := integral_const_mul _ _

private theorem score_pairing {n : ℕ} {h : Vector n → ℝ}
    {D : Vector n → (Vector n →L[ℝ] ℝ)} {a b u : ℝ} (ha : a ≠ 0)
    (hD : Integrable D (stdGaussian (Vector n)))
    (L : Vector n →L[ℝ] ℝ) (hL : L = a • ∫ y, D y ∂stdGaussian (Vector n))
    (hS : ∀ v : Vector n,
      (∫ y, h y * inner ℝ v y ∂stdGaussian (Vector n)) =
        b * ∫ y, D y v ∂stdGaussian (Vector n)) :
    (∫ y, h y * ((u⁻¹) • L) y ∂stdGaussian (Vector n)) =
      (b / a) * (‖L‖ ^ 2 / u) := by
  let v := (InnerProductSpace.toDual ℝ (Vector n)).symm L
  have hv (y : Vector n) : L y = inner ℝ v y :=
    (InnerProductSpace.toDual_symm_apply (x := y) (y := L)).symm
  have hn : L v = ‖L‖ ^ 2 := by
    rw [hv v, real_inner_self_eq_norm_sq]
    dsimp [v]
    rw [(InnerProductSpace.toDual ℝ (Vector n)).symm.norm_map]
  have he := congrArg (fun C : Vector n →L[ℝ] ℝ => C v) hL
  simp only [smul_apply, smul_eq_mul] at he
  have hDv : (∫ y, D y v ∂stdGaussian (Vector n)) = ‖L‖ ^ 2 / a := by
    rw [← ContinuousLinearMap.integral_apply hD]
    apply (eq_div_iff ha).mpr
    nlinarith only [hn, he]
  simp only [smul_apply, smul_eq_mul]
  calc
    _ = u⁻¹ * ∫ y, h y * inner ℝ v y ∂stdGaussian (Vector n) := by
      simp_rw [hv, show ∀ y, h y * (u⁻¹ * inner ℝ v y) =
        u⁻¹ * (h y * inner ℝ v y) by intro y; ring]
      rw [integral_const_mul]
    _ = u⁻¹ * (b * (‖L‖ ^ 2 / a)) := by rw [hS v, hDv]
    _ = (b / a) * (‖L‖ ^ 2 / u) := by ring

/-- The Gaussian score paired with the logarithmic gradient of the Mehler
density is exactly its pointwise Fisher integrand, with the correct factor. -/
private theorem mehler_score_pairing {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 < t) (x : Vector n) :
    (∫ y, Real.exp (f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)) *
        ((mehlerExponential f t x)⁻¹ • fderiv ℝ (mehlerExponential f t) x) y
      ∂stdGaussian (Vector n)) =
      (Real.sqrt (1 - Real.exp (-t) ^ 2) / Real.exp (-t)) *
        (‖fderiv ℝ (mehlerExponential f t) x‖ ^ 2 / mehlerExponential f t x) := by
  obtain ⟨B, hB⟩ := hb
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-t) ^ 2)
  let z : Vector n → Vector n := fun y => a • x + b • y
  let D : Vector n → Vector n →L[ℝ] ℝ := fun y => Real.exp (f (z y)) • fderiv ℝ f (z y)
  have hDm : Measurable D :=
    ((hf.continuous.measurable.comp (by fun_prop)).exp).smul
      ((measurable_fderiv ℝ f).comp (by fun_prop))
  have hDi : Integrable D (stdGaussian (Vector n)) := by
    apply Integrable.of_bound hDm.aestronglyMeasurable (Real.exp B * K)
    exact Eventually.of_forall fun y => by
      dsimp only [D]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self _).trans (hB _)))
        (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _) (Real.exp_pos _).le
  apply score_pairing (a := a) (b := b) (D := D) (Real.exp_pos (-t)).ne' hDi
    (fderiv ℝ (mehlerExponential f t) x)
    (mehler_fderiv_commutation hf ⟨B, hB⟩ ht x).fderiv
  intro v
  simpa only [D, z, a, b, smul_apply, smul_eq_mul] using
    gaussian_affine_score hf ⟨B, hB⟩ a b
      (Real.sqrt_pos.mpr (mehler_noise_pos ht)).ne' x v

private theorem gaussian_rotation_ibp {n : ℕ} {f A : Vector n → ℝ}
    {K L : ℝ≥0} (hf : LipschitzWith K f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) (hA : LipschitzWith L A)
    (hc : ∃ C : ℝ, ∀ x, |A x| ≤ C) (hAd : Differentiable ℝ A)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (∫ x, A x * (∫ y, Real.exp (f (a • x + b • y)) *
        fderiv ℝ f (a • x + b • y) (a • y - b • x) ∂stdGaussian (Vector n))
      ∂stdGaussian (Vector n)) =
    -(∫ x, ∫ y, Real.exp (f (a • x + b • y)) * fderiv ℝ A x y
      ∂stdGaussian (Vector n) ∂stdGaussian (Vector n)) := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨C, hC⟩ := hc
  let γ := stdGaussian (Vector n)
  let ν := γ.prod γ
  let z : Vector n × Vector n → Vector n := fun p => a • p.1 + b • p.2
  let v : Vector n × Vector n → Vector n := fun p => a • p.2 - b • p.1
  let H : Vector n × Vector n → ℝ := fun p => A p.1 * Real.exp (f (z p))
  let U : Vector n × Vector n → ℝ := fun p => Real.exp (f (z p)) * fderiv ℝ A p.1 p.2
  let V : Vector n × Vector n → ℝ := fun p => A p.1 * Real.exp (f (z p)) * fderiv ℝ f (z p) (v p)
  let q : Vector n × Vector n → ℝ := fun p => ‖p.1‖ + ‖p.2‖
  have hC0 : 0 ≤ C := (abs_nonneg (A 0)).trans (hC 0)
  have heB (w : Vector n) : ‖Real.exp (f w)‖ ≤ Real.exp B := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hB w))
  have hAm : Measurable A := hA.continuous.measurable
  have hfm : Measurable f := hf.continuous.measurable
  have hzm : Measurable z := by fun_prop
  have hvm : Measurable v := by fun_prop
  have hHm : Measurable H := (hAm.comp measurable_fst).mul ((hfm.comp hzm).exp)
  have hAfm : Measurable (fun p : Vector n × Vector n => fderiv ℝ A p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous.measurable.comp
      (((measurable_fderiv ℝ A).comp measurable_fst).prodMk measurable_snd)
  have hffm : Measurable (fun p : Vector n × Vector n => fderiv ℝ f (z p) (v p)) :=
    isBoundedBilinearMap_apply.continuous.measurable.comp
      (((measurable_fderiv ℝ f).comp hzm).prodMk hvm)
  have hUm : Measurable U := ((hfm.comp hzm).exp).mul hAfm
  have hVm : Measurable V := ((hAm.comp measurable_fst).mul ((hfm.comp hzm).exp)).mul hffm
  have hqi : Integrable q ν :=
    ((IsGaussian.integrable_id (μ := γ)).norm.comp_fst γ).add
      ((IsGaussian.integrable_id (μ := γ)).norm.comp_snd γ)
  have hUi : Integrable U ν := by
    apply (hqi.const_mul (Real.exp B * (L : ℝ))).mono' hUm.aestronglyMeasurable
    apply Eventually.of_forall
    intro p
    have hd : ‖fderiv ℝ A p.1 p.2‖ ≤ (L : ℝ) * ‖p.2‖ :=
      ((fderiv ℝ A p.1).le_opNorm p.2).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hA) (norm_nonneg _))
    calc
      ‖U p‖ = ‖Real.exp (f (z p))‖ * ‖fderiv ℝ A p.1 p.2‖ := norm_mul _ _
      _ ≤ Real.exp B * ((L : ℝ) * ‖p.2‖) := mul_le_mul (heB _) hd (norm_nonneg _) (Real.exp_pos B).le
      _ ≤ (Real.exp B * (L : ℝ)) * q p := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg p.1)) (by positivity)
  have hvbound (p : Vector n × Vector n) : ‖v p‖ ≤ (|a| + |b|) * q p := by
    calc
      _ ≤ ‖a • p.2‖ + ‖b • p.1‖ := norm_sub_le _ _
      _ = |a| * ‖p.2‖ + |b| * ‖p.1‖ := by simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ |a| * q p + |b| * q p :=
        add_le_add (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg p.1)) (abs_nonneg a))
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg p.2)) (abs_nonneg b))
      _ = _ := by ring
  have hVi : Integrable V ν := by
    apply (hqi.const_mul (C * Real.exp B * (K : ℝ) * (|a| + |b|))).mono' hVm.aestronglyMeasurable
    apply Eventually.of_forall
    intro p
    have hd : ‖fderiv ℝ f (z p) (v p)‖ ≤ (K : ℝ) * ‖v p‖ :=
      ((fderiv ℝ f (z p)).le_opNorm (v p)).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _))
    calc
      ‖V p‖ = ‖A p.1‖ * ‖Real.exp (f (z p))‖ * ‖fderiv ℝ f (z p) (v p)‖ := by simp only [V, norm_mul]
      _ ≤ C * Real.exp B * ((K : ℝ) * ((|a| + |b|) * q p)) :=
        mul_le_mul (mul_le_mul (by simpa only [Real.norm_eq_abs] using hC p.1)
          (heB _) (norm_nonneg _) hC0)
          (hd.trans (mul_le_mul_of_nonneg_left (hvbound p) K.coe_nonneg))
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hHi : Integrable H ν := by
    apply bounded_integrable hHm.aestronglyMeasurable (B := C * Real.exp B)
    intro p
    change ‖A p.1 * Real.exp (f (z p))‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul (by simpa only [Real.norm_eq_abs] using hC p.1) (heB _) (norm_nonneg _) hC0
  have hmove (θ : ℝ) (x y : Vector n) :
      ‖Real.cos θ • x + Real.sin θ • y - x‖ ≤ (‖x‖ + ‖y‖) * ‖θ‖ := by
    have hcos : ‖Real.cos θ - 1‖ ≤ ‖θ‖ := by
      simpa only [Real.cos_zero, sub_zero, Real.norm_eq_abs] using Real.abs_cos_sub_cos_le θ 0
    have hsin : ‖Real.sin θ‖ ≤ ‖θ‖ := by
      simpa only [Real.norm_eq_abs] using (Real.abs_sin_le_abs (x := θ))
    calc
      _ = ‖(Real.cos θ - 1) • x + Real.sin θ • y‖ := by congr 1; module
      _ ≤ ‖(Real.cos θ - 1) • x‖ + ‖Real.sin θ • y‖ := norm_add_le _ _
      _ ≤ ‖θ‖ * ‖x‖ + ‖θ‖ * ‖y‖ := by
        simp only [norm_smul]
        exact add_le_add (mul_le_mul_of_nonneg_right hcos (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hsin (norm_nonneg _))
      _ = _ := by ring
  let D : ℝ := Real.exp B * ((L : ℝ) + C * K * (|a| + |b|))
  have hrot0 (p : Vector n × Vector n) : ContinuousLinearMap.rotation 0 p = p := by
    simp [ContinuousLinearMap.rotation_apply]
  have hbound (p : Vector n × Vector n) (θ : ℝ) :
      ‖H (ContinuousLinearMap.rotation θ p) - H p‖ ≤ (D * q p) * ‖θ‖ := by
    let p' := ContinuousLinearMap.rotation θ p
    have hx : ‖p'.1 - p.1‖ ≤ q p * ‖θ‖ := by
      simpa only [p', q, ContinuousLinearMap.rotation_apply] using hmove θ p.1 p.2
    have hy : ‖p'.2 - p.2‖ ≤ q p * ‖θ‖ := by
      simpa [p', q, ContinuousLinearMap.rotation_apply, Real.cos_neg, Real.sin_neg,
        add_comm, neg_smul] using hmove (-θ) p.2 p.1
    have hz : ‖z p' - z p‖ ≤ (|a| + |b|) * q p * ‖θ‖ := by
      calc
        _ = ‖a • (p'.1 - p.1) + b • (p'.2 - p.2)‖ := by congr 1; dsimp [z]; module
        _ ≤ ‖a • (p'.1 - p.1)‖ + ‖b • (p'.2 - p.2)‖ := norm_add_le _ _
        _ ≤ |a| * (q p * ‖θ‖) + |b| * (q p * ‖θ‖) := by
          simp only [norm_smul, Real.norm_eq_abs]
          exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg a))
            (mul_le_mul_of_nonneg_left hy (abs_nonneg b))
        _ = _ := by ring
    have hAA : ‖A p'.1 - A p.1‖ ≤ (L : ℝ) * (q p * ‖θ‖) :=
      (hA.norm_sub_le _ _).trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg)
    have hFF : ‖Real.exp (f (z p')) - Real.exp (f (z p))‖ ≤
        Real.exp B * K * ((|a| + |b|) * q p * ‖θ‖) :=
      (exp_lipschitz_bound hf hB _ _).trans
        (mul_le_mul_of_nonneg_left hz (mul_nonneg (Real.exp_pos B).le K.coe_nonneg))
    calc
      _ = ‖(A p'.1 - A p.1) * Real.exp (f (z p')) +
          A p.1 * (Real.exp (f (z p')) - Real.exp (f (z p)))‖ := by
        congr 1; dsimp [H, p']; ring
      _ ≤ ‖(A p'.1 - A p.1) * Real.exp (f (z p'))‖ +
          ‖A p.1 * (Real.exp (f (z p')) - Real.exp (f (z p)))‖ := norm_add_le _ _
      _ ≤ ((L : ℝ) * (q p * ‖θ‖)) * Real.exp B +
          C * (Real.exp B * K * ((|a| + |b|) * q p * ‖θ‖)) := by
        simp only [norm_mul]
        exact add_le_add (mul_le_mul hAA (heB _) (norm_nonneg _) (by positivity))
          (mul_le_mul (by simpa only [Real.norm_eq_abs] using hC p.1) hFF (norm_nonneg _) hC0)
      _ = _ := by dsimp [D]; ring
  have hdf : ∀ᵐ p ∂ν, DifferentiableAt ℝ f (z p) := by
    have hac : γ ≪ (volume : Measure (Vector n)) := by
      change stdGaussian (Vector n) ≪ (volume : Measure (Vector n))
      rw [GaussianDensity.stdGaussian_eq_withDensity]
      exact withDensity_absolutelyContinuous _ _
    apply ae_of_ae_map hzm.aemeasurable
    have hmix : ν.map z = γ := gaussian_mix_map a b hab
    rw [hmix]
    exact hac.ae_le hf.ae_differentiableAt
  have hdiff : ∀ᵐ p ∂ν, HasDerivAt
      (fun θ => H (ContinuousLinearMap.rotation θ p)) (U p + V p) 0 := by
    filter_upwards [hdf] with p hp
    have hx : HasDerivAt (fun θ : ℝ => (ContinuousLinearMap.rotation θ p).1) p.2 0 := by
      convert! ((Real.hasDerivAt_cos 0).smul_const p.1).add
        ((Real.hasDerivAt_sin 0).smul_const p.2) using 1
      simp
    have hy : HasDerivAt (fun θ : ℝ => (ContinuousLinearMap.rotation θ p).2) (-p.1) 0 := by
      convert! (((Real.hasDerivAt_sin 0).neg).smul_const p.1).add
        ((Real.hasDerivAt_cos 0).smul_const p.2) using 1
      simp
    have hz : HasDerivAt (fun θ : ℝ => z (ContinuousLinearMap.rotation θ p)) (v p) 0 := by
      convert (hx.const_smul a).add (hy.const_smul b) using 1
      simp only [v, smul_neg, sub_eq_add_neg]
    have hp' : DifferentiableAt ℝ f (z (ContinuousLinearMap.rotation 0 p)) := by
      simpa only [hrot0] using hp
    have hh := ((hAd _).hasFDerivAt.comp_hasDerivAt 0 hx).mul
      ((hp'.hasFDerivAt.comp_hasDerivAt 0 hz).exp)
    convert hh using 1
    · rfl
    · simp only [Function.comp_apply, hrot0, U, V]
      ring
  have hinv (θ : ℝ) :
      (∫ p, H (ContinuousLinearMap.rotation θ p) ∂ν) = ∫ p, H p ∂ν := by
    have hmap : ν.map (ContinuousLinearMap.rotation θ) = ν :=
      IsGaussian.map_rotation_eq_self integral_id_stdGaussian θ
    have hh := integral_map (μ := ν)
      (ContinuousLinearMap.rotation θ).measurable.aemeasurable
      (show AEStronglyMeasurable H (ν.map (ContinuousLinearMap.rotation θ)) by
        rw [hmap]; exact hHm.aestronglyMeasurable)
    rw [hmap] at hh
    exact hh.symm
  have hd := (hasDerivAt_integral_of_anchored_bound (s := univ) (by exact univ_mem)
    (fun θ _ => (hHm.comp (ContinuousLinearMap.rotation θ).measurable).aestronglyMeasurable)
    (by simpa only [hrot0] using hHi) (hUm.add hVm).aestronglyMeasurable
    (Eventually.of_forall fun p θ _ => by simpa only [hrot0, sub_zero] using hbound p θ)
    (hqi.const_mul D) hdiff).2
  have hd0 : HasDerivAt (fun θ => ∫ p, H (ContinuousLinearMap.rotation θ p) ∂ν) 0 0 := by
    simpa only [hinv] using (hasDerivAt_const 0 (∫ p, H p ∂ν))
  have heq := hd.unique hd0
  simp only [Pi.add_apply] at heq
  rw [integral_add hUi hVi] at heq
  have hprod : (∫ p, V p ∂ν) = -(∫ p, U p ∂ν) := by linarith
  rw [integral_prod _ hVi, integral_prod _ hUi] at hprod
  simpa only [V, U, z, v, γ, mul_assoc, integral_const_mul] using hprod

private theorem mehler_log_data {n : ℕ} {f : Vector n → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B)
    {t : ℝ} (ht : 0 < t) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => 1 + Real.log (mehlerExponential f t x)) ∧
      (∃ C : ℝ, ∀ x, |1 + Real.log (mehlerExponential f t x)| ≤ C) ∧
      ∀ x, HasFDerivAt (fun x => 1 + Real.log (mehlerExponential f t x))
        ((mehlerExponential f t x)⁻¹ • fderiv ℝ (mehlerExponential f t) x) x := by
  obtain ⟨B, hB⟩ := hb
  have hu (x : Vector n) := mehler_fderiv_commutation hf ⟨B, hB⟩ ht x
  have hp (x : Vector n) := mehler_pos hf.continuous hB t x
  have hAd (x : Vector n) :
      HasFDerivAt (fun x => 1 + Real.log (mehlerExponential f t x))
        ((mehlerExponential f t x)⁻¹ • fderiv ℝ (mehlerExponential f t) x) x :=
    (hu x).differentiableAt.hasFDerivAt.log (hp x).ne' |>.const_add 1
  have hnorm (x : Vector n) :
      ‖fderiv ℝ (mehlerExponential f t) x‖ ≤ Real.exp (-t) * (Real.exp B * K) := by
    rw [(hu x).fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have hh := norm_integral_le_of_norm_le_const (μ := stdGaussian (Vector n))
      (Eventually.of_forall fun y => show
        ‖Real.exp (f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)) •
          fderiv ℝ f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)‖ ≤
            Real.exp B * K from by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul (Real.exp_le_exp.mpr ((le_abs_self _).trans (hB _)))
          (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _) (Real.exp_pos _).le)
    simpa only [probReal_univ, mul_one] using hh
  have hinv (x : Vector n) : (mehlerExponential f t x)⁻¹ ≤ Real.exp B := by
    simpa only [one_div, Real.exp_neg, inv_inv] using
      one_div_le_one_div_of_le (Real.exp_pos (-B)) (mehler_bounds hf.continuous hB t x).1
  let L : ℝ≥0 := ⟨Real.exp B * (Real.exp (-t) * (Real.exp B * K)), by positivity⟩
  refine ⟨L, lipschitzWith_of_nnnorm_fderiv_le (fun x => (hAd x).differentiableAt) ?_,
    ⟨1 + B, ?_⟩, hAd⟩
  · intro x
    change ‖fderiv ℝ (fun x => 1 + Real.log (mehlerExponential f t x)) x‖ ≤
      Real.exp B * (Real.exp (-t) * (Real.exp B * K))
    rw [(hAd x).fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hp x))]
    exact mul_le_mul (hinv x) (hnorm x) (norm_nonneg _) (Real.exp_pos _).le
  · intro x
    calc
      _ ≤ |(1 : ℝ)| + |Real.log (mehlerExponential f t x)| := abs_add_le _ _
      _ ≤ 1 + B := by
        rw [abs_one]
        linarith only [mehler_log_bound hf.continuous hB t x]

private theorem mehler_velocity_rotation_form {n : ℕ} (f : Vector n → ℝ)
    {t : ℝ} (ht : 0 < t) (x : Vector n) :
    mehlerVelocity f t x =
      (Real.exp (-t) / Real.sqrt (1 - Real.exp (-t) ^ 2)) *
        ∫ y, Real.exp (f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)) *
          fderiv ℝ f (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-t) ^ 2) • y)
            (Real.exp (-t) • y - Real.sqrt (1 - Real.exp (-t) ^ 2) • x)
          ∂stdGaussian (Vector n) := by
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-t) ^ 2)
  have hb : b ≠ 0 := (Real.sqrt_pos.mpr (mehler_noise_pos ht)).ne'
  have hv (y : Vector n) : -a • x + (a ^ 2 / b) • y = (a / b) • (a • y - b • x) := by
    rw [smul_sub, smul_smul, smul_smul, div_mul_cancel₀ a hb,
      show a / b * a = a ^ 2 / b by ring]
    module
  change (∫ y, Real.exp (f (a • x + b • y)) *
      fderiv ℝ f (a • x + b • y) (-a • x + (a ^ 2 / b) • y)
      ∂stdGaussian (Vector n)) = (a / b) *
        ∫ y, Real.exp (f (a • x + b • y)) *
          fderiv ℝ f (a • x + b • y) (a • y - b • x) ∂stdGaussian (Vector n)
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [hv, map_smul]
    simp only [smul_eq_mul]
    ring

private theorem mehler_entropy_coefficient_eq_neg_fisher {n : ℕ}
    {f : Vector n → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hb : ∃ B : ℝ, ∀ x, |f x| ≤ B) {t : ℝ} (ht : 0 < t) :
    (∫ x, (1 + Real.log (mehlerExponential f t x)) * mehlerVelocity f t x
      ∂stdGaussian (Vector n)) = -mehlerFisher f t := by
  obtain ⟨L, hL, hLb, hLd⟩ := mehler_log_data hf hb ht
  have hrot := gaussian_rotation_ibp hf hb hL hLb (fun x => (hLd x).differentiableAt)
    (Real.exp (-t)) (Real.sqrt (1 - Real.exp (-t) ^ 2)) (mehler_coefficients ht.le)
  simp_rw [show ∀ x, fderiv ℝ (fun x => 1 + Real.log (mehlerExponential f t x)) x =
    (mehlerExponential f t x)⁻¹ • fderiv ℝ (mehlerExponential f t) x from fun x => (hLd x).fderiv] at hrot
  simp_rw [mehler_score_pairing hf hb ht] at hrot
  rw [integral_const_mul] at hrot
  let a := Real.exp (-t)
  let b := Real.sqrt (1 - Real.exp (-t) ^ 2)
  have ha : a ≠ 0 := (Real.exp_pos (-t)).ne'
  have hb0 : b ≠ 0 := (Real.sqrt_pos.mpr (mehler_noise_pos ht)).ne'
  calc
    _ = (a / b) * (∫ x, (1 + Real.log (mehlerExponential f t x)) *
        (∫ y, Real.exp (f (a • x + b • y)) *
          fderiv ℝ f (a • x + b • y) (a • y - b • x) ∂stdGaussian (Vector n))
        ∂stdGaussian (Vector n)) := by
      simp_rw [mehler_velocity_rotation_form f ht]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp [a, b]; ring
    _ = (a / b) * (-(b / a) * mehlerFisher f t) := by
      rw [hrot]
      simp only [a, b, mehlerFisher, neg_mul]
    _ = -mehlerFisher f t := by field_simp [ha, hb0]

/-- The exact bounded Lipschitz de Bruijn identity, including all dimensions. -/
private theorem mehler_entropy_dissipation : MehlerEntropyDissipation := by
  intro n f K hf hb t ht
  rw [← mehler_entropy_coefficient_eq_neg_fisher hf hb ht]
  exact mehler_entropy_hasDerivAt hf hb ht

namespace Endpoints

open SourceSphereSharpConcentration

/-- The original de Bruijn interface, with all analytic hypotheses discharged. -/
theorem mehlerEntropyDissipation_reduced3 : MehlerEntropyDissipation := mehler_entropy_dissipation

/-- Gross's exact bounded Lipschitz interface, with no analytic hypothesis. -/
theorem bounded_lipschitz_gaussian_logSobolev_reduced3 : BoundedLipschitzGaussianLogSobolev :=
  bounded_lipschitz_gaussian_logSobolev_reduced2
    mehlerEntropyDissipation_reduced3

/-- The exact sphere interface, with no logarithmic Sobolev hypothesis. -/
theorem bakryEmerySphereLogSobolev_reduced3 : BakryEmerySphereLogSobolev :=
  bakryEmerySphereLogSobolev_reduced2 mehlerEntropyDissipation_reduced3

/-- `lem:ent-lsi`, with the Gaussian and sphere interfaces discharged. -/
theorem geodesic_lipschitz_centered_mgf_reduced3
    {m : ℕ} (hm : 2 ≤ m)
    (g : Vector (m+1) → ℝ) {L : ℝ} (hL : 0 ≤ L) (hg : GeodesicLipschitz g L)
    (t : ℝ) :
    (∫ x, Real.exp (t * (g x - ∫ y, g y ∂unitSphereLaw (m+1)))
      ∂unitSphereLaw (m+1)) ≤ Real.exp (L ^ 2 * t ^ 2 / (2 * ((m : ℝ) - 1))) :=
  geodesic_lipschitz_centered_mgf bakryEmerySphereLogSobolev_reduced3 hm g hL hg t

open SphericalGaussianJet EntranceLatitudeTangentObservable

/-- The sharp latitude MGF, with no logarithmic Sobolev hypothesis. -/
theorem observable_centered_mgf_le_sharp_reduced3
    {n P : ℕ} (hn : 3 ≤ n)
    (c : Degree P → ℝ) (J : Disorder (n+1) P) (hJ : J ∈ regularDisorder)
    (x : Vector (n+1)) (hx : ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y, inner ℝ (e y) x = 0)
    {r : ℝ} (hr : |r| ≤ 1) (t : ℝ) :
    mgf (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (latitudeLaw x e r) t ≤
      Real.exp (9 * (derivativeConstant c) ^ 2 * ((n+1 : ℕ) : ℝ) * t ^ 2 /
        (2 * ((n : ℝ) - 2))) :=
  observable_centered_mgf_le_sharp bakryEmerySphereLogSobolev_reduced3
    hn c J hJ x hx e he hr t

/-- The genuine sub-Gaussian predicate, with no logarithmic Sobolev hypothesis. -/
theorem observable_hasSubgaussianMGF_reduced3
    {n P : ℕ} (hn : 5 ≤ n) (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (hJ : J ∈ regularDisorder) (x : Vector (n+1))
    (hx : ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ y, inner ℝ (e y) x = 0)
    {r : ℝ} (hr : |r| ≤ 1) :
    HasSubgaussianMGF
      (fun u => observable c J x u - ∫ v, observable c J x v ∂latitudeLaw x e r)
      (18 * (derivativeConstant c) ^ 2).toNNReal (latitudeLaw x e r) :=
  observable_hasSubgaussianMGF bakryEmerySphereLogSobolev_reduced3
    hn c J hJ x hx e he hr

/-- Both clauses of `lem:ent-latitude` on the original Gaussian-bank event. -/
theorem center_latitude_mean_and_mgf_reduced3
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈ originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) :=
  center_latitude_mean_and_mgf bakryEmerySphereLogSobolev_reduced3 μ hQ

/-- Both latitude clauses on the constant-completed entrance event. -/
theorem constant_completed_center_latitude_mean_and_mgf_reduced3
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
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
    bakryEmerySphereLogSobolev_reduced3 μ hQ

/-- The full-event `lem:ent-latitude`, with no logarithmic Sobolev hypothesis. -/
theorem full_center_latitude_mean_and_mgf_reduced3
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
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
    bakryEmerySphereLogSobolev_reduced3 μ hQ

end Endpoints

end SlowEquilibration.SourceGaussianDeBruijn
