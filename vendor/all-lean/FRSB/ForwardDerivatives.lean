module
public import FRSB.ForwardHeat
public import Paper.GaussianDifferentiation

@[expose] public section

/-! Differentiating the actual tilted Gaussian heat step. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace FRSB

/-- Actual Gaussian tilt in the forward heat step. -/
def forwardTiltExpectation (r t : ℝ) (w f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Paper.gaussianExpectation (fun z => f (r / t * x + Real.sqrt (r * (t - r) / t) * z) *
      Real.exp (-w (r / t * x + Real.sqrt (r * (t - r) / t) * z))) /
    Paper.gaussianExpectation (fun z => Real.exp (-w (r / t * x + Real.sqrt (r * (t - r) / t) * z)))

lemma integrable_gaussian_bounded (f : ℝ → ℝ) (hf : Continuous f) (C : ℝ)
    (hb : ∀ z, ‖f z‖ ≤ C) : Integrable f (gaussianReal 0 1) :=
  (integrable_const C).mono' hf.aestronglyMeasurable (.of_forall hb)

lemma norm_exp_neg_le_one (w : ℝ → ℝ) (hw : ∀ x, 0 ≤ w x) (x : ℝ) :
    ‖Real.exp (-w x)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hw x))

lemma integrable_forward_weighted (r t x : ℝ) (w f : ℝ → ℝ)
    (hw : Continuous w) (hnon : ∀ y, 0 ≤ w y) (hf : Continuous f)
    (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) :
    Integrable (fun z => f (r / t * x + Real.sqrt (r * (t - r) / t) * z) *
      Real.exp (-w (r / t * x + Real.sqrt (r * (t - r) / t) * z))) (gaussianReal 0 1) := by
  apply integrable_gaussian_bounded _ (by fun_prop) M
  intro z
  rw [norm_mul]
  exact (mul_le_mul (hb _) (norm_exp_neg_le_one w hnon _) (norm_nonneg _) ((norm_nonneg (f 0)).trans (hb 0))).trans_eq (mul_one _)

/-- The first derivative in the paper's heat-step formula, with derivative
exchange justified by actual Gaussian domination. -/
theorem hasDerivAt_forwardHeatCorrection (r t x : ℝ) (w dw : ℝ → ℝ)
    (hw : Continuous w) (hdw : Continuous dw) (hnon : ∀ y, 0 ≤ w y)
    (hder : ∀ y, HasDerivAt w (dw y) y) (M : ℝ) (hb : ∀ y, ‖dw y‖ ≤ M) :
    HasDerivAt (forwardHeatCorrection r t w)
      (r / t * forwardTiltExpectation r t w dw x) x := by
  let θ := r / t
  let b := Real.sqrt (r * (t - r) / t)
  let F := fun y => Real.exp (-w y)
  let dF := fun y => -dw y * Real.exp (-w y)
  have hdF (y : ℝ) : HasDerivAt F (dF y) y := by
    simpa only [F, dF, Pi.neg_apply, mul_comm] using (hder y).neg.exp
  have hbF (y : ℝ) : ‖dF y‖ ≤ M := by
    dsimp only [dF]
    rw [norm_mul, norm_neg]
    exact (mul_le_mul (hb y) (norm_exp_neg_le_one w hnon y)
      (norm_nonneg _) ((norm_nonneg (dw 0)).trans (hb 0))).trans_eq (mul_one _)
  have hiF : Integrable (fun z => F (θ * x + b * z)) (gaussianReal 0 1) :=
    forwardHeat_average_integrable r t x w hw hnon
  have hh := Paper.hasDerivAt_gaussian_shift F dF b (θ * x) M
    (by fun_prop) (by fun_prop) hiF hdF hbF
  have hcomp := hh.comp x ((hasDerivAt_id x).const_mul θ)
  have hp := forwardHeat_average_pos r t x w hw hnon
  have hout := hcomp.log (ne_of_gt hp) |>.neg
  have he : Paper.gaussianExpectation (fun z => dF (θ * x + b * z)) =
      -Paper.gaussianExpectation (fun z => dw (θ * x + b * z) * F (θ * x + b * z)) := by
    unfold Paper.gaussianExpectation
    rw [← integral_neg]
    congr 1
    ext z
    dsimp only [dF, F]
    ring
  rw [he] at hout
  convert hout using 1
  · rfl
  · dsimp only [forwardTiltExpectation, θ, b, F, Function.comp_def]
    ring

/-- A Gaussian tilt preserves every uniform bound of its observable. -/
theorem norm_forwardTiltExpectation_le (r t x : ℝ) (w f : ℝ → ℝ)
    (hw : Continuous w) (hnon : ∀ y, 0 ≤ w y) (hf : Continuous f)
    (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) : ‖forwardTiltExpectation r t w f x‖ ≤ M := by
  let Y := fun z => r / t * x + Real.sqrt (r * (t - r) / t) * z
  let F := fun z => Real.exp (-w (Y z))
  have hiF : Integrable F (gaussianReal 0 1) := forwardHeat_average_integrable r t x w hw hnon
  have hiN : Integrable (fun z => f (Y z) * F z) (gaussianReal 0 1) :=
    integrable_forward_weighted r t x w f hw hnon hf M hb
  have hp : 0 < ∫ z, F z ∂gaussianReal 0 1 := forwardHeat_average_pos r t x w hw hnon
  have hh : ‖∫ z, f (Y z) * F z ∂gaussianReal 0 1‖ ≤ M * ∫ z, F z ∂gaussianReal 0 1 := by
    calc
      _ ≤ ∫ z, ‖f (Y z) * F z‖ ∂gaussianReal 0 1 := norm_integral_le_integral_norm _
      _ ≤ ∫ z, M * F z ∂gaussianReal 0 1 := integral_mono hiN.norm (hiF.const_mul M) (fun z => by
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact mul_le_mul_of_nonneg_right (hb _) (Real.exp_pos _).le)
      _ = _ := integral_const_mul _ _
  dsimp only [forwardTiltExpectation, Paper.gaussianExpectation]
  rw [norm_div, Real.norm_of_nonneg hp.le]
  exact (div_le_iff₀ hp).mpr hh

/-- The tilted variance is nonnegative, proved by integrating its centered square. -/
theorem forwardTilt_variance_nonneg (r t x : ℝ) (w f : ℝ → ℝ)
    (hw : Continuous w) (hnon : ∀ y, 0 ≤ w y) (hf : Continuous f)
    (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) :
    0 ≤ forwardTiltExpectation r t w (fun y => f y ^ 2) x - forwardTiltExpectation r t w f x ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hb 0)
  let Y := fun z => r / t * x + Real.sqrt (r * (t - r) / t) * z
  let F := fun z => Real.exp (-w (Y z))
  let A := ∫ z, F z ∂gaussianReal 0 1
  let N := ∫ z, f (Y z) * F z ∂gaussianReal 0 1
  let Q := ∫ z, f (Y z) ^ 2 * F z ∂gaussianReal 0 1
  let m := N / A
  have hiF : Integrable F (gaussianReal 0 1) := forwardHeat_average_integrable r t x w hw hnon
  have hiN : Integrable (fun z => f (Y z) * F z) (gaussianReal 0 1) :=
    integrable_forward_weighted r t x w f hw hnon hf M hb
  have hiQ : Integrable (fun z => f (Y z) ^ 2 * F z) (gaussianReal 0 1) :=
    integrable_forward_weighted r t x w (fun y => f y ^ 2) hw hnon (hf.pow 2) (M ^ 2) (fun y => by
      rw [norm_pow]
      gcongr
      exact hb y)
  have he : (∫ z, (f (Y z) - m) ^ 2 * F z ∂gaussianReal 0 1) = Q - 2 * m * N + m ^ 2 * A := by
    have hfne : (fun z => (f (Y z) - m) ^ 2 * F z) =
        (fun z => f (Y z) ^ 2 * F z - (2 * m) * (f (Y z) * F z) + m ^ 2 * F z) := by
      funext z
      ring
    have hadd := integral_add (hiQ.sub (hiN.const_mul (2 * m))) (hiF.const_mul (m ^ 2))
    have hsub := integral_sub hiQ (hiN.const_mul (2 * m))
    simp only [Pi.sub_apply, Pi.add_apply] at hadd hsub
    rw [hfne, hadd, hsub, integral_const_mul, integral_const_mul]
  have hh : 0 ≤ Q - 2 * m * N + m ^ 2 * A := by
    rw [← he]
    exact integral_nonneg (fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hp : 0 < A := forwardHeat_average_pos r t x w hw hnon
  have hma : m * A = N := div_mul_cancel₀ _ hp.ne'
  have hh' : 0 ≤ Q / A - m ^ 2 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hp).mpr
    have heq : m * N = m ^ 2 * A := by rw [← hma]; ring
    nlinarith [heq]
  exact hh'

/-- The slope bound does not increase during a genuine forward heat step. -/
theorem forwardHeatCorrection_slope_bound {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (x : ℝ) (w dw : ℝ → ℝ) (hw : Continuous w) (hdw : Continuous dw)
    (hnon : ∀ y, 0 ≤ w y) (hder : ∀ y, HasDerivAt w (dw y) y)
    (M : ℝ) (hb : ∀ y, ‖dw y‖ ≤ M) :
    ‖deriv (forwardHeatCorrection r t w) x‖ ≤ M := by
  rw [(hasDerivAt_forwardHeatCorrection r t x w dw hw hdw hnon hder M hb).deriv, norm_mul]
  have hθ0 : 0 ≤ r / t := div_nonneg hr.le (hr.trans hrt).le
  have hθ1 : r / t ≤ 1 := (div_le_one (hr.trans hrt)).mpr hrt.le
  rw [Real.norm_of_nonneg hθ0]
  exact (mul_le_mul hθ1 (norm_forwardTiltExpectation_le r t x w dw hw hnon hdw M hb)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Gaussian differentiation of any bounded smooth observable with the
actual forward weight. -/
theorem hasDerivAt_forwardWeightedAverage (r t x : ℝ) (w dw f df : ℝ → ℝ)
    (hw : Continuous w) (hdw : Continuous dw) (hf : Continuous f) (hdf : Continuous df)
    (hnon : ∀ y, 0 ≤ w y) (hderw : ∀ y, HasDerivAt w (dw y) y)
    (hderf : ∀ y, HasDerivAt f (df y) y)
    (Mw Mf Md : ℝ) (hbw : ∀ y, ‖dw y‖ ≤ Mw) (hbf : ∀ y, ‖f y‖ ≤ Mf)
    (hbd : ∀ y, ‖df y‖ ≤ Md) :
    HasDerivAt (fun y => Paper.gaussianExpectation (fun z =>
      f (r / t * y + Real.sqrt (r * (t - r) / t) * z) *
        Real.exp (-w (r / t * y + Real.sqrt (r * (t - r) / t) * z))))
      (r / t * Paper.gaussianExpectation (fun z =>
        (df (r / t * x + Real.sqrt (r * (t - r) / t) * z) -
          f (r / t * x + Real.sqrt (r * (t - r) / t) * z) *
            dw (r / t * x + Real.sqrt (r * (t - r) / t) * z)) *
          Real.exp (-w (r / t * x + Real.sqrt (r * (t - r) / t) * z)))) x := by
  let θ := r / t
  let b := Real.sqrt (r * (t - r) / t)
  let G := fun y => f y * Real.exp (-w y)
  let dG := fun y => (df y - f y * dw y) * Real.exp (-w y)
  have hMw : 0 ≤ Mw := (norm_nonneg (dw 0)).trans (hbw 0)
  have hMf : 0 ≤ Mf := (norm_nonneg (f 0)).trans (hbf 0)
  have hMd : 0 ≤ Md := (norm_nonneg (df 0)).trans (hbd 0)
  have hdG (y : ℝ) : HasDerivAt G (dG y) y := by
    convert (hderf y).mul (hderw y).neg.exp using 1
    dsimp only [dG, Pi.neg_apply]
    ring
  have hbG (y : ℝ) : ‖dG y‖ ≤ Md + Mf * Mw := by
    dsimp only [dG]
    rw [norm_mul]
    have hh : ‖df y - f y * dw y‖ ≤ Md + Mf * Mw := by
      apply (norm_sub_le _ _).trans
      rw [norm_mul]
      gcongr
      · exact hbd y
      · exact hbf y
      · exact hbw y
    exact (mul_le_mul hh (norm_exp_neg_le_one w hnon y) (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
  have hiG : Integrable (fun z => G (θ * x + b * z)) (gaussianReal 0 1) :=
    integrable_forward_weighted r t x w f hw hnon hf Mf hbf
  have hh := Paper.hasDerivAt_gaussian_shift G dG b (θ * x) (Md + Mf * Mw)
    (by fun_prop) (by fun_prop) hiG hdG hbG
  have hout := hh.comp x ((hasDerivAt_id x).const_mul θ)
  convert hout using 1
  · rfl
  · dsimp only [θ, b, dG]
    ring

set_option maxHeartbeats 1000000 in
/-- The exact second-derivative formula for the heat-step potential. -/
theorem hasDerivAt_deriv_forwardHeatCorrection (r t x : ℝ) (w dw ddw : ℝ → ℝ)
    (hw : Continuous w) (hdw : Continuous dw) (hddw : Continuous ddw)
    (hnon : ∀ y, 0 ≤ w y) (hderw : ∀ y, HasDerivAt w (dw y) y)
    (hderdw : ∀ y, HasDerivAt dw (ddw y) y)
    (M K : ℝ) (hbw : ∀ y, ‖dw y‖ ≤ M) (hbddw : ∀ y, ‖ddw y‖ ≤ K) :
    HasDerivAt (deriv (forwardHeatCorrection r t w))
      ((r / t) ^ 2 * (forwardTiltExpectation r t w ddw x -
        (forwardTiltExpectation r t w (fun y => dw y ^ 2) x - forwardTiltExpectation r t w dw x ^ 2))) x := by
  let θ := r / t
  let Y := fun y z => θ * y + Real.sqrt (r * (t - r) / t) * z
  let A := fun y => Paper.gaussianExpectation (fun z => Real.exp (-w (Y y z)))
  let N := fun y => Paper.gaussianExpectation (fun z => dw (Y y z) * Real.exp (-w (Y y z)))
  let Q := Paper.gaussianExpectation (fun z => dw (Y x z) ^ 2 * Real.exp (-w (Y x z)))
  let S := Paper.gaussianExpectation (fun z => ddw (Y x z) * Real.exp (-w (Y x z)))
  have hp : 0 < A x := forwardHeat_average_pos r t x w hw hnon
  have hN := hasDerivAt_forwardWeightedAverage r t x w dw dw ddw hw hdw hdw hddw hnon hderw hderdw M M K hbw hbw hbddw
  have heN : Paper.gaussianExpectation (fun z => (ddw (Y x z) - dw (Y x z) * dw (Y x z)) * Real.exp (-w (Y x z))) = S - Q := by
    have hiS := integrable_forward_weighted r t x w ddw hw hnon hddw K hbddw
    have hiQ := integrable_forward_weighted r t x w (fun y => dw y ^ 2) hw hnon (hdw.pow 2) (M ^ 2)
      (fun y => by rw [norm_pow]; gcongr; exact hbw y)
    unfold Paper.gaussianExpectation
    dsimp only [S, Q, Paper.gaussianExpectation]
    have he : (fun z => (ddw (Y x z) - dw (Y x z) * dw (Y x z)) * Real.exp (-w (Y x z))) =
        (fun z => ddw (Y x z) * Real.exp (-w (Y x z)) - dw (Y x z) ^ 2 * Real.exp (-w (Y x z))) := by
      funext z
      ring
    have hh := integral_sub hiS hiQ
    try simp only [Pi.sub_apply] at hh
    rw [he]
    exact hh
  change HasDerivAt N (θ * _) x at hN
  rw [heN] at hN
  have hA := hasDerivAt_forwardWeightedAverage r t x w dw (fun _ => 1) (fun _ => 0)
    hw hdw continuous_const continuous_const hnon hderw (fun y => hasDerivAt_const y 1)
    M 1 0 hbw (fun y => by norm_num) (fun y => by norm_num)
  simp only [one_mul, zero_sub, neg_mul] at hA
  have heA : Paper.gaussianExpectation (fun z => -(dw (Y x z) * Real.exp (-w (Y x z)))) = -N x := by
    exact integral_neg _
  change HasDerivAt A (θ * _) x at hA
  rw [heA] at hA
  have hout := (hN.div hA hp.ne').const_mul θ
  have heFirst : deriv (forwardHeatCorrection r t w) = fun y => θ * (N y / A y) := by
    funext y
    exact (hasDerivAt_forwardHeatCorrection r t y w dw hw hdw hnon hderw M hbw).deriv
  rw [heFirst]
  convert hout using 1
  dsimp only [forwardTiltExpectation, θ, S, Q, N, A, Y]
  field_simp
  ring

lemma forwardTiltExpectation_le (r t x : ℝ) (w f : ℝ → ℝ)
    (hw : Continuous w) (hnon : ∀ y, 0 ≤ w y) (hf : Continuous f)
    (M : ℝ) (hb : ∀ y, ‖f y‖ ≤ M) (C : ℝ) (hupper : ∀ y, f y ≤ C) :
    forwardTiltExpectation r t w f x ≤ C := by
  have hp := forwardHeat_average_pos r t x w hw hnon
  apply (div_le_iff₀ hp).mpr
  have hh := integral_mono (integrable_forward_weighted r t x w f hw hnon hf M hb)
    ((forwardHeat_average_integrable r t x w hw hnon).const_mul C)
    (fun z => mul_le_mul_of_nonneg_right (hupper _) (Real.exp_pos _).le)
  simpa only [Paper.gaussianExpectation, integral_const_mul] using hh

/-- The upper curvature bound does not increase during the actual heat step. -/
theorem forwardHeatCorrection_curvature_bound {r t : ℝ} (hr : 0 < r) (hrt : r < t)
    (x : ℝ) (w dw ddw : ℝ → ℝ) (hw : Continuous w) (hdw : Continuous dw) (hddw : Continuous ddw)
    (hnon : ∀ y, 0 ≤ w y) (hderw : ∀ y, HasDerivAt w (dw y) y)
    (hderdw : ∀ y, HasDerivAt dw (ddw y) y)
    (M K C : ℝ) (hbw : ∀ y, ‖dw y‖ ≤ M) (hbddw : ∀ y, ‖ddw y‖ ≤ K)
    (hC : 0 ≤ C) (hupper : ∀ y, ddw y ≤ C) :
    deriv (deriv (forwardHeatCorrection r t w)) x ≤ C := by
  rw [(hasDerivAt_deriv_forwardHeatCorrection r t x w dw ddw hw hdw hddw hnon hderw hderdw M K hbw hbddw).deriv]
  have hv := forwardTilt_variance_nonneg r t x w dw hw hnon hdw M hbw
  have hu := forwardTiltExpectation_le r t x w ddw hw hnon hddw K hbddw C hupper
  have hθ0 : 0 ≤ r / t := div_nonneg hr.le (hr.trans hrt).le
  have hθ1 : r / t ≤ 1 := (div_le_one (hr.trans hrt)).mpr hrt.le
  have hθsq : (r / t) ^ 2 ≤ 1 := by nlinarith
  calc
    _ ≤ (r / t) ^ 2 * C := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ ≤ 1 * C := mul_le_mul_of_nonneg_right hθsq hC
    _ = C := one_mul _

end FRSB
