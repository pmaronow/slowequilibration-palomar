-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalConcentration
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-! Ordinary integral partition functions for bounded measurable families of
linear fields. The spin measure may be nonatomic, including the genuine
uniform sphere law. Differentiation is proved by dominated convergence. -/

namespace SlowEquilibration.GaussianSpinInterpolation

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

variable {V H : Type*} [MeasurableSpace V]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  [FiniteDimensional ℝ H]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

def weight (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (w : H) (v : V) : ℝ :=
  ρ v * Real.exp (L v w)

def weightDerivative (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (w : H) (v : V) : H →L[ℝ] ℝ :=
  weight ρ L w v • L v

def moment (ν : Measure V) (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (w : H) : ℝ :=
  ∫ v, weight ρ L w v ∂ν

def momentDerivative (ν : Measure V) (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ)
    (w : H) : H →L[ℝ] ℝ := ∫ v, weightDerivative ρ L w v ∂ν

theorem weight_measurable (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) (w : H) : Measurable (weight ρ L w) :=
  hρ.mul (((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL).exp)

theorem weightDerivative_measurable (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) (w : H) :
    Measurable (weightDerivative ρ L w) := (weight_measurable ρ L hρ hL w).smul hL

theorem weight_bound (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ)
    {C K : ℝ} {v : V} (hρ : |ρ v| ≤ C) (hL : ‖L v‖ ≤ K) (w : H) :
    ‖weight ρ L w v‖ ≤ C * Real.exp (K * ‖w‖) := by
  have hC : 0 ≤ C := (abs_nonneg _).trans hρ
  have hexp : Real.exp (L v w) ≤ Real.exp (K * ‖w‖) :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans ((L v).le_opNorm w |>.trans
      (mul_le_mul_of_nonneg_right hL (norm_nonneg _))))
  rw [weight, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact mul_le_mul hρ hexp (Real.exp_pos _).le hC

theorem weightDerivative_bound (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ)
    {C K : ℝ} {v : V} (hρ : |ρ v| ≤ C) (hL : ‖L v‖ ≤ K) (w : H) :
    ‖weightDerivative ρ L w v‖ ≤ C * Real.exp (K * ‖w‖) * K := by
  rw [weightDerivative, norm_smul]
  exact mul_le_mul (weight_bound ρ L hρ hL w) hL (norm_nonneg _)
    (mul_nonneg ((abs_nonneg _).trans hρ) (Real.exp_pos _).le)

theorem weight_integrable (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    Integrable (weight ρ L w) ν :=
  Integrable.of_bound (weight_measurable ρ L hρ hL w).aestronglyMeasurable _
    (hb.mono (fun _ hv => weight_bound ρ L hv.1 hv.2 w))

theorem weightDerivative_integrable (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    Integrable (weightDerivative ρ L w) ν :=
  Integrable.of_bound (weightDerivative_measurable ρ L hρ hL w).aestronglyMeasurable _
    (hb.mono (fun _ hv => weightDerivative_bound ρ L hv.1 hv.2 w))

theorem weight_hasFDerivAt (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (v : V) (w : H) :
    HasFDerivAt (fun y => weight ρ L y v) (weightDerivative ρ L w v) w := by
  simpa only [weightDerivative, weight, smul_smul] using
    (L v).hasFDerivAt.exp.const_mul (ρ v)

theorem norm_le_of_mem_ball {w y : H} (hy : y ∈ Metric.ball w 1) :
    ‖y‖ ≤ ‖w‖ + 1 := by
  have hd : ‖y-w‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have ht := norm_add_le (y-w) w
  rw [sub_add_cancel] at ht
  linarith

theorem moment_hasFDerivAt (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    HasFDerivAt (moment ν ρ L) (momentDerivative ν ρ L w) w := by
  let B := C * Real.exp (K * (‖w‖+1)) * K
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (E := ℝ) (s := Metric.ball w 1)
    (F := fun y v => weight ρ L y v) (F' := fun y v => weightDerivative ρ L y v)
    (bound := fun _ => B) (Metric.ball_mem_nhds w zero_lt_one)
  · exact .of_forall fun y => (weight_integrable ν ρ L hρ hL hb y).aestronglyMeasurable
  · exact weight_integrable ν ρ L hρ hL hb w
  · exact (weightDerivative_measurable ρ L hρ hL w).aestronglyMeasurable
  · filter_upwards [hb] with v hv y hy
    exact (weightDerivative_bound ρ L hv.1 hv.2 y).trans (by
      dsimp [B]
      gcongr
      exact norm_le_of_mem_ball hy)
  · exact integrable_const B
  · exact .of_forall fun v y _ => weight_hasFDerivAt ρ L v y

theorem momentDerivative_continuous (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) :
    Continuous (momentDerivative ν ρ L) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  let B := C * Real.exp (K * (‖w‖+1)) * K
  apply continuousAt_of_dominated (bound := fun _ => B)
  · exact .of_forall fun y => (weightDerivative_measurable ρ L hρ hL y).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds w zero_lt_one] with y hy
    filter_upwards [hb] with v hv
    exact (weightDerivative_bound ρ L hv.1 hv.2 y).trans (by
      dsimp [B]
      gcongr
      exact norm_le_of_mem_ball hy)
  · exact integrable_const B
  · exact .of_forall fun v => by
      change ContinuousAt (fun y => (ρ v * Real.exp (L v y)) • L v) w
      fun_prop

theorem moment_contDiff (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) : ContDiff ℝ 1 (moment ν ρ L) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨_,
    momentDerivative_continuous ν ρ L hρ hL hC hK hb,
    moment_hasFDerivAt ν ρ L hρ hL hC hK hb⟩

/-- The normalized ordinary integral of a spin observable. -/
def expectation (ν : Measure V) (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (w : H) : ℝ :=
  moment ν ρ L w / moment ν (fun _ => 1) L w

def expectationDerivative (ν : Measure V) (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ)
    (w : H) : H →L[ℝ] ℝ :=
  (moment ν (fun _ => 1) L w)⁻¹ •
    (momentDerivative ν ρ L w - expectation ν ρ L w •
      momentDerivative ν (fun _ => 1) L w)

theorem moment_one_pos (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) :
    0 < moment ν (fun _ => 1) L w := by
  have hi := weight_integrable ν (fun _ => 1) L measurable_const hL
    (hb.mono (fun v hv => ⟨by norm_num, hv⟩) : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  change Integrable (fun v => 1 * Real.exp (L v w)) ν at hi
  simpa only [moment, weight, one_mul] using integral_exp_pos
    (by simpa only [one_mul] using hi)

theorem norm_moment_le (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    ‖moment ν ρ L w‖ ≤ C * moment ν (fun _ => 1) L w := by
  have hi := weight_integrable ν ρ L hρ hL hb w
  have h1 := weight_integrable ν (fun _ => 1) L measurable_const hL
    (hb.mono (fun v hv => ⟨by norm_num, hv.2⟩) : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  calc
    _ ≤ ∫ v, ‖weight ρ L w v‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ v, C * weight (fun _ => 1) L w v ∂ν := by
      apply integral_mono_ae hi.norm (h1.const_mul C)
      filter_upwards [hb] with v hv
      simp only [weight, norm_mul, Real.norm_eq_abs,
        Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
      exact mul_le_mul_of_nonneg_right hv.1 (Real.exp_pos _).le
    _ = _ := integral_const_mul C _

theorem norm_momentDerivative_le (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C) (_hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    ‖momentDerivative ν ρ L w‖ ≤ (C*K) * moment ν (fun _ => 1) L w := by
  have hi := weightDerivative_integrable ν ρ L hρ hL hb w
  have h1 := weight_integrable ν (fun _ => 1) L measurable_const hL
    (hb.mono (fun v hv => ⟨by norm_num, hv.2⟩) : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  calc
    _ ≤ ∫ v, ‖weightDerivative ρ L w v‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ v, (C*K) * weight (fun _ => 1) L w v ∂ν := by
      apply integral_mono_ae hi.norm (h1.const_mul (C*K))
      filter_upwards [hb] with v hv
      simp only [weightDerivative, norm_smul, weight, norm_mul,
        Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
      calc
        _ ≤ (C * Real.exp (L v w)) * K := by gcongr; exact hv.1; exact hv.2
        _ = _ := by ring
    _ = _ := integral_const_mul (C*K) _

theorem norm_expectation_le (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    ‖expectation ν ρ L w‖ ≤ C := by
  have hz := moment_one_pos ν L hL (hb.mono (fun _ hv => hv.2)) w
  rw [expectation, norm_div, Real.norm_of_nonneg hz.le]
  exact (div_le_iff₀ hz).mpr (norm_moment_le ν ρ L hρ hL hC hb w)

theorem expectation_hasFDerivAt (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    HasFDerivAt (expectation ν ρ L) (expectationDerivative ν ρ L w) w := by
  have h1 : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K :=
    hb.mono (fun _ hv => ⟨by norm_num, hv.2⟩)
  have hz := moment_one_pos ν L hL (hb.mono (fun _ hv => hv.2)) w
  have hd := moment_hasFDerivAt ν ρ L hρ hL hC hK hb w
  have hd1 := moment_hasFDerivAt ν (fun _ => 1) L measurable_const hL zero_le_one hK h1 w
  have hinv := (hasDerivAt_inv hz.ne').comp_hasFDerivAt w hd1
  convert hd.mul hinv using 1
  · funext y
    simp only [expectation, div_eq_mul_inv, Pi.mul_apply, Function.comp_apply]
  · ext d
    simp only [expectationDerivative, expectation, add_apply,
      sub_apply, smul_apply, smul_eq_mul, Function.comp_apply]
    field_simp
    ring

theorem expectation_contDiff (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) :
    ContDiff ℝ 1 (expectation ν ρ L) := by
  apply (moment_contDiff ν ρ L hρ hL hC hK hb).div
    (moment_contDiff ν (fun _ => 1) L measurable_const hL zero_le_one hK
      (hb.mono (fun _ hv => ⟨by norm_num, hv.2⟩)))
  intro w
  exact (moment_one_pos ν L hL (hb.mono (fun _ hv => hv.2)) w).ne'

theorem norm_expectationDerivative_le (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    ‖expectationDerivative ν ρ L w‖ ≤ 2*C*K := by
  have hz := moment_one_pos ν L hL (hb.mono (fun _ hv => hv.2)) w
  have h1 : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K :=
    hb.mono (fun _ hv => ⟨by norm_num, hv.2⟩)
  have he := norm_expectation_le ν ρ L hρ hL hC hb w
  have hd := norm_momentDerivative_le ν ρ L hρ hL hC hK hb w
  have hd1 := norm_momentDerivative_le ν (fun _ => 1) L measurable_const hL zero_le_one hK h1 w
  unfold expectationDerivative
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz]
  calc
    _ ≤ (moment ν (fun _ => 1) L w)⁻¹ *
        (‖momentDerivative ν ρ L w‖ + ‖expectation ν ρ L w • momentDerivative ν (fun _ => 1) L w‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hz.le)
    _ ≤ (moment ν (fun _ => 1) L w)⁻¹ *
        ((C*K)*moment ν (fun _ => 1) L w + C*(K*moment ν (fun _ => 1) L w)) := by
      rw [norm_smul]
      gcongr
      simpa only [one_mul] using hd1
    _ = _ := by field_simp; ring

theorem momentDerivative_apply (ν : Measure V) [IsFiniteMeasure ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w d : H) :
    momentDerivative ν ρ L w d = moment ν (fun v => ρ v * L v d) L w := by
  rw [momentDerivative, ContinuousLinearMap.integral_apply
    (weightDerivative_integrable ν ρ L hρ hL hb w)]
  apply integral_congr_ae
  exact .of_forall fun v => by
    simp only [weightDerivative, weight, smul_apply, smul_eq_mul]
    ring

/-- The genuine Gibbs covariance derivative, for an arbitrary nonatomic spin
measure and a bounded measurable linear family. -/
theorem expectationDerivative_apply (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w d : H) :
    expectationDerivative ν ρ L w d =
      expectation ν (fun v => ρ v * L v d) L w -
        expectation ν ρ L w * expectation ν (fun v => L v d) L w := by
  have h1 : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K :=
    hb.mono (fun _ hv => ⟨by norm_num, hv.2⟩)
  rw [expectationDerivative, smul_apply, sub_apply, smul_apply,
    momentDerivative_apply ν ρ L hρ hL hb,
    momentDerivative_apply ν (fun _ => 1) L measurable_const hL h1]
  simp only [one_mul, expectation, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Gaussian integration by parts for the literal integral Gibbs expectation.
The value and gradient bounds are derived above, rather than assumed. -/
theorem gaussian_expectation_ibp {ι : Type*} [Fintype ι]
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (ρ : V → ℝ) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hρ : Measurable ρ) (hL : Measurable L) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (d : EuclideanSpace ℝ ι) :
    (∫ w, inner ℝ d w * expectation ν ρ L w
      ∂SYK.standardGaussianMeasureOnEuclidean ι) =
    ∫ w, expectationDerivative ν ρ L w d
      ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  let B := max C (2*C*K)
  have hg := expectation_contDiff ν ρ L hρ hL hC hK hb
  have hd (w : EuclideanSpace ℝ ι) :=
    expectation_hasFDerivAt ν ρ L hρ hL hC hK hb w
  have hgrad (w : EuclideanSpace ℝ ι) :
      ‖gradient (expectation ν ρ L) w‖ ≤ 2*C*K := by
    rw [gradient, (hd w).fderiv, (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.norm_map]
    exact norm_expectationDerivative_le ν ρ L hρ hL hC hK hb w
  have hi := SYK.gaussian_ibp (expectation ν ρ L) d hg B 0
    (fun w => by
      simp only [zero_mul, Real.exp_zero, mul_one]
      exact (norm_expectation_le ν ρ L hρ hL hC hb w).trans (le_max_left _ _))
    (fun w => by
      simp only [zero_mul, Real.exp_zero, mul_one]
      exact (hgrad w).trans (le_max_right _ _))
  rw [hi]
  apply integral_congr_ae
  exact .of_forall fun w => by
    change inner ℝ d (gradient (expectation ν ρ L) w) = expectationDerivative ν ρ L w d
    rw [real_inner_comm, gradient, (hd w).fderiv, InnerProductSpace.toDual_symm_apply]

def logPartition (ν : Measure V) (L : V → H →L[ℝ] ℝ) (w : H) : ℝ :=
  Real.log (moment ν (fun _ => 1) L w)

def score (ν : Measure V) (L : V → H →L[ℝ] ℝ) (w : H) : H →L[ℝ] ℝ :=
  (moment ν (fun _ => 1) L w)⁻¹ • momentDerivative ν (fun _ => 1) L w

theorem logPartition_hasFDerivAt (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) :
    HasFDerivAt (logPartition ν L) (score ν L w) w :=
  (moment_hasFDerivAt ν (fun _ => 1) L measurable_const hL zero_le_one hK
    (hb.mono (fun _ hv => ⟨by norm_num, hv⟩)) w).log (moment_one_pos ν L hL hb w).ne'

theorem logPartition_contDiff (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) : ContDiff ℝ 1 (logPartition ν L) :=
  (moment_contDiff ν (fun _ => 1) L measurable_const hL zero_le_one hK
    (hb.mono (fun _ hv => ⟨by norm_num, hv⟩))).log
    (fun w => (moment_one_pos ν L hL hb w).ne')

theorem score_continuous (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) : Continuous (score ν L) := by
  have hc := (logPartition_contDiff ν L hL hK hb).continuous_fderiv (by norm_num)
  convert hc using 1
  funext w
  exact (logPartition_hasFDerivAt ν L hL hK hb w).fderiv.symm

theorem norm_score_le (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) : ‖score ν L w‖ ≤ K := by
  have hz := moment_one_pos ν L hL hb w
  have hd := norm_momentDerivative_le ν (fun _ => 1) L measurable_const hL zero_le_one hK
    (hb.mono (fun _ hv => ⟨by norm_num, hv⟩)) w
  rw [score, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz]
  calc
    _ ≤ (moment ν (fun _ => 1) L w)⁻¹ * (K*moment ν (fun _ => 1) L w) :=
      mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hd) (inv_nonneg.mpr hz.le)
    _ = _ := by field_simp

theorem abs_logPartition_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) : |logPartition ν L w| ≤ K*‖w‖ := by
  have hi := weight_integrable ν (fun _ => 1) L measurable_const hL
    (hb.mono (fun _ hv => ⟨by norm_num, hv⟩) : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  have hbounds : Real.exp (-K*‖w‖) ≤ moment ν (fun _ => 1) L w ∧
      moment ν (fun _ => 1) L w ≤ Real.exp (K*‖w‖) := by
    constructor
    · have hm := integral_mono_ae (integrable_const (Real.exp (-K*‖w‖))) hi
        (hb.mono (fun v hv => by
          simp only [weight, one_mul]
          apply Real.exp_le_exp.mpr
          have hh := (L v).le_opNorm w
          have hh' := hh.trans (mul_le_mul_of_nonneg_right hv (norm_nonneg w))
          rw [Real.norm_eq_abs] at hh'
          linarith [neg_le_abs (L v w)]))
      simpa only [integral_const, probReal_univ, one_smul, moment] using hm
    · have hm := integral_mono_ae hi (integrable_const (Real.exp (K*‖w‖)))
        (hb.mono (fun v hv => by
          simp only [weight, one_mul]
          apply Real.exp_le_exp.mpr
          have hh := (L v).le_opNorm w
          rw [Real.norm_eq_abs] at hh
          exact (le_abs_self _).trans (hh.trans (mul_le_mul_of_nonneg_right hv (norm_nonneg w)))))
      simpa only [integral_const, probReal_univ, one_smul, moment] using hm
  have hz := moment_one_pos ν L hL hb w
  have hlo := Real.log_le_log (Real.exp_pos _) hbounds.1
  have hhi := Real.log_le_log hz hbounds.2
  rw [Real.log_exp] at hlo hhi
  exact abs_le.mpr ⟨by simpa only [logPartition, neg_mul] using hlo, hhi⟩

theorem logPartition_radial_hasDerivAt (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) (t : ℝ) :
    HasDerivAt (fun u => logPartition ν L (u • w)) (score ν L (t • w) w) t := by
  simpa only [one_smul, Function.comp_def, id_eq] using
    (logPartition_hasFDerivAt ν L hL hK hb (t • w)).comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const w)

def averagedLogPartition {ι : Type*} [Fintype ι]
    (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (t : ℝ) : ℝ :=
  ∫ w, logPartition ν L (t • w) ∂SYK.standardGaussianMeasureOnEuclidean ι

theorem gaussian_norm_integrable {ι : Type*} [Fintype ι] :
    Integrable (fun w : EuclideanSpace ℝ ι => ‖w‖)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply (SYK.integrable_exp_mul_norm (ι := ι) 1).mono' continuous_norm.aestronglyMeasurable
  exact .of_forall fun w => by
    simp only [Real.norm_of_nonneg (norm_nonneg _), one_mul]
    linarith [Real.add_one_le_exp ‖w‖]

theorem logPartition_radial_gaussian_integrable {ι : Type*} [Fintype ι]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (t : ℝ) :
    Integrable (fun w => logPartition ν L (t • w))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hn := gaussian_norm_integrable (ι := ι)
  have hcont : Continuous (fun w : EuclideanSpace ℝ ι => logPartition ν L (t • w)) :=
    (logPartition_contDiff ν L hL hK hb).continuous.comp
      (continuous_id.const_smul t)
  have hdom : ∀ᵐ w ∂SYK.standardGaussianMeasureOnEuclidean ι,
      ‖logPartition ν L (t • w)‖ ≤ (K * |t|) * ‖w‖ := .of_forall fun w => by
    rw [Real.norm_eq_abs]
    calc
      _ ≤ K * ‖t • w‖ := abs_logPartition_le ν L hL hb (t • w)
      _ = _ := by rw [norm_smul, Real.norm_eq_abs]; ring
  exact (hn.const_mul (K * |t|)).mono' hcont.aestronglyMeasurable hdom

/-- Differentiation of the actual quenched logarithm is justified by a
global integrable Gaussian norm bound on its derivative. -/
theorem averagedLogPartition_hasDerivAt {ι : Type*} [Fintype ι]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (t : ℝ) :
    HasDerivAt (averagedLogPartition ν L)
      (∫ w, score ν L (t • w) w ∂SYK.standardGaussianMeasureOnEuclidean ι) t := by
  have hn := gaussian_norm_integrable (ι := ι)
  have hsc := score_continuous ν L hL hK hb
  have hmeas : AEStronglyMeasurable (fun w : EuclideanSpace ℝ ι => score ν L (t • w) w)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    have hc : Continuous (fun w : EuclideanSpace ℝ ι => score ν L (t • w) w) :=
      (hsc.comp (continuous_id.const_smul t)).clm_apply continuous_id
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ w ∂SYK.standardGaussianMeasureOnEuclidean ι,
      ∀ u ∈ (univ : Set ℝ), ‖score ν L (u • w) w‖ ≤ K*‖w‖ := .of_forall fun w u _ =>
    ((score ν L (u • w)).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (norm_score_le ν L hL hK hb (u • w)) (norm_nonneg w))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := SYK.standardGaussianMeasureOnEuclidean ι)
    (s := univ) (F := fun u w => logPartition ν L (u • w))
    (F' := fun u w => score ν L (u • w) w) (bound := fun w => K*‖w‖)
    (by simp) (.of_forall fun u =>
      (logPartition_radial_gaussian_integrable ν L hL hK hb u).aestronglyMeasurable)
    (logPartition_radial_gaussian_integrable ν L hL hK hb t) hmeas hbound
    (hn.const_mul K) (.of_forall fun w u _ => logPartition_radial_hasDerivAt ν L hL hK hb w u)).2

theorem score_apply (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w d : H) :
    score ν L w d = expectation ν (fun v => L v d) L w := by
  rw [score, smul_apply, momentDerivative_apply ν (fun _ => 1) L measurable_const hL (C := 1) (K := K)
    (hb.mono (fun _ hv => ⟨by norm_num, hv⟩))]
  simp only [one_mul, smul_eq_mul, expectation, div_eq_mul_inv, mul_comm]

theorem expectation_const_mul (ν : Measure V) (ρ : V → ℝ)
    (L : V → H →L[ℝ] ℝ) (a : ℝ) (w : H) :
    expectation ν (fun v => a * ρ v) L w = a * expectation ν ρ L w := by
  unfold expectation moment
  simp only [weight, mul_assoc, integral_const_mul]
  ring

def scaledLinear (L : V → H →L[ℝ] ℝ) (t : ℝ) : V → H →L[ℝ] ℝ :=
  fun v => t • L v

theorem scaledLinear_measurable (L : V → H →L[ℝ] ℝ) (hL : Measurable L) (t : ℝ) :
    Measurable (scaledLinear L t) := by
  change Measurable (fun v => t • L v)
  exact (measurable_const (a := t)).smul hL

theorem scaledLinear_bound (ν : Measure V) (L : V → H →L[ℝ] ℝ) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (t : ℝ) :
    ∀ᵐ v ∂ν, ‖scaledLinear L t v‖ ≤ |t| * K := by
  filter_upwards [hb] with v hv
  rw [scaledLinear, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hv (abs_nonneg _)

theorem expectation_scaledLinear (ν : Measure V) (ρ : V → ℝ)
    (L : V → H →L[ℝ] ℝ) (t : ℝ) (w : H) :
    expectation ν ρ (scaledLinear L t) w = expectation ν ρ L (t • w) := by
  simp only [expectation, moment, weight, scaledLinear, smul_apply, map_smul, smul_eq_mul]

/-- The coordinate form of the continuous-spin Gaussian interpolation
identity. In particular the response is an actual Gibbs variance. -/
theorem gaussian_coordinate_response {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (t : ℝ) (i : ι) :
    (∫ w, w i * expectation ν (fun v => L v (EuclideanSpace.single i 1)) L (t • w)
      ∂SYK.standardGaussianMeasureOnEuclidean ι) =
    t * ∫ w,
      (expectation ν (fun v => (L v (EuclideanSpace.single i 1)) ^ 2) L (t • w) -
        expectation ν (fun v => L v (EuclideanSpace.single i 1)) L (t • w) ^ 2)
      ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  let e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  let ρ : V → ℝ := fun v => L v e
  have hρ : Measurable ρ := (ContinuousLinearMap.apply ℝ ℝ e).continuous.measurable.comp hL
  have hρb : ∀ᵐ v ∂ν, |ρ v| ≤ K := by
    filter_upwards [hb] with v hv
    have he : ‖e‖ = 1 := by simp [e]
    have hh := (L v).le_opNorm e
    rw [Real.norm_eq_abs, he, mul_one] at hh
    exact hh.trans hv
  have hbt : ∀ᵐ v ∂ν, |ρ v| ≤ K ∧ ‖scaledLinear L t v‖ ≤ |t| * K :=
    hρb.and (scaledLinear_bound ν L hb t)
  have h := gaussian_expectation_ibp ν ρ (scaledLinear L t) hρ
    (scaledLinear_measurable L hL t) hK (mul_nonneg (abs_nonneg _) hK) hbt e
  have hpoint (w : EuclideanSpace ℝ ι) :
      expectationDerivative ν ρ (scaledLinear L t) w e =
      t * (expectation ν (fun v => (L v e)^2) L (t • w) - expectation ν ρ L (t • w)^2) := by
    rw [expectationDerivative_apply ν ρ (scaledLinear L t) hρ
      (scaledLinear_measurable L hL t) hbt]
    have hprod : (fun v => ρ v * scaledLinear L t v e) = fun v => t * (L v e)^2 := by
      funext v
      simp only [ρ, scaledLinear, smul_apply, smul_eq_mul]
      ring
    have hlin : (fun v => scaledLinear L t v e) = fun v => t * ρ v := rfl
    rw [hprod, hlin, expectation_const_mul, expectation_const_mul]
    simp only [expectation_scaledLinear]
    ring
  simpa only [e, ρ, EuclideanSpace.inner_single_left, conj_trivial, one_mul,
    expectation_scaledLinear, integral_congr_ae (.of_forall hpoint), integral_const_mul] using h

theorem score_eq_coordinate_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (z w : EuclideanSpace ℝ ι) :
    score ν L z w = ∑ i, w i * expectation ν (fun v => L v (EuclideanSpace.single i 1)) L z := by
  have hw : (∑ i, w i • EuclideanSpace.single i 1) = w := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun ι ℝ).sum_repr w
  calc
    score ν L z w = score ν L z (∑ i, w i • EuclideanSpace.single i 1) :=
      congrArg (score ν L z) hw.symm
    _ = ∑ i, w i * score ν L z (EuclideanSpace.single i 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := by simp_rw [score_apply ν L hL hb]

theorem gaussian_coordinate_score_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (t : ℝ) (i : ι) :
    Integrable (fun w => w i * expectation ν (fun v => L v (EuclideanSpace.single i 1)) L (t • w))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  let e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  let ρ : V → ℝ := fun v => L v e
  have hρ : Measurable ρ := (ContinuousLinearMap.apply ℝ ℝ e).continuous.measurable.comp hL
  have hρb : ∀ᵐ v ∂ν, |ρ v| ≤ K ∧ ‖L v‖ ≤ K := by
    filter_upwards [hb] with v hv
    have hh := (L v).le_opNorm e
    have he : ‖e‖ = 1 := by simp [e]
    rw [Real.norm_eq_abs, he, mul_one] at hh
    exact ⟨hh.trans hv, hv⟩
  have hc : Continuous (fun w : EuclideanSpace ℝ ι =>
      w i * expectation ν ρ L (t • w)) :=
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).mul ((expectation_contDiff ν ρ L hρ hL hK hK hρb).continuous.comp
      (continuous_id.const_smul t))
  apply (gaussian_norm_integrable (ι := ι) |>.const_mul K).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => by
    rw [norm_mul, Real.norm_eq_abs]
    have he := norm_expectation_le ν ρ L hρ hL hK hρb (t • w)
    calc
      _ ≤ ‖w‖ * K := mul_le_mul (PiLp.norm_apply_le w i) he (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_comm _ _

/-- The exact radial Gaussian interpolation derivative. Every term is an
ordinary integral Gibbs expectation, for arbitrary bounded measurable spins. -/
theorem averagedLogPartition_hasDerivAt_covarianceTrace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (t : ℝ) :
    HasDerivAt (averagedLogPartition ν L)
      (t * ∑ i, ∫ w,
        (expectation ν (fun v => (L v (EuclideanSpace.single i 1)) ^ 2) L (t • w) -
          expectation ν (fun v => L v (EuclideanSpace.single i 1)) L (t • w) ^ 2)
        ∂SYK.standardGaussianMeasureOnEuclidean ι) t := by
  have hd := averagedLogPartition_hasDerivAt ν L hL hK hb t
  convert hd using 1
  rw [integral_congr_ae (.of_forall (fun w => score_eq_coordinate_sum ν L hL hb (t • w) w)),
    integral_finsetSum Finset.univ (fun i _ => gaussian_coordinate_score_integrable ν L hL hK hb t i)]
  simp_rw [gaussian_coordinate_response ν L hL hK hb t]
  exact Finset.mul_sum _ _ _

/-- The ordinary Gibbs measure behind the normalized integral notation. -/
def gibbsMeasure (ν : Measure V) (L : V → H →L[ℝ] ℝ) (w : H) : Measure V :=
  ν.withDensity (fun v => ENNReal.ofReal
    (Real.exp (L v w) / moment ν (fun _ => 1) L w))

theorem gibbsMeasure_absolutelyContinuous (ν : Measure V) (L : V → H →L[ℝ] ℝ) (w : H) :
    gibbsMeasure ν L w ≪ ν := withDensity_absolutelyContinuous _ _

theorem gibbsMeasure_probability (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) : IsProbabilityMeasure (gibbsMeasure ν L w) := by
  have hz := moment_one_pos ν L hL hb w
  have hi := weight_integrable ν (fun _ => 1) L measurable_const hL
    (hb.mono (fun _ hv => ⟨by norm_num, hv⟩) : ∀ᵐ v ∂ν, |(1:ℝ)| ≤ 1 ∧ ‖L v‖ ≤ K) w
  change Integrable (fun v => 1*Real.exp (L v w)) ν at hi
  simp only [one_mul] at hi
  constructor
  rw [gibbsMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (.of_forall fun v => (div_pos (Real.exp_pos _) hz).le), integral_div]
  have hm : (∫ v, Real.exp (L v w) ∂ν) = moment ν (fun _ => 1) L w := by
    simp only [moment, weight, one_mul]
  rw [hm, div_self hz.ne', ENNReal.ofReal_one]

theorem integral_gibbsMeasure (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) (ρ : V → ℝ) :
    (∫ v, ρ v ∂gibbsMeasure ν L w) = expectation ν ρ L w := by
  have hz := moment_one_pos ν L hL hb w
  have hm : Measurable (fun v => Real.exp (L v w) / moment ν (fun _ => 1) L w) :=
    ((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL).exp.div_const _
  rw [gibbsMeasure, integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (div_pos (Real.exp_pos _) hz).le, smul_eq_mul]
  unfold expectation moment
  rw [← integral_div]
  apply integral_congr_ae
  exact .of_forall fun v => by simp only [weight]; ring

/-- The covariance term in interpolation is exactly the variance under the
actual normalized Gibbs probability measure. -/
theorem expectation_variance (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    expectation ν (fun v => (ρ v)^2) L w - (expectation ν ρ L w)^2 =
      variance ρ (gibbsMeasure ν L w) := by
  have hfield := hb.mono (fun _ hv => hv.2)
  have : IsProbabilityMeasure (gibbsMeasure ν L w) := gibbsMeasure_probability ν L hL hfield w
  have hm : MemLp ρ 2 (gibbsMeasure ν L w) := MemLp.of_bound hρ.aestronglyMeasurable C
    ((hb.mono (fun v hv => by simpa only [Real.norm_eq_abs] using hv.1)).filter_mono
      (gibbsMeasure_absolutelyContinuous ν L w).ae_le)
  rw [← covariance_self hm.aemeasurable, covariance_eq_sub hm hm,
    integral_gibbsMeasure ν L hL hfield w ρ]
  simp only [Pi.mul_apply]
  rw [integral_gibbsMeasure ν L hL hfield w (fun v => ρ v * ρ v)]
  simp only [pow_two]

theorem expectation_square_sub_square_nonneg (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (ρ : V → ℝ) (L : V → H →L[ℝ] ℝ) (hρ : Measurable ρ) (hL : Measurable L)
    {C K : ℝ} (hb : ∀ᵐ v ∂ν, |ρ v| ≤ C ∧ ‖L v‖ ≤ K) (w : H) :
    0 ≤ expectation ν (fun v => (ρ v)^2) L w - (expectation ν ρ L w)^2 := by
  rw [expectation_variance ν ρ L hρ hL hb w]
  exact variance_nonneg _ _

end
end SlowEquilibration.GaussianSpinInterpolation
