-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalOverlapExponential
public import SphericalAging.BrownianFutureConditionalIntegral
public import Mathlib.Probability.Martingale.Basic

/-! Conditional expectation for the original C1 spherical flow is derived
from its genuine future-Wiener restart and independent future integration. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalOverlapExponential
open MeasureTheory ProbabilityTheory Set Filter
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalC1Dynamics SphericalReversibility.Ito MultivariateTaylor
open scoped NNReal ContDiff InnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def physicalFiltration (N : ℕ) :=
  NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)

/-- The conditional Markov identity is proved from the actual independent
future Brownian path, with no conditional transition premise. -/
theorem process_condExp (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (x : State N) (s t : ℝ≥0) (f : State N → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y,‖f y‖ ≤ C) :
    (VectorBrownian.law N)[(fun omega => f (process β g hg x (s + t) omega)) | physicalFiltration N s]
      =ᵐ[VectorBrownian.law N]
    fun omega => expectation β g hg t f (process β g hg x s omega) := by
  let hb := (cutoffDrift_lipschitz β g hg _ (cutoffRadius_pos N)).choose_spec
  let hn := (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec
  let D := FixedCoefficients.canonicalDriver N
  let Z := process β g hg x s
  let G : State N × VectorBrownian.Space N → ℝ :=
    fun q => f (FixedCoefficients.jointProcess D hb hn q.1 t q.2)
  have hZ : Measurable[physicalFiltration N s] Z :=
    (GlobalSDE.process_stronglyAdapted D hb hn x s).measurable
  have hmZ : Measurable Z := hZ.mono ((physicalFiltration N).le s) le_rfl
  let : IsProbabilityMeasure ((VectorBrownian.law N).map Z) := by infer_instance
  have hG : StronglyMeasurable G :=
    hf.stronglyMeasurable.comp_measurable (FixedCoefficients.terminal_measurable D hb hn t)
  have hGi : Integrable G (((VectorBrownian.law N).map Z).prod (VectorBrownian.law N)) :=
    Integrable.of_bound hG.aestronglyMeasurable C (.of_forall fun q => hC _)
  have hr := FixedCoefficients.future_restart hb hn (coefficientBounds β g hg) x s t
  have he : (fun omega => f (process β g hg x (s + t) omega)) =ᵐ[VectorBrownian.law N]
      (fun omega => G (Z omega,BrownianFuturePath.future s omega)) :=
    hr.mono (fun _ h => congrArg f h)
  have hc := BrownianFutureConditionalIntegral.waiting_future_condExp s Z hZ G hG hGi
  have hi (y : State N) : (∫ eta,G (y,eta) ∂VectorBrownian.law N) = expectation β g hg t f y := by
    apply integral_congr_ae
    filter_upwards [FixedCoefficients.jointProcess_ae D hb hn y] with eta heta
    exact congrArg f (heta t)
  exact (condExp_congr_ae he).trans (hc.trans (.of_forall fun omega => hi (Z omega)))

def clippedExpOverlap (u : State N) (ell : ℝ) (x : State N) : ℝ :=
  Real.exp (ell * max (-1) (min 1 (overlapValue u x)))

lemma clippedExpOverlap_continuous (u : State N) (ell : ℝ) : Continuous (clippedExpOverlap u ell) := by
  unfold clippedExpOverlap overlapValue
  fun_prop

lemma clippedExpOverlap_bound (u : State N) (ell : ℝ) (x : State N) :
    ‖clippedExpOverlap u ell x‖ ≤ Real.exp |ell| := by
  unfold clippedExpOverlap
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  have hb : |max (-1 : ℝ) (min 1 (overlapValue u x))| ≤ 1 := by
    apply abs_le.mpr
    exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  exact (le_abs_self _).trans (by rw [abs_mul]; nlinarith [abs_nonneg ell])

lemma clippedExpOverlap_eq (hN : N ≠ 0) (u x : State N) (hu : OnSphere u) (hx : OnSphere x) (ell : ℝ) :
    clippedExpOverlap u ell x = expOverlap u ell x := by
  have hb := abs_le.mp (overlapValue_abs_le_one hN u x hu hx)
  unfold clippedExpOverlap
  rw [min_eq_right hb.2,max_eq_right hb.1]
  rfl

lemma expectation_clippedExpOverlap_eq (hN : N ≠ 0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g) (u : State N) (hu : OnSphere u)
    (x : State N) (hx : OnSphere x) (ell : ℝ) (t : ℝ≥0) :
    expectation β g hg t (clippedExpOverlap u ell) x = expectation β g hg t (expOverlap u ell) x := by
  apply integral_congr_ae
  filter_upwards [process_onSphere hN β g hg x hx] with omega homega
  exact clippedExpOverlap_eq hN u _ hu (homega t) ell

/-- Actual conditional exponential moment uses the true sphere process,
rather than an assumed conditional MGF or Markov property. -/
theorem expOverlap_condExp (hN : N ≠ 0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g) (u x : State N)
    (hu : OnSphere u) (hx : OnSphere x) (ell : ℝ) (s t : ℝ≥0) :
    (VectorBrownian.law N)[(fun omega => expOverlap u ell (process β g hg x (s + t) omega)) | physicalFiltration N s]
      =ᵐ[VectorBrownian.law N]
    fun omega => expectation β g hg t (expOverlap u ell) (process β g hg x s omega) := by
  have he : (fun omega => expOverlap u ell (process β g hg x (s + t) omega)) =ᵐ[VectorBrownian.law N]
      (fun omega => clippedExpOverlap u ell (process β g hg x (s + t) omega)) := by
    filter_upwards [process_onSphere hN β g hg x hx] with omega homega
    exact (clippedExpOverlap_eq hN u _ hu (homega (s + t)) ell).symm
  have hc := process_condExp β g hg x s t (clippedExpOverlap u ell)
    (clippedExpOverlap_continuous u ell) (Real.exp |ell|) (clippedExpOverlap_bound u ell)
  have hinner : (fun omega => expectation β g hg t (clippedExpOverlap u ell) (process β g hg x s omega)) =ᵐ[VectorBrownian.law N]
      (fun omega => expectation β g hg t (expOverlap u ell) (process β g hg x s omega)) := by
    filter_upwards [process_onSphere hN β g hg x hx] with omega homega
    exact expectation_clippedExpOverlap_eq hN β g hg u hu _ (homega s) ell t
  exact (condExp_congr_ae he).trans (hc.trans hinner)

lemma expOverlap_bound_onSphere (hN : N ≠ 0) (u x : State N) (hu : OnSphere u)
    (hx : OnSphere x) (ell : ℝ) : ‖expOverlap u ell x‖ ≤ Real.exp |ell| := by
  rw [← clippedExpOverlap_eq hN u x hu hx ell]
  exact clippedExpOverlap_bound u ell x

lemma expOverlap_process_integrable (hN : N ≠ 0) (β : ℝ)
    (g : State N → State N) (hg : ContDiff ℝ 1 g) (u x : State N)
    (hu : OnSphere u) (hx : OnSphere x) (ell : ℝ) (t : ℝ≥0) :
    Integrable (fun omega => expOverlap u ell (process β g hg x t omega)) (VectorBrownian.law N) := by
  have ha := GlobalSDE.process_stronglyAdapted (FixedCoefficients.canonicalDriver N)
    (cutoffDrift_lipschitz β g hg _ (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec x t
  apply Integrable.of_bound (((expLinear_contDiff (ell • overlapLinear u)).continuous.comp_stronglyMeasurable ha).mono
    ((physicalFiltration N).le t)).aestronglyMeasurable (Real.exp |ell|)
  exact (process_onSphere hN β g hg x hx).mono (fun _ h => expOverlap_bound_onSphere hN u _ hu (h t) ell)

def overlapSubmartingale (β C : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (u x : State N) (ell : ℝ) (t : ℝ≥0) (omega : VectorBrownian.Space N) : ℝ :=
  Real.exp ((|ell| * (1 + β * C)) * (t : ℝ)) * expOverlap u ell (process β g hg x t omega)

lemma overlapSubmartingale_nonneg (β C : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (u x : State N) (ell : ℝ) : 0 ≤ overlapSubmartingale β C g hg u x ell := by
  intro t omega
  exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le

/-- The original exponential overlap, with a deterministic drift factor,
is a true submartingale in the actual augmented Brownian filtration. -/
theorem overlapSubmartingale_submartingale (hN : N ≠ 0) {β C : ℝ} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (hgrad : ∀ y,OnSphere y → ‖g y‖ ≤ C * Real.sqrt (N : ℝ))
    (u x : State N) (hu : OnSphere u) (hx : OnSphere x) (ell : ℝ) :
    Submartingale (overlapSubmartingale β C g hg u x ell) (physicalFiltration N) (VectorBrownian.law N) := by
  let b := |ell| * (1 + β * C)
  have ha : StronglyAdapted (physicalFiltration N) (fun t omega => expOverlap u ell (process β g hg x t omega)) := by
    intro t
    exact (expLinear_contDiff (ell • overlapLinear u)).continuous.comp_stronglyMeasurable
      (GlobalSDE.process_stronglyAdapted (FixedCoefficients.canonicalDriver N)
        (cutoffDrift_lipschitz β g hg _ (cutoffRadius_pos N)).choose_spec
        (CutoffSDE.cutoffNoise_lipschitz N _ (cutoffRadius_pos N)).choose_spec x t)
  refine ⟨fun t => stronglyMeasurable_const.mul (ha t),?_,fun t =>
    (expOverlap_process_integrable hN β g hg u x hu hx ell t).const_mul (Real.exp (b * (t : ℝ)))⟩
  intro i j hij
  have ht : i + (j - i) = j := add_tsub_cancel_of_le hij
  have hc := expOverlap_condExp hN β g hg u x hu hx ell i (j - i)
  rw [ht] at hc
  have hm := condExp_smul (μ := VectorBrownian.law N) (Real.exp (b * (j : ℝ)))
    (fun omega => expOverlap u ell (process β g hg x j omega)) (physicalFiltration N i)
  filter_upwards [hc,hm,process_onSphere hN β g hg x hx] with omega homega hscale hsphere
  have hl := expectation_expOverlap_lower hN hβ hC g hg hgrad u (process β g hg x i omega)
    hu (hsphere i) ell (j - i)
  have hex : Real.exp (b * (j : ℝ)) * Real.exp ((-|ell| * (1 + β * C)) * ((j - i : ℝ≥0) : ℝ)) =
      Real.exp (b * (i : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    have he := congrArg (fun r : ℝ≥0 => (r : ℝ)) ht
    simp only [NNReal.coe_add] at he
    rw [← he]
    dsimp [b]
    ring
  have hlo := mul_le_mul_of_nonneg_left hl (Real.exp_pos (b * (j : ℝ))).le
  rw [← mul_assoc,hex] at hlo
  change Real.exp (b * (i : ℝ)) * expOverlap u ell (process β g hg x i omega) ≤ _
  have hUj : overlapSubmartingale β C g hg u x ell j =
      Real.exp (b * (j : ℝ)) • (fun omega => expOverlap u ell (process β g hg x j omega)) := by
    funext eta
    rfl
  rw [hUj,hscale]
  change _ ≤ Real.exp (b * (j : ℝ)) *
    ((VectorBrownian.law N)[fun eta => expOverlap u ell (process β g hg x j eta) | physicalFiltration N i] omega)
  rw [homega]
  exact hlo

end SlowEquilibration.SphericalOverlapExponential
