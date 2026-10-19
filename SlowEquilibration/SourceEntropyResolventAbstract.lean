-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedEntranceFisher
public import SlowEquilibration.ConditionedEntranceGlobalInitialL1
public import SlowEquilibration.ConditionedEntranceNormalizedTiltIntegrable
public import SlowEquilibration.ConditionedEntranceSquareCommutatorReduction
public import SlowEquilibration.ConditionedEntranceWeightedDefectCauchy
public import SlowEquilibration.ConditionedEntranceKillingHorizon
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The abstract analytic steps of Section 8's entropy--resolvent comparison.
The carré du champ, weak resolvent equations, and change of measure are
kept separate from all quantitative Fisher and weighted-energy conclusions.
The general closed-form realization and process identification are explicit
interfaces. This module does not construct the associated self-adjoint
operators from a closed Dirichlet form, or construct the Markov process and
unit-exponential killing time. The bridges from those literal objects to
the particular realization interfaces remain unproved. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceEntropyResolventAbstract
open MeasureTheory Filter Set
open scoped Topology ENNReal
open SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Type*} [MeasurableSpace X]

/-- A bounded measurable representative; the bound is never used in the
constants of the comparison. -/
def BoundedMeasurable (g : X → ℝ) : Prop :=
  Measurable g ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C

private lemma bm_const (a : ℝ) : BoundedMeasurable (fun _ : X => a) :=
  ⟨measurable_const, ‖a‖, norm_nonneg _, fun _ => le_rfl⟩

private lemma bm_add {f g : X → ℝ} (hf : BoundedMeasurable f)
    (hg : BoundedMeasurable g) : BoundedMeasurable (fun x => f x + g x) := by
  obtain ⟨hf, A, hA, hbA⟩ := hf
  obtain ⟨hg, B, hB, hbB⟩ := hg
  exact ⟨hf.add hg, A+B, add_nonneg hA hB, fun x =>
    (norm_add_le _ _).trans (add_le_add (hbA x) (hbB x))⟩

private lemma bm_neg {f : X → ℝ} (hf : BoundedMeasurable f) :
    BoundedMeasurable (fun x => -f x) := by
  obtain ⟨hf, A, hA, hbA⟩ := hf
  exact ⟨hf.neg, A, hA, fun x => by simpa only [norm_neg] using hbA x⟩

private lemma bm_sub {f g : X → ℝ} (hf : BoundedMeasurable f)
    (hg : BoundedMeasurable g) : BoundedMeasurable (fun x => f x-g x) :=
  bm_add hf (bm_neg hg)

private lemma bm_mul {f g : X → ℝ} (hf : BoundedMeasurable f)
    (hg : BoundedMeasurable g) : BoundedMeasurable (fun x => f x*g x) := by
  obtain ⟨hf, A, hA, hbA⟩ := hf
  obtain ⟨hg, B, hB, hbB⟩ := hg
  exact ⟨hf.mul hg, A*B, mul_nonneg hA hB, fun x => by
    rw [norm_mul]
    exact mul_le_mul (hbA x) (hbB x) (norm_nonneg _) hA⟩

private lemma bm_sq {f : X → ℝ} (hf : BoundedMeasurable f) :
    BoundedMeasurable (fun x => f x^2) := by
  simpa only [pow_two] using bm_mul hf hf

private lemma bm_abs {f : X → ℝ} (hf : BoundedMeasurable f) :
    BoundedMeasurable (fun x => |f x|) := by
  obtain ⟨hm,C,hC,hb⟩ := hf
  exact ⟨hm.abs,C,hC,fun x => by simpa only [Real.norm_eq_abs,abs_abs] using hb x⟩

private lemma bm_exp {f : X → ℝ} (hf : BoundedMeasurable f) :
    BoundedMeasurable (fun x => Real.exp (f x)) := by
  obtain ⟨hf, A, hA, hbA⟩ := hf
  refine ⟨hf.exp, Real.exp A, (Real.exp_pos A).le, fun x => ?_⟩
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hbA x))

private lemma bm_defect {w : X → ℝ} (hw : BoundedMeasurable w) :
    BoundedMeasurable (tiltDefect w) := bm_sub (bm_const 1) (bm_exp (bm_neg hw))

private lemma bm_log {F : X → ℝ} (hF : BoundedMeasurable F)
    (hFlo : ∀ x, 1 ≤ F x) : BoundedMeasurable (fun x => Real.log (F x)) := by
  obtain ⟨hm, A, hA, hbA⟩ := hF
  refine ⟨hm.log, A, hA, fun x => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (hFlo x))]
  exact (Real.log_le_sub_one_of_pos (by linarith [hFlo x])).trans
    (by have hb := hbA x; rw [Real.norm_eq_abs,
        abs_of_nonneg (by linarith [hFlo x])] at hb; linarith)

private lemma bm_inv {F : X → ℝ} (hF : BoundedMeasurable F)
    (hFlo : ∀ x, 1 ≤ F x) : BoundedMeasurable (fun x => (F x)⁻¹) := by
  refine ⟨hF.1.inv, 1, by norm_num, fun x => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith [hFlo x]))]
  exact inv_le_one_of_one_le₀ (hFlo x)

private lemma bm_integrable (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : BoundedMeasurable f) : Integrable f μ := by
  obtain ⟨hm, C, hC, hb⟩ := hf
  exact (integrable_const (μ := μ) C).mono' hm.aestronglyMeasurable
    (.of_forall fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using hb x)

private lemma bm_mul_integrable (μ : Measure X) {f g : X → ℝ}
    (hf : BoundedMeasurable f) (hg : Integrable g μ) :
    Integrable (fun x => f x*g x) μ := by
  obtain ⟨hm, C, _, hb⟩ := hf
  exact hg.bdd_mul hm.aestronglyMeasurable (.of_forall hb)

private lemma tilt_integrable (μ : Measure X) {w g : X → ℝ}
    (hw : BoundedMeasurable w) {M : ℝ} (hM : 0 < M) (hg : Integrable g μ) :
    Integrable g (normalizedTilt μ w M) :=
  (integrable_normalizedTilt_iff μ w g hw.1 hM).2
    (bm_mul_integrable μ (bm_exp hw) hg)

/-- Integral Cauchy--Schwarz for an abstract carré du champ. It requires
only its pointwise determinant inequality, and allows vanishing energies. -/
theorem integral_cauchy_of_square_bound (μ : Measure X) (a b c : X → ℝ)
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ)
    (ha0 : ∀ᵐ x ∂μ, 0 ≤ a x) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hsq : ∀ᵐ x ∂μ, c x^2 ≤ a x*b x) :
    |∫ x, c x ∂μ| ≤ Real.sqrt ((∫ x, a x ∂μ)*(∫ x, b x ∂μ)) := by
  have hquad (t : ℝ) : 0 ≤
      (∫ x, a x ∂μ)*(t*t) + (2*(∫ x, c x ∂μ))*t + ∫ x, b x ∂μ := by
    have hp : ∀ᵐ x ∂μ, 0 ≤ a x*(t*t)+(2*c x)*t+b x := by
      filter_upwards [ha0,hb0,hsq] with x hax hbx hx
      by_cases haZ : a x = 0
      · have hcZ : c x = 0 := by rw [haZ, zero_mul] at hx; nlinarith [sq_nonneg (c x)]
        simp [haZ,hcZ,hbx]
      · have hap : 0 < a x := lt_of_le_of_ne hax (Ne.symm haZ)
        have hh : 0 ≤ a x*(a x*(t*t)+(2*c x)*t+b x) := by
          nlinarith [sq_nonneg (a x*t+c x)]
        exact nonneg_of_mul_nonneg_right hh hap
    have hi := integral_nonneg_of_ae hp
    have hsum := integral_add ((ha.mul_const (t*t)).add ((hc.const_mul 2).mul_const t)) hb
    change (∫ x, a x*(t*t)+(2*c x)*t+b x ∂μ) =
      (∫ x, a x*(t*t)+(2*c x)*t ∂μ)+(∫ x, b x ∂μ) at hsum
    have hsum' := integral_add (ha.mul_const (t*t)) ((hc.const_mul 2).mul_const t)
    change (∫ x, a x*(t*t)+(2*c x)*t ∂μ) =
      (∫ x, a x*(t*t) ∂μ)+(∫ x, (2*c x)*t ∂μ) at hsum'
    rw [hsum, hsum', integral_mul_const, integral_mul_const, integral_const_mul] at hi
    exact hi
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  have hA := integral_nonneg_of_ae ha0
  have hB := integral_nonneg_of_ae hb0
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1
  rw [sq_abs, Real.sq_sqrt (mul_nonneg hA hB)]
  nlinarith

/-- The sharp zero-order error uses the unshifted densities of mass one.
This is the printed `5 sqrt ε`, rather than the shifted-density constant. -/
theorem density_defect_le_five_sqrt (ν : Measure X) (k I f h : X → ℝ)
    (hI : Integrable I ν) (hf : Integrable f ν)
    (hkI : Integrable (fun x => k x^2*I x) ν)
    (hkf : Integrable (fun x => k x^2*f x) ν)
    (hc : Integrable (fun x => k x*(I x-f x)*h x) ν)
    (hI0 : ∀ᵐ x ∂ν, 0 ≤ I x) (hf0 : ∀ᵐ x ∂ν, 0 ≤ f x)
    (hh : ∀ᵐ x ∂ν, 0 ≤ h x ∧ h x ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hImass : (∫ x, I x ∂ν) ≤ 3) (hfmass : (∫ x, f x ∂ν) ≤ 3)
    (hkImass : (∫ x, k x^2*I x ∂ν) ≤ 2*ε)
    (hkfmass : (∫ x, k x^2*f x ∂ν) ≤ 2*ε) :
    |∫ x, k x*(I x-f x)*h x ∂ν| ≤ 5*Real.sqrt ε := by
  let a := fun x => k x^2*I x+k x^2*f x
  let b := fun x => I x+f x
  let c := fun x => k x*(I x-f x)*h x
  have ha0 : ∀ᵐ x ∂ν, 0 ≤ a x := by
    filter_upwards [hI0,hf0] with x hi hf
    exact add_nonneg (mul_nonneg (sq_nonneg _) hi) (mul_nonneg (sq_nonneg _) hf)
  have hb0 : ∀ᵐ x ∂ν, 0 ≤ b x := by
    filter_upwards [hI0,hf0] with x hi hf using add_nonneg hi hf
  have hs : ∀ᵐ x ∂ν, c x^2 ≤ a x*b x := by
    filter_upwards [hI0,hf0,hh] with x hi hf hu
    have hu2 : h x^2 ≤ 1 := by nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hu.2)]
    have hd : (I x-f x)^2 ≤ (I x+f x)^2 := by nlinarith [mul_nonneg hi hf]
    have hm := mul_le_mul_of_nonneg_left hu2 (mul_nonneg (sq_nonneg (k x))
      (sq_nonneg (I x-f x)))
    have hm' := mul_le_mul_of_nonneg_left hd (sq_nonneg (k x))
    dsimp only [a,b,c]
    nlinarith
  have hcs := integral_cauchy_of_square_bound ν a b c (hkI.add hkf) (hI.add hf) hc ha0 hb0 hs
  have hA : (∫ x, a x ∂ν) ≤ 4*ε := by
    dsimp only [a]; rw [integral_add hkI hkf]; linarith
  have hB : (∫ x, b x ∂ν) ≤ 6 := by
    dsimp only [b]; rw [integral_add hI hf]; linarith
  have hp : (∫ x, a x ∂ν)*(∫ x, b x ∂ν) ≤ 24*ε := by
    have hm := mul_le_mul hA hB (integral_nonneg_of_ae hb0) (by positivity : 0 ≤ 4*ε)
    nlinarith
  have hroot : Real.sqrt (24*ε) ≤ 5*Real.sqrt ε := by
    nlinarith [Real.sq_sqrt hε, Real.sq_sqrt (show 0 ≤ 24*ε by positivity),
      Real.sqrt_nonneg ε, Real.sqrt_nonneg (24*ε)]
  exact hcs.trans ((Real.sqrt_le_sqrt hp).trans hroot)

/-- The actual domain and carré-du-champ data in (D1)--(D3). Bilinearity
is represented by linear maps; identities and positivity are a.e.
statements, so no common exceptional set is imposed on the form domain. -/
structure DiffusionCalculus (μ : Measure X) where
  domain : Submodule ℝ (X → ℝ)
  gamma : (X → ℝ) →ₗ[ℝ] (X → ℝ) →ₗ[ℝ] (X → ℝ)
  integrable : ∀ g ∈ domain, ∀ v ∈ domain, Integrable (gamma g v) μ
  symmetric : ∀ g ∈ domain, ∀ v ∈ domain, gamma g v =ᵐ[μ] gamma v g
  nonnegative : ∀ g ∈ domain, ∀ᵐ x ∂μ, 0 ≤ gamma g g x
  one_mem : (fun _ => (1 : ℝ)) ∈ domain
  conservative : (∫ x, gamma (fun _ => 1) (fun _ => 1) x ∂μ) = 0
  mul_mem : ∀ g ∈ domain, ∀ v ∈ domain,
    BoundedMeasurable g → BoundedMeasurable v → (fun x => g x*v x) ∈ domain
  product_rule : ∀ g ∈ domain, ∀ v ∈ domain, ∀ ψ ∈ domain,
    BoundedMeasurable g → BoundedMeasurable v →
    gamma (fun x => g x*v x) ψ =ᵐ[μ]
      (fun x => g x*gamma v ψ x+v x*gamma g ψ x)
  chain_mem : ∀ g ∈ domain, BoundedMeasurable g → ∀ φ : ℝ → ℝ,
    ContDiff ℝ 1 φ → (fun x => φ (g x)) ∈ domain
  chain_rule : ∀ g ∈ domain, ∀ ψ ∈ domain, BoundedMeasurable g →
    ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ →
    gamma (fun x => φ (g x)) ψ =ᵐ[μ]
      (fun x => deriv φ (g x)*gamma g ψ x)

private lemma gamma_cauchy (μ : Measure X) (D : DiffusionCalculus μ)
    (g v : X → ℝ) (hg : g ∈ D.domain) (hv : v ∈ D.domain) :
    ∀ᵐ x ∂μ, (D.gamma g v x)^2 ≤ D.gamma g g x*D.gamma v v x := by
  have hq (q : ℚ) : ∀ᵐ x ∂μ,
      0 ≤ D.gamma g g x*((q : ℝ)*(q : ℝ))+
        (2*D.gamma g v x)*(q : ℝ)+D.gamma v v x := by
    have hp := D.nonnegative ((q : ℝ) • g+v)
      (D.domain.add_mem (D.domain.smul_mem (q : ℝ) hg) hv)
    filter_upwards [hp, D.symmetric g hg v hv] with x hx hs
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx
    rw [← hs] at hx
    convert hx using 1; ring
  have hall := eventually_countable_forall.mpr hq
  filter_upwards [hall] with x hx
  have hp (t : ℝ) : 0 ≤ D.gamma g g x*(t*t)+
      (2*D.gamma g v x)*t+D.gamma v v x := by
    exact Rat.denseRange_cast.induction_on t
      (isClosed_le continuous_const (by fun_prop)) hx
  have hd := discrim_le_zero hp
  unfold discrim at hd
  nlinarith

private lemma gamma_one_zero (μ : Measure X) (D : DiffusionCalculus μ)
    (g : X → ℝ) (hg : g ∈ D.domain) :
    D.gamma (fun _ => 1) g =ᵐ[μ] (fun _ => 0) := by
  have hz := (integral_eq_zero_iff_of_nonneg_ae
    (D.nonnegative _ D.one_mem) (D.integrable _ D.one_mem _ D.one_mem)).mp D.conservative
  filter_upwards [hz, gamma_cauchy μ D (fun _ => 1) g D.one_mem hg] with x hx hc
  change D.gamma (fun _ => 1) (fun _ => 1) x = 0 at hx
  rw [hx, zero_mul] at hc
  nlinarith [sq_nonneg (D.gamma (fun _ => 1) g x)]

private def positiveLogExtension (x : ℝ) : ℝ :=
  Real.log (x*Real.smoothTransition (4*x-2)+(1-Real.smoothTransition (4*x-2)))

private lemma positiveLogExtension_contDiff : ContDiff ℝ 1 positiveLogExtension := by
  have hc : ContDiff ℝ 1 (fun x : ℝ => Real.smoothTransition (4*x-2)) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  apply (contDiff_id.mul hc |>.add (contDiff_const.sub hc)).log
  intro x
  apply ne_of_gt
  by_cases hx : x ≤ 1/2
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 4*x-2 ≤ 0)]
    norm_num
  · have hs := Real.smoothTransition.nonneg (4*x-2)
    have hs1 := Real.smoothTransition.le_one (4*x-2)
    have hp : 0 < x := by linarith
    by_cases hs0 : Real.smoothTransition (4*x-2) = 0
    · rw [hs0]; norm_num
    · have hsp : 0 < Real.smoothTransition (4*x-2) := lt_of_le_of_ne hs (Ne.symm hs0)
      change 0 < x*Real.smoothTransition (4*x-2)+(1-Real.smoothTransition (4*x-2))
      nlinarith [mul_pos hp hsp]

private lemma positiveLogExtension_eq {x : ℝ} (hx : 3/4 ≤ x) :
    positiveLogExtension x = Real.log x := by
  unfold positiveLogExtension
  rw [Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4*x-2)]
  simp

private lemma positiveLogExtension_deriv {x : ℝ} (hx : 1 ≤ x) :
    deriv positiveLogExtension x = x⁻¹ := by
  have he : positiveLogExtension =ᶠ[𝓝 x] Real.log := by
    filter_upwards [Ioi_mem_nhds (by linarith : 3/4 < x)] with y hy
    exact positiveLogExtension_eq hy.le
  exact ((Real.hasDerivAt_log (by linarith : x ≠ 0)).congr_of_eventuallyEq he).deriv

private lemma log_domain (μ : Measure X) (D : DiffusionCalculus μ)
    (F : X → ℝ) (hF : F ∈ D.domain) (hbF : BoundedMeasurable F)
    (hFlo : ∀ x, 1 ≤ F x) : (fun x => Real.log (F x)) ∈ D.domain := by
  have he : (fun x => positiveLogExtension (F x)) = fun x => Real.log (F x) := by
    funext x
    exact positiveLogExtension_eq (by linarith [hFlo x])
  rw [← he]
  exact D.chain_mem F hF hbF positiveLogExtension positiveLogExtension_contDiff

private lemma gamma_log (μ : Measure X) (D : DiffusionCalculus μ)
    (F : X → ℝ) (hF : F ∈ D.domain) (hbF : BoundedMeasurable F)
    (hFlo : ∀ x, 1 ≤ F x) :
    D.gamma F (fun x => Real.log (F x)) =ᵐ[μ]
      (fun x => D.gamma F F x/F x) := by
  have hlog := log_domain μ D F hF hbF hFlo
  have he : (fun x => positiveLogExtension (F x)) = fun x => Real.log (F x) := by
    funext x; exact positiveLogExtension_eq (by linarith [hFlo x])
  have hc := D.chain_rule F hF F hF hbF positiveLogExtension positiveLogExtension_contDiff
  rw [he] at hc
  filter_upwards [D.symmetric F hF _ hlog, hc] with x hs hx
  rw [hs,hx,positiveLogExtension_deriv (hFlo x)]
  ring

/-- The Fisher estimate `eq:ent-fisher` is a consequence of (D1)--(D3)
and the weak unperturbed resolvent equation, with no Fisher hypothesis. -/
theorem abstract_resolvent_fisher_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (D : DiffusionCalculus μ) (F₀ F : X → ℝ)
    (hF₀ : BoundedMeasurable F₀) (hF : BoundedMeasurable F)
    (hF₀pos : ∀ x, 0 < F₀ x) (hFlo : ∀ x, 1 ≤ F x)
    (hFdom : F ∈ D.domain) {lam : ℝ} (hlam : 0 ≤ lam)
    (hmass : (∫ x, F₀ x ∂μ) = ∫ x, F x ∂μ)
    (hres : ∀ v ∈ D.domain, BoundedMeasurable v →
      (∫ x, D.gamma F v x ∂μ) = lam*∫ x, (F₀ x-F x)*v x ∂μ) :
    (∫ x, D.gamma F F x/F x ∂μ) ≤ lam*∫ x, F₀ x*Real.log (F₀ x) ∂μ := by
  have hlog := log_domain μ D F hFdom hF hFlo
  have hlogb := bm_log hF hFlo
  have htest := hres _ hlog hlogb
  rw [integral_congr_ae (gamma_log μ D F hFdom hF hFlo)] at htest
  have hF₀log : Integrable (fun x => F₀ x*Real.log (F₀ x)) μ := by
    obtain ⟨hm₀, C, _, hCb⟩ := hF₀
    have hm : Measurable (fun x => F₀ x*Real.log (F₀ x)) := hm₀.mul hm₀.log
    have hc : ContinuousOn (fun x : ℝ => x*Real.log x) (Icc 0 C) :=
      (Real.continuous_mul_log.continuousOn)
    obtain ⟨K,hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    exact (integrable_const (μ := μ) (max K 0)).mono' hm.aestronglyMeasurable
      (.of_forall fun x => (hK (F₀ x) ⟨(hF₀pos x).le,
        (le_abs_self _).trans (hCb x)⟩).trans (le_max_left _ _))
  exact fisher_bound_of_resolvent_test μ F₀ F hlam (.of_forall hF₀pos) (.of_forall hFlo)
    (bm_integrable μ hF₀) (bm_integrable μ hF) hF₀log
    (bm_integrable μ (bm_mul hF hlogb))
    (bm_integrable μ (bm_mul (bm_sub hF₀ hF) hlogb)) hmass htest

private lemma tilt_ae (μ : Measure X) (w : X → ℝ) (M : ℝ)
    {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ x ∂normalizedTilt μ w M, p x :=
  (withDensity_absolutelyContinuous μ _).ae_le hp

/-- The tested weighted-energy inequality in the manuscript follows from
the two primitive weak equations and diffusion product calculus. In
particular it is not a hypothesis supplied to the comparison theorem. -/
theorem abstract_weighted_energy_reduction (μ : Measure X) [IsProbabilityMeasure μ]
    (D : DiffusionCalculus μ) (w F₀ F h κ : X → ℝ)
    (hw : BoundedMeasurable w) (hF₀b : BoundedMeasurable F₀)
    (hFb : BoundedMeasurable F) (hhb : BoundedMeasurable h)
    (hκb : BoundedMeasurable κ)
    (hF₀lo : ∀ x, 1 ≤ F₀ x) (hFlo : ∀ x, 1 ≤ F x)
    (hhhi : ∀ x, h x ≤ 1) (hκlo : ∀ x, 0 ≤ κ x)
    (hFdom : F ∈ D.domain) (hhdom : h ∈ D.domain)
    {lam M : ℝ} (hlam : 0 ≤ lam) (hM : 0 < M)
    (hMass : (∫ x, Real.exp (w x) ∂μ) = M)
    (hbase : ∀ v ∈ D.domain, BoundedMeasurable v →
      (∫ x, D.gamma F v x ∂μ) = lam*∫ x, (F₀ x-F x)*v x ∂μ)
    (hkilled : ∀ v ∈ D.domain, BoundedMeasurable v →
      (∫ x, D.gamma h v x ∂normalizedTilt μ w M) +
        (∫ x, (lam+κ x)*h x*v x ∂normalizedTilt μ w M) =
          ∫ x, κ x*v x ∂normalizedTilt μ w M) :
    let ν := normalizedTilt μ w M
    (∫ x, F x*D.gamma h h x ∂ν) + lam/2*(∫ x, F x*h x^2 ∂ν) ≤
      (∫ x, κ x*F x ∂ν) +
        lam/2*|∫ x, tiltDefect w x*(F x-1)*h x^2 ∂ν| +
          |∫ x, tiltDefect w x*h x*D.gamma F h x ∂ν| := by
  dsimp only
  let ν := normalizedTilt μ w M
  let : IsProbabilityMeasure ν := normalizedTilt_probability μ w hM
    (bm_integrable μ (bm_exp hw)) hMass
  let k := tiltDefect w
  let A := ∫ x, F x*h x^2 ∂ν
  let B := ∫ x, F x*D.gamma h h x ∂ν
  let C := ∫ x, k x*h x*D.gamma F h x ∂ν
  let K := ∫ x, κ x*F x*h x^2 ∂ν
  let S := ∫ x, κ x*F x ∂ν
  let Z := ∫ x, Real.exp (-w x)*(lam*(F₀ x-F x))*h x^2 ∂ν
  let cross := ∫ x, h x*D.gamma F h x ∂ν
  have hk := bm_defect hw
  have hiΓ := tilt_integrable μ hw hM (D.integrable F hFdom h hhdom)
  have hihΓ := bm_mul_integrable ν hhb hiΓ
  have hiB := bm_mul_integrable ν hFb
    (tilt_integrable μ hw hM (D.integrable h hhdom h hhdom))
  have hiC : Integrable (fun x => k x*h x*D.gamma F h x) ν :=
    bm_mul_integrable ν (bm_mul hk hhb) hiΓ
  have hiA := bm_integrable ν (bm_mul hFb (bm_sq hhb))
  have hiK := bm_integrable ν (bm_mul (bm_mul hκb hFb) (bm_sq hhb))
  have hiZ := bm_integrable ν
    (bm_mul (bm_mul (bm_exp (bm_neg hw))
      (bm_mul (bm_const lam) (bm_sub hF₀b hFb))) (bm_sq hhb))
  have hiDef := bm_integrable ν
    (bm_mul (bm_mul hk (bm_sub hFb (bm_const 1))) (bm_sq hhb))
  have hhsq : (fun x => h x^2) ∈ D.domain := by
    simpa only [pow_two] using D.mul_mem h hhdom h hhdom hhb hhb
  have hFh : (fun x => F x*h x) ∈ D.domain := D.mul_mem F hFdom h hhdom hFb hhb
  have hsq : D.gamma F (fun x => h x^2) =ᵐ[μ]
      (fun x => 2*(h x*D.gamma F h x)) := by
    have hp := D.product_rule h hhdom h hhdom F hFdom hhb hhb
    simp only [← pow_two] at hp
    filter_upwards [hp,D.symmetric F hFdom _ hhsq,D.symmetric h hhdom F hFdom]
      with x hx hs hs'
    rw [hs,hx,hs']; ring
  have hprod : D.gamma h (fun x => F x*h x) =ᵐ[ν]
      (fun x => F x*D.gamma h h x+h x*D.gamma F h x) := by
    apply tilt_ae
    filter_upwards [D.symmetric h hhdom _ hFh,
      D.product_rule F hFdom h hhdom h hhdom hFb hhb] with x hs hp
    rw [hs,hp]
  have hprodInt : (∫ x, D.gamma h (fun y => F y*h y) x ∂ν) = B+cross := by
    rw [integral_congr_ae hprod]
    exact integral_add hiB hihΓ
  have hzeroInt : (∫ x, (lam+κ x)*h x*(F x*h x) ∂ν) = lam*A+K := by
    calc
      _ = ∫ x, lam*(F x*h x^2)+κ x*F x*h x^2 ∂ν := by
        apply integral_congr_ae; exact .of_forall fun x => by ring
      _ = _ := by
        rw [integral_add (hiA.const_mul lam) hiK,integral_const_mul]
  have hkill := hkilled _ hFh (bm_mul hFb hhb)
  change (∫ x, D.gamma h (fun y => F y*h y) x ∂ν)+
    (∫ x, (lam+κ x)*h x*(F x*h x) ∂ν) = ∫ x, κ x*(F x*h x) ∂ν at hkill
  rw [hprodInt,hzeroInt] at hkill
  have hrhs : (∫ x, κ x*(F x*h x) ∂ν) ≤ S := by
    apply integral_mono (bm_integrable ν (bm_mul hκb (bm_mul hFb hhb)))
      (bm_integrable ν (bm_mul hκb hFb))
    intro x
    have hp : 0 ≤ κ x*F x := mul_nonneg (hκlo x) (by linarith [hFlo x])
    nlinarith [mul_le_mul_of_nonneg_left (hhhi x) hp]
  have he : B+cross+lam*A+K ≤ S := by linarith
  have hΓsq := D.integrable F hFdom _ hhsq
  have hIBP : (∫ x, lam*(F₀ x-F x)*h x^2 ∂μ) =
      ∫ x, D.gamma F (fun y => h y^2) x ∂μ := by
    rw [hbase _ hhsq (bm_sq hhb)]
    calc
      _ = ∫ x, lam*((F₀ x-F x)*h x^2) ∂μ := by
        apply integral_congr_ae; exact .of_forall fun x => by ring
      _ = _ := integral_const_mul _ _
  have hc := exponential_tilt_weak_commutator μ w hw.1 hM
    (D.gamma F (fun y => h y^2)) (fun x => lam*(F₀ x-F x)*h x^2)
    hΓsq (bm_mul_integrable μ (bm_exp hw) hΓsq) hIBP
  have hcL : (∫ x, D.gamma F (fun y => h y^2) x ∂ν) = 2*cross := by
    rw [integral_congr_ae (tilt_ae μ w M hsq),integral_const_mul]
  have hcE : (∫ x, k x*D.gamma F (fun y => h y^2) x ∂ν) = 2*C := by
    calc
      _ = ∫ x, 2*(k x*h x*D.gamma F h x) ∂ν := by
        apply integral_congr_ae
        filter_upwards [tilt_ae μ w M hsq] with x hx
        rw [hx]; ring
      _ = _ := integral_const_mul _ _
  have hcZ : (∫ x, (1-tiltDefect w x)*(lam*(F₀ x-F x)*h x^2) ∂ν) = Z := by
    apply integral_congr_ae
    exact .of_forall fun x => by unfold tiltDefect; ring
  change (∫ x, D.gamma F (fun y => h y^2) x ∂ν) =
    (∫ x, (1-tiltDefect w x)*(lam*(F₀ x-F x)*h x^2) ∂ν)+
      (∫ x, k x*D.gamma F (fun y => h y^2) x ∂ν) at hc
  rw [hcL,hcZ,hcE] at hc
  have he' : B+(1/2 : ℝ)*Z+C+K+lam*A ≤ S := by linarith
  have hK0 : 0 ≤ K := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (mul_nonneg (hκlo x) (by linarith [hFlo x])) (sq_nonneg _)
  exact squareCommutator_energy_reduction ν lam hlam F₀ F h w (.of_forall hF₀lo)
    hiZ hiA hiDef B C K S hK0 he'

private lemma abstract_gamma_cross_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (D : DiffusionCalculus μ) (w F h v : X → ℝ)
    (hw : BoundedMeasurable w) (hFb : BoundedMeasurable F)
    (hvb : BoundedMeasurable v) (hFlo : ∀ x, 1 ≤ F x)
    (hvunit : ∀ x, v x^2 ≤ 1) (hFdom : F ∈ D.domain) (hhdom : h ∈ D.domain)
    {M ε J : ℝ} (hM : 0 < M)
    (hMass : (∫ x, Real.exp (w x) ∂μ) = M)
    (hsmall : (∫ x, (tiltDefect w x)^2*(D.gamma F F x/F x)
      ∂normalizedTilt μ w M) ≤ 2*ε*J) :
    |∫ x, tiltDefect w x*v x*D.gamma F h x ∂normalizedTilt μ w M| ≤
      Real.sqrt (2*ε*J*(∫ x, F x*D.gamma h h x ∂normalizedTilt μ w M)) := by
  let ν := normalizedTilt μ w M
  let : IsProbabilityMeasure ν := normalizedTilt_probability μ w hM
    (bm_integrable μ (bm_exp hw)) hMass
  let k := tiltDefect w
  let a := fun x => k x^2*(D.gamma F F x/F x)
  let b := fun x => F x*D.gamma h h x
  let c := fun x => k x*v x*D.gamma F h x
  have hΓFF := tilt_integrable μ hw hM (D.integrable F hFdom F hFdom)
  have hiA : Integrable a ν := by
    have hi := bm_mul_integrable ν (bm_mul (bm_sq (bm_defect hw)) (bm_inv hFb hFlo)) hΓFF
    convert hi using 1
    funext x
    dsimp only [a,k]
    ring
  have hiB : Integrable b ν := bm_mul_integrable ν hFb
    (tilt_integrable μ hw hM (D.integrable h hhdom h hhdom))
  have hiC : Integrable c ν := bm_mul_integrable ν (bm_mul (bm_defect hw) hvb)
    (tilt_integrable μ hw hM (D.integrable F hFdom h hhdom))
  have ha0 : ∀ᵐ x ∂ν, 0 ≤ a x := by
    filter_upwards [tilt_ae μ w M (D.nonnegative F hFdom)] with x hx
    exact mul_nonneg (sq_nonneg _) (div_nonneg hx (by linarith [hFlo x]))
  have hb0 : ∀ᵐ x ∂ν, 0 ≤ b x := by
    filter_upwards [tilt_ae μ w M (D.nonnegative h hhdom)] with x hx
    exact mul_nonneg (by linarith [hFlo x]) hx
  have hc2 : ∀ᵐ x ∂ν, c x^2 ≤ a x*b x := by
    filter_upwards [tilt_ae μ w M (gamma_cauchy μ D F h hFdom hhdom)] with x hx
    have h1 := mul_le_mul_of_nonneg_left (hvunit x)
      (mul_nonneg (sq_nonneg (k x)) (sq_nonneg (D.gamma F h x)))
    have h2 := mul_le_mul_of_nonneg_left hx (sq_nonneg (k x))
    have he : a x*b x = k x^2*(D.gamma F F x*D.gamma h h x) := by
      dsimp only [a,b]
      field_simp [show F x ≠ 0 by linarith [hFlo x]]
    rw [he]
    dsimp only [c]
    nlinarith
  have hcs := integral_cauchy_of_square_bound ν a b c hiA hiB hiC ha0 hb0 hc2
  have hp := mul_le_mul_of_nonneg_right hsmall (integral_nonneg_of_ae hb0)
  exact hcs.trans (Real.sqrt_le_sqrt hp)

/-- The source identity `eq:ent-source` is obtained from the weak equations
and the proved commutator. No derivative of the bounded measurable tilt
appears. -/
theorem abstract_resolvent_source_identity (μ : Measure X) [IsProbabilityMeasure μ]
    (D : DiffusionCalculus μ) (w F₀ F h κ : X → ℝ)
    (hw : BoundedMeasurable w) (hF₀b : BoundedMeasurable F₀)
    (hFb : BoundedMeasurable F) (hhb : BoundedMeasurable h)
    (hκb : BoundedMeasurable κ) (hFdom : F ∈ D.domain) (hhdom : h ∈ D.domain)
    {lam M : ℝ} (hM : 0 < M) (hMass : (∫ x, Real.exp (w x) ∂μ) = M)
    (hbase : ∀ v ∈ D.domain, BoundedMeasurable v →
      (∫ x, D.gamma F v x ∂μ) = lam*∫ x, (F₀ x-F x)*v x ∂μ)
    (hkilled : ∀ v ∈ D.domain, BoundedMeasurable v →
      (∫ x, D.gamma h v x ∂normalizedTilt μ w M) +
        (∫ x, (lam+κ x)*h x*v x ∂normalizedTilt μ w M) =
          ∫ x, κ x*v x ∂normalizedTilt μ w M) :
    let ν := normalizedTilt μ w M
    lam*(∫ x, (F₀ x-1)*h x ∂ν) =
      (∫ x, κ x*(F x-1)*(1-h x) ∂ν) +
        lam*(∫ x, tiltDefect w x*(F₀ x-F x)*h x ∂ν) -
          (∫ x, tiltDefect w x*D.gamma F h x ∂ν) := by
  dsimp only
  let ν := normalizedTilt μ w M
  let : IsProbabilityMeasure ν := normalizedTilt_probability μ w hM
    (bm_integrable μ (bm_exp hw)) hMass
  let k := tiltDefect w
  let f := fun x => F x-1
  have hfdom : f ∈ D.domain := D.domain.sub_mem hFdom D.one_mem
  have hfb : BoundedMeasurable f := bm_sub hFb (bm_const 1)
  have hγhf : D.gamma h f =ᵐ[ν] D.gamma F h := by
    apply tilt_ae
    filter_upwards [D.symmetric h hhdom f hfdom,
      gamma_one_zero μ D h hhdom] with x hs hz
    rw [hs]
    change D.gamma (F-(fun _ => 1)) h x = D.gamma F h x
    simp only [map_sub, LinearMap.sub_apply, Pi.sub_apply]
    rw [hz,sub_zero]
  have hΓ := D.integrable F hFdom h hhdom
  have hIBP : (∫ x, lam*(F₀ x-F x)*h x ∂μ) = ∫ x, D.gamma F h x ∂μ := by
    rw [hbase h hhdom hhb]
    calc
      _ = ∫ x, lam*((F₀ x-F x)*h x) ∂μ := by
        apply integral_congr_ae; exact .of_forall fun x => by ring
      _ = _ := integral_const_mul _ _
  have hc := exponential_tilt_weak_commutator μ w hw.1 hM
    (D.gamma F h) (fun x => lam*(F₀ x-F x)*h x)
    hΓ (bm_mul_integrable μ (bm_exp hw) hΓ) hIBP
  have hi := bm_integrable ν (bm_mul (bm_sub hF₀b hFb) hhb)
  have hik := bm_integrable ν (bm_mul (bm_mul (bm_defect hw) (bm_sub hF₀b hFb)) hhb)
  have hz : (∫ x, (1-k x)*(lam*(F₀ x-F x)*h x) ∂ν) =
      lam*(∫ x, (F₀ x-F x)*h x ∂ν) - lam*(∫ x, k x*(F₀ x-F x)*h x ∂ν) := by
    calc
      _ = ∫ x, lam*((F₀ x-F x)*h x)-lam*(k x*(F₀ x-F x)*h x) ∂ν := by
        apply integral_congr_ae; exact .of_forall fun x => by ring
      _ = _ := by
        rw [integral_sub (hi.const_mul lam) (hik.const_mul lam),
          integral_const_mul,integral_const_mul]
  have hkill := hkilled f hfdom hfb
  change (∫ x, D.gamma h f x ∂ν)+(∫ x, (lam+κ x)*h x*f x ∂ν) =
    ∫ x, κ x*f x ∂ν at hkill
  rw [integral_congr_ae hγhf] at hkill
  change (∫ x, D.gamma F h x ∂ν) = (∫ x, (1-k x)*(lam*(F₀ x-F x)*h x) ∂ν)+
    (∫ x, k x*D.gamma F h x ∂ν) at hc
  rw [hz] at hc
  have hzero : (∫ x, (lam+κ x)*h x*f x ∂ν) =
      lam*(∫ x, f x*h x ∂ν)+(∫ x, κ x*f x*h x ∂ν) := by
    calc
      _ = ∫ x, lam*(f x*h x)+κ x*f x*h x ∂ν := by
        apply integral_congr_ae; exact .of_forall fun x => by ring
      _ = _ := by
        rw [integral_add ((bm_integrable ν (bm_mul hfb hhb)).const_mul lam)
          (bm_integrable ν (bm_mul (bm_mul hκb hfb) hhb)),integral_const_mul]
  rw [hzero] at hkill
  have hright : (∫ x, κ x*(F x-1)*(1-h x) ∂ν) =
      (∫ x, κ x*f x ∂ν)-(∫ x, κ x*f x*h x ∂ν) := by
    calc
      _ = ∫ x, κ x*f x-κ x*f x*h x ∂ν := by
        apply integral_congr_ae; exact .of_forall fun x => by dsimp only [f]; ring
      _ = _ := integral_sub (bm_integrable ν (bm_mul hκb hfb))
        (bm_integrable ν (bm_mul (bm_mul hκb hfb) hhb))
  have hleft : (∫ x, (F₀ x-1)*h x ∂ν) =
      (∫ x, (F₀ x-F x)*h x ∂ν)+(∫ x, f x*h x ∂ν) := by
    calc
      _ = ∫ x, (F₀ x-F x)*h x+f x*h x ∂ν := by
        apply integral_congr_ae; exact .of_forall fun x => by dsimp only [f]; ring
      _ = _ := integral_add hi (bm_integrable ν (bm_mul hfb hhb))
  rw [hleft,hright]
  linarith

variable {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]

/-- The carré-du-champ part of (D4), on arbitrary probability spaces.
The resolvent part of (D4) is expressed by the frozen solution `f` in the
comparison theorem. -/
structure FrozenDiffusionCalculus (θ : Measure U) (μ : Measure E)
    extends DiffusionCalculus (θ.prod μ) where
  gammaFrozen : (E → ℝ) → (E → ℝ) → E → ℝ
  frozen : ∀ g v : E → ℝ,
    (fun z : U×E => g z.2) ∈ domain → (fun z : U×E => v z.2) ∈ domain →
    gamma (fun z : U×E => g z.2) (fun z : U×E => v z.2) =ᵐ[θ.prod μ]
      (fun z => gammaFrozen g v z.2)

private lemma bm_frozen {f : E → ℝ} (hf : BoundedMeasurable f) :
    BoundedMeasurable (fun z : U×E => f z.2) := by
  obtain ⟨hm,C,hC,hb⟩ := hf
  exact ⟨hm.comp measurable_snd,C,hC,fun z => hb z.2⟩

private lemma frozen_integral (θ : Measure U) (μ : Measure E)
    [IsProbabilityMeasure θ] [IsProbabilityMeasure μ]
    (f : E → ℝ) (hf : Integrable f μ) :
    (∫ z : U×E, f z.2 ∂θ.prod μ) = ∫ x, f x ∂μ := by
  rw [integral_prod _ (hf.comp_snd θ)]
  simp

/-- The exact bounded-density entropy--resolvent comparison. Every Fisher,
commutator, and weighted-energy estimate is proved from the primitive weak
equations and the two literal axis moments. Realization of these weak
solutions by the closed-form resolvents is a separate standard-mathematics
obligation; no energy conclusion is required here. -/
theorem bounded_density_resolvent_comparison
    (θ : Measure U) (μ : Measure E) [IsProbabilityMeasure θ] [IsProbabilityMeasure μ]
    (D : FrozenDiffusionCalculus θ μ) (w κ h : U×E → ℝ) (f₀ f : E → ℝ)
    (hw : BoundedMeasurable w) (hκb : BoundedMeasurable κ)
    (hhb : BoundedMeasurable h) (hf₀b : BoundedMeasurable f₀) (hfb : BoundedMeasurable f)
    (hf₀lo : ∀ x, 0 ≤ f₀ x) (hflo : ∀ x, 0 ≤ f x)
    (hf₀mass : (∫ x, f₀ x ∂μ) = 1) (hfmass : (∫ x, f x ∂μ) = 1)
    (hhlo : ∀ z, 0 ≤ h z) (hhhi : ∀ z, h z ≤ 1) (hκlo : ∀ z, 0 ≤ κ z)
    {lam η ε : ℝ} (hlam : 0 < lam) (hη : 0 ≤ η) (hηhalf : η ≤ 1/2) (hε : 0 ≤ ε)
    (haxis : ∀ᵐ x ∂μ, (∫ u, |Real.exp (w (u,x))-1| ∂θ) ≤ η)
    (haxis2 : ∀ᵐ x ∂μ,
      (∫ u, Real.exp (w (u,x))*(tiltDefect w (u,x))^2 ∂θ) ≤ ε)
    (hFdom : (fun z : U×E => 1+f z.2) ∈ D.domain) (hhdom : h ∈ D.domain)
    (hbase : ∀ v ∈ D.domain, BoundedMeasurable v →
      (∫ z, D.gamma (fun y : U×E => 1+f y.2) v z ∂θ.prod μ) =
        lam*∫ z, (f₀ z.2-f z.2)*v z ∂θ.prod μ)
    (hkilled : let M := ∫ z, Real.exp (w z) ∂θ.prod μ
      ∀ v ∈ D.domain, BoundedMeasurable v →
        (∫ z, D.gamma h v z ∂normalizedTilt (θ.prod μ) w M) +
          (∫ z, (lam+κ z)*h z*v z ∂normalizedTilt (θ.prod μ) w M) =
            ∫ z, κ z*v z ∂normalizedTilt (θ.prod μ) w M) :
    let M := ∫ z, Real.exp (w z) ∂θ.prod μ
    let ν := normalizedTilt (θ.prod μ) w M
    let H₀ := ∫ x, (1+f₀ x)*Real.log (1+f₀ x) ∂μ
    let R := lam⁻¹*∫ z, κ z*(1+f z.2) ∂ν
    (∫ z, f₀ z.2*h z ∂θ.prod μ) ≤
      4*η+5*Real.sqrt ε+R+2*Real.sqrt (ε*H₀*(R+ε*(1+H₀))) := by
  dsimp only
  let ρ := θ.prod μ
  let M := ∫ z, Real.exp (w z) ∂ρ
  let ν := normalizedTilt ρ w M
  let F : U×E → ℝ := fun z => 1+f z.2
  let F₀ : U×E → ℝ := fun z => 1+f₀ z.2
  let k := tiltDefect w
  let H₀ := ∫ x, (1+f₀ x)*Real.log (1+f₀ x) ∂μ
  let R := lam⁻¹*∫ z, κ z*F z ∂ν
  let A := ∫ z, F z*h z^2 ∂ν
  let B := ∫ z, F z*D.gamma h h z ∂ν
  let J := ∫ z, D.gamma F F z/F z ∂ρ
  have hew := bm_integrable ρ (bm_exp hw)
  have hMclose : |M-1| ≤ η := exponential_mass_close_one θ μ w hew rfl haxis
  have hMhalf : (1/2 : ℝ) ≤ M := by have ht := (abs_le.mp hMclose).1; linarith
  have hMp : 0 < M := by linarith
  let : IsProbabilityMeasure ν := normalizedTilt_probability ρ w hMp hew rfl
  have hFlo : ∀ z, 1 ≤ F z := fun z => by dsimp only [F]; linarith [hflo z.2]
  have hF₀lo : ∀ z, 1 ≤ F₀ z := fun z => by dsimp only [F₀]; linarith [hf₀lo z.2]
  have hFb : BoundedMeasurable F := bm_add (bm_const 1) (bm_frozen hfb)
  have hF₀b : BoundedMeasurable F₀ := bm_add (bm_const 1) (bm_frozen hf₀b)
  have hbase' : ∀ v ∈ D.domain, BoundedMeasurable v →
      (∫ z, D.gamma F v z ∂ρ) = lam*∫ z, (F₀ z-F z)*v z ∂ρ := by
    intro v hv hb
    rw [hbase v hv hb]
    congr 1
    apply integral_congr_ae
    exact .of_forall fun z => by dsimp only [F₀,F]; ring
  have hmassF : (∫ z, F₀ z ∂ρ) = ∫ z, F z ∂ρ := by
    rw [frozen_integral θ μ (fun x => 1+f₀ x)
      (bm_integrable μ (bm_add (bm_const 1) hf₀b)),
      frozen_integral θ μ (fun x => 1+f x)
      (bm_integrable μ (bm_add (bm_const 1) hfb)),
      integral_add (integrable_const _) (bm_integrable μ hf₀b),
      integral_add (integrable_const _) (bm_integrable μ hfb),hf₀mass,hfmass]
  have hFisher : J ≤ lam*H₀ := by
    have hh := abstract_resolvent_fisher_bound ρ D.toDiffusionCalculus F₀ F hF₀b hFb
      (fun z => by linarith [hF₀lo z]) hFlo hFdom hlam.le hmassF hbase'
    have he : (∫ z, F₀ z*Real.log (F₀ z) ∂ρ) = H₀ :=
      frozen_integral θ μ _ (bm_integrable μ (bm_mul (bm_add (bm_const 1) hf₀b)
        (bm_log (bm_add (bm_const 1) hf₀b) (fun x => by linarith [hf₀lo x]))))
    rw [he] at hh
    exact hh
  have hJ0 : 0 ≤ J := by
    apply integral_nonneg_of_ae
    filter_upwards [D.nonnegative F hFdom] with z hz
    exact div_nonneg hz (by linarith [hFlo z])
  have hH0 : 0 ≤ H₀ := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (by linarith [hf₀lo x]) (Real.log_nonneg (by linarith [hf₀lo x]))
  have hR0 : 0 ≤ R := by
    apply mul_nonneg (inv_nonneg.mpr hlam.le)
    apply integral_nonneg
    intro z
    exact mul_nonneg (hκlo z) (by linarith [hFlo z])
  have hA0 : 0 ≤ A := integral_nonneg fun z =>
    mul_nonneg (by linarith [hFlo z]) (sq_nonneg _)
  have hB0 : 0 ≤ B := by
    apply integral_nonneg_of_ae
    filter_upwards [tilt_ae ρ w M (D.nonnegative h hhdom)] with z hz
    exact mul_nonneg (by linarith [hFlo z]) hz
  have hExpAxis := axis_exponential_mean_le θ μ w hew haxis
  have project (g : E → ℝ) (hg : BoundedMeasurable g) (hg0 : ∀ x, 0 ≤ g x)
      (hgmass : (∫ x, g x ∂μ) = 1) :
      (∫ z, g z.2 ∂ν) ≤ 3 ∧ (∫ z, k z^2*g z.2 ∂ν) ≤ 2*ε := by
    have h1 := exponential_tilt_frozen_projection θ μ w hw.1 hη hηhalf
      (show 1-η ≤ M by have ht := (abs_le.mp hMclose).1; linarith)
      g (bm_integrable μ hg) (.of_forall hg0)
      (bm_integrable ρ (bm_mul (bm_exp hw) (bm_frozen hg))) hExpAxis
    have h2 := tiltDefect_square_projection θ μ w hw.1 hMhalf hε
      g (bm_integrable μ hg) (.of_forall hg0)
      (bm_integrable ρ (bm_mul (bm_mul (bm_exp hw) (bm_sq (bm_defect hw)))
        (bm_frozen hg))) haxis2
    rw [hgmass,mul_one] at h1 h2
    exact ⟨h1,h2⟩
  obtain ⟨hf₀tilt,hkf₀⟩ := project f₀ hf₀b hf₀lo hf₀mass
  obtain ⟨hftilt,hkf⟩ := project f hfb hflo hfmass
  let j : E → ℝ := fun x => D.gammaFrozen (fun y => 1+f y) (fun y => 1+f y) x/(1+f x)
  have hjrep : (fun z => D.gamma F F z/F z) =ᵐ[ρ] (fun z => j z.2) := by
    filter_upwards [D.frozen (fun x => 1+f x) (fun x => 1+f x) hFdom hFdom]
      with z hz
    exact congrArg (fun a => a/F z) hz
  have hjprod : Integrable (fun z : U×E => j z.2) ρ := by
    have hi := bm_mul_integrable ρ (bm_inv hFb hFlo) (D.integrable F hFdom F hFdom)
    have hi' : Integrable (fun z => D.gamma F F z/F z) ρ := by
      convert hi using 1; funext z; ring
    exact hi'.congr hjrep
  have hji : Integrable j μ := hjprod.of_comp_snd (by exact NeZero.ne θ)
  have hj0 : ∀ᵐ x ∂μ, 0 ≤ j x := by
    have hp : ∀ᵐ z ∂ρ, 0 ≤ j z.2 := by
      filter_upwards [hjrep,D.nonnegative F hFdom] with z hz hp
      rw [← hz]
      exact div_nonneg hp (by linarith [hFlo z])
    obtain ⟨u,hu⟩ := (Measure.ae_ae_of_ae_prod hp).exists
    exact hu
  have hjmass : (∫ x, j x ∂μ) = J := by
    rw [← frozen_integral θ μ j hji,← integral_congr_ae hjrep]
  have hsmall : (∫ z, k z^2*(D.gamma F F z/F z) ∂ν) ≤ 2*ε*J := by
    have hi := bm_mul_integrable ρ (bm_mul (bm_exp hw) (bm_sq (bm_defect hw))) hjprod
    have hs := tiltDefect_square_projection θ μ w hw.1 hMhalf hε j hji hj0 hi haxis2
    rw [hjmass] at hs
    have he : (fun z => k z^2*(D.gamma F F z/F z)) =ᵐ[ν]
        (fun z => k z^2*j z.2) := by
      filter_upwards [tilt_ae ρ w M hjrep] with z hz
      rw [hz]
    rw [integral_congr_ae he]
    exact hs
  have hcross (v : U×E → ℝ) (hv : BoundedMeasurable v) (hv2 : ∀ z, v z^2 ≤ 1) :=
    abstract_gamma_cross_bound ρ D.toDiffusionCalculus w F h v hw hFb hv hFlo hv2
      hFdom hhdom hMp rfl hsmall
  have hh2 : ∀ z, h z^2 ≤ 1 := fun z => by
    nlinarith [mul_nonneg (hhlo z) (sub_nonneg.mpr (hhhi z))]
  have hcrossh := hcross h hhb hh2
  have hcross1 := hcross (fun _ => 1) (bm_const 1) (fun _ => by norm_num)
  simp only [mul_one] at hcross1
  have hdef : |∫ z, k z*(F z-1)*h z^2 ∂ν| ≤ Real.sqrt (2*ε*A) := by
    have hc := weighted_defect_square_commutator_cauchy ν k F h
      (bm_defect hw).1.aestronglyMeasurable hFb.1.aestronglyMeasurable
      hhb.1.aestronglyMeasurable (.of_forall hFlo) (.of_forall fun z => ⟨hhlo z,hhhi z⟩)
      (bm_integrable ν (bm_mul (bm_sq (bm_defect hw)) (bm_sub hFb (bm_const 1))))
      (bm_integrable ν (bm_mul hFb (bm_sq hhb)))
    have hsf : (∫ z, k z^2*(F z-1) ∂ν) ≤ 2*ε := by
      simpa only [F,add_sub_cancel_left] using hkf
    exact hc.trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hsf hA0))
  have henergy := abstract_weighted_energy_reduction ρ D.toDiffusionCalculus w F₀ F h κ
    hw hF₀b hFb hhb hκb hF₀lo hFlo hhhi hκlo hFdom hhdom hlam.le hMp rfl hbase' hkilled
  have hRmass : (∫ z, κ z*F z ∂ν) = lam*R := by
    dsimp only [R]; field_simp
  change B+lam/2*A ≤ (∫ z, κ z*F z ∂ν)+
    lam/2*|∫ z, k z*(F z-1)*h z^2 ∂ν|+|∫ z, k z*h z*D.gamma F h z ∂ν| at henergy
  rw [hRmass] at henergy
  have henergy' : B+lam/2*A ≤ lam*R+lam/2*Real.sqrt (2*ε*A)+Real.sqrt (2*ε*J*B) := by
    have hh := mul_le_mul_of_nonneg_left hdef (by positivity : 0 ≤ lam/2)
    linarith
  have hlast := resolvent_commutator_error_bound hlam hA0 hB0 hε hJ0 hH0 hR0 hFisher henergy'
  have hsource := abstract_resolvent_source_identity ρ D.toDiffusionCalculus w F₀ F h κ
    hw hF₀b hFb hhb hκb hFdom hhdom hMp rfl hbase' hkilled
  have hzero := density_defect_le_five_sqrt ν k (fun z => f₀ z.2) (fun z => f z.2) h
    (bm_integrable ν (bm_frozen hf₀b)) (bm_integrable ν (bm_frozen hfb))
    (bm_integrable ν (bm_mul (bm_sq (bm_defect hw)) (bm_frozen hf₀b)))
    (bm_integrable ν (bm_mul (bm_sq (bm_defect hw)) (bm_frozen hfb)))
    (bm_integrable ν (bm_mul (bm_mul (bm_defect hw)
      (bm_sub (bm_frozen hf₀b) (bm_frozen hfb))) hhb))
    (.of_forall fun z => hf₀lo z.2) (.of_forall fun z => hflo z.2)
    (.of_forall fun z => ⟨hhlo z,hhhi z⟩) hε hf₀tilt hftilt hkf₀ hkf
  have hzero' : |∫ z, k z*(F₀ z-F z)*h z ∂ν| ≤ 5*Real.sqrt ε := by
    convert hzero using 1
    congr 1
    apply integral_congr_ae
    exact .of_forall fun z => by dsimp only [F₀,F]; ring
  have hsourceR : (∫ z, κ z*(F z-1)*(1-h z) ∂ν) ≤ lam*R := by
    rw [← hRmass]
    apply integral_mono
      (bm_integrable ν (bm_mul (bm_mul hκb (bm_sub hFb (bm_const 1)))
        (bm_sub (bm_const 1) hhb))) (bm_integrable ν (bm_mul hκb hFb))
    intro z
    change κ z*(F z-1)*(1-h z) ≤ κ z*F z
    have hp : 0 ≤ κ z*(F z-1) := mul_nonneg (hκlo z) (by linarith [hFlo z])
    nlinarith [mul_nonneg hp (hhlo z),hκlo z]
  have hpair : (∫ z, f₀ z.2*h z ∂ν) ≤ R+5*Real.sqrt ε+Real.sqrt (2*ε*J*B)/lam := by
    have hsource' : lam*(∫ z, f₀ z.2*h z ∂ν) =
        (∫ z, κ z*(F z-1)*(1-h z) ∂ν)+lam*(∫ z, k z*(F₀ z-F z)*h z ∂ν)-
          (∫ z, k z*D.gamma F h z ∂ν) := by
      simpa only [F₀,add_sub_cancel_left] using hsource
    have hz := le_abs_self (∫ z, k z*(F₀ z-F z)*h z ∂ν)
    have hc := neg_le_abs (∫ z, k z*D.gamma F h z ∂ν)
    have hm := mul_le_mul_of_nonneg_left (hz.trans hzero') hlam.le
    apply (mul_le_mul_iff_right₀ hlam).mp
    have he : lam*(R+5*Real.sqrt ε+Real.sqrt (2*ε*J*B)/lam) =
        lam*(R+5*Real.sqrt ε)+Real.sqrt (2*ε*J*B) := by field_simp
    rw [he]
    linarith
  have hinitial := normalizedTilt_initialDensity_l1_le_four_eta θ μ w hw.1 hew f₀
    (bm_integrable μ hf₀b) hf₀lo hf₀mass (bm_integrable ρ (bm_frozen hf₀b))
    (bm_integrable ρ (bm_mul (bm_exp hw) (bm_frozen hf₀b))) hη hηhalf haxis
  let q : U×E → ℝ := fun z => M*Real.exp (-w z)*f₀ z.2
  have hqb : BoundedMeasurable q := bm_mul (bm_mul (bm_const M) (bm_exp (bm_neg hw)))
    (bm_frozen hf₀b)
  have hinit : (∫ z, f₀ z.2*h z ∂ρ) ≤ (∫ z, f₀ z.2*h z ∂ν)+4*η := by
    rw [← normalizedTilt_initial_pairing ρ w hw.1 hMp (fun z => f₀ z.2) h]
    have hm := integral_mono (bm_integrable ν (bm_mul hqb hhb))
      ((bm_integrable ν (bm_mul (bm_frozen hf₀b) hhb)).add
        (bm_integrable ν (bm_abs (bm_sub hqb (bm_frozen hf₀b)))))
      (fun z => by
        change q z*h z ≤ f₀ z.2*h z+|q z-f₀ z.2|
        have hh := mul_le_mul_of_nonneg_right (le_abs_self (q z-f₀ z.2)) (hhlo z)
        have hh' := mul_le_mul_of_nonneg_left (hhhi z) (abs_nonneg (q z-f₀ z.2))
        nlinarith)
    change (∫ x, q x*h x ∂ν) ≤ ∫ x, f₀ x.2*h x+|q x-f₀ x.2| ∂ν at hm
    rw [integral_add (bm_integrable ν (bm_mul (bm_frozen hf₀b) hhb))
      (bm_integrable ν (bm_abs (bm_sub hqb (bm_frozen hf₀b))))] at hm
    exact hm.trans (add_le_add_right hinitial _)
  linarith

private lemma shifted_entropy_dominator {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≤ 2*b) :
    0 ≤ (1+a)*Real.log (1+a) ∧
    (1+a)*Real.log (1+a) ≤ 2*((1+b)*Real.log (1+b))+2*(1+b) := by
  have hla : 0 ≤ Real.log (1+a) := Real.log_nonneg (by linarith)
  have hcoef : 1+a ≤ 2*(1+b) := by linarith
  have hl := Real.log_le_log (by linarith : 0 < 1+a) hcoef
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : 1+b ≠ 0)] at hl
  have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog : Real.log (1+a) ≤ 1+Real.log (1+b) := by linarith
  refine ⟨mul_nonneg (by linarith) hla, ?_⟩
  have hm := mul_le_mul hcoef hlog hla (by positivity : 0 ≤ 2*(1+b))
  exact hm.trans_eq (by ring)

/-- The manuscript's unbounded-density approximation is proved by
normalized truncation and dominated convergence. Both L¹ and shifted
entropy converge; no approximation theorem is a literature premise. -/
theorem finite_entropy_density_approximation (μ : Measure E) [IsProbabilityMeasure μ]
    (I : E → ℝ) (hI : Measurable I) (hI0 : ∀ x, 0 ≤ I x)
    (hmass : (∫ x, I x ∂μ) = 1)
    (hEnt : Integrable (fun x => (1+I x)*Real.log (1+I x)) μ) :
    ∃ q : ℕ → E → ℝ,
      (∀ n, BoundedMeasurable (q n) ∧ (∀ x, 0 ≤ q n x) ∧ (∫ x, q n x ∂μ) = 1) ∧
      Tendsto (fun n => ∫ x, |q n x-I x| ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x, (1+q n x)*Real.log (1+q n x) ∂μ) atTop
        (𝓝 (∫ x, (1+I x)*Real.log (1+I x) ∂μ)) := by
  have hIi : Integrable I μ := Integrable.of_integral_ne_zero (by rw [hmass]; norm_num)
  let u : ℕ → E → ℝ := fun n x => min (I x) ((n : ℝ)+1)
  let a : ℕ → ℝ := fun n => ∫ x, u n x ∂μ
  let q : ℕ → E → ℝ := fun n x => u n x/a n
  have hu0 (n : ℕ) (x : E) : 0 ≤ u n x := le_min (hI0 x) (by positivity)
  have huB (n : ℕ) : BoundedMeasurable (u n) := by
    refine ⟨hI.min measurable_const,(n : ℝ)+1,by positivity,fun x => ?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg (hu0 n x)]
    exact min_le_right _ _
  have hui (n : ℕ) : Integrable (u n) μ := bm_integrable μ (huB n)
  have ha0 (n : ℕ) : 0 < a n := by
    have han : 0 ≤ a n := integral_nonneg (hu0 n)
    by_contra hneg
    have haz : a n = 0 := le_antisymm (le_of_not_gt hneg) han
    have huz := (integral_eq_zero_iff_of_nonneg (hu0 n) (hui n)).mp haz
    have hIz : I =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [huz] with x hx
      by_contra hx0
      have hIp : 0 < I x := lt_of_le_of_ne (hI0 x) (Ne.symm hx0)
      have hup : 0 < u n x := lt_min hIp (by positivity)
      change u n x = 0 at hx
      linarith
    have hzero : (∫ x, I x ∂μ) = 0 := by rw [integral_congr_ae hIz,integral_zero]
    linarith
  have hqB (n : ℕ) : BoundedMeasurable (q n) := by
    refine ⟨(huB n).1.div_const _,((n : ℝ)+1)/a n,
      div_nonneg (by positivity) (ha0 n).le,fun x => ?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hu0 n x) (ha0 n).le)]
    exact div_le_div_of_nonneg_right (min_le_right _ _) (ha0 n).le
  have hq0 (n : ℕ) (x : E) : 0 ≤ q n x := div_nonneg (hu0 n x) (ha0 n).le
  have hqm (n : ℕ) : (∫ x, q n x ∂μ) = 1 := by
    change (∫ x, u n x/a n ∂μ) = 1
    rw [integral_div]
    exact div_self (ha0 n).ne'
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hut (x : E) : Tendsto (fun n => u n x) atTop (𝓝 (I x)) := by
    have he : (fun n => u n x) =ᶠ[atTop] (fun _ => I x) :=
      (hnat.eventually_ge_atTop (I x)).mono (fun n hn => min_eq_left hn)
    exact Tendsto.congr' he.symm tendsto_const_nhds
  have hat : Tendsto a atTop (𝓝 1) := by
    have ht := tendsto_integral_of_dominated_convergence (μ := μ) I
      (fun n => (huB n).1.aestronglyMeasurable) hIi
      (fun n => .of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hu0 n x)]
        exact min_le_left _ _) (.of_forall hut)
    simpa only [hmass] using ht
  have hqt (x : E) : Tendsto (fun n => q n x) atTop (𝓝 (I x)) := by
    have ht := (hut x).div hat (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun n => u n x/a n) atTop (𝓝 (I x/1)) at ht
    simpa only [div_one] using ht
  have hhalf : ∀ᶠ n in atTop, (1/2 : ℝ) ≤ a n :=
    (hat.eventually (Ioi_mem_nhds (by norm_num : (1/2 : ℝ) < 1))).mono (fun _ hn => hn.le)
  have hqle (n : ℕ) (hn : (1/2 : ℝ) ≤ a n) (x : E) : q n x ≤ 2*I x := by
    apply (div_le_iff₀ (ha0 n)).mpr
    have hmul := mul_le_mul_of_nonneg_left hn (hI0 x)
    have hmin := min_le_left (I x) ((n : ℝ)+1)
    nlinarith
  have hl1 : Tendsto (fun n => ∫ x, |q n x-I x| ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ) (fun x => 3*I x)
      (.of_forall fun n => ((hqB n).1.sub hI).abs.aestronglyMeasurable)
      (hhalf.mono fun n hn => .of_forall fun x => by
        rw [Real.norm_eq_abs,abs_abs]
        calc
          |q n x-I x| ≤ |q n x|+|I x| := abs_sub _ _
          _ ≤ 3*I x := by rw [abs_of_nonneg (hq0 n x),abs_of_nonneg (hI0 x)]; linarith [hqle n hn x])
      (hIi.const_mul 3)
      (.of_forall fun x => by
        simpa only [Pi.sub_apply,sub_self,abs_zero] using
          ((hqt x).sub (tendsto_const_nhds (x := I x))).abs)
    simpa only [Pi.sub_apply,integral_zero] using ht
  let b : E → ℝ := fun x => 2*((1+I x)*Real.log (1+I x))+2*(1+I x)
  have hbi : Integrable b μ :=
    (hEnt.const_mul 2).add (((integrable_const (μ := μ) (1 : ℝ)).add hIi).const_mul 2)
  have hent : Tendsto (fun n => ∫ x, (1+q n x)*Real.log (1+q n x) ∂μ) atTop
      (𝓝 (∫ x, (1+I x)*Real.log (1+I x) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence b
    · exact .of_forall fun n => ((measurable_const.add (hqB n).1).mul
        (measurable_const.add (hqB n).1).log).aestronglyMeasurable
    · exact hhalf.mono fun n hn => .of_forall fun x => by
        have hd := shifted_entropy_dominator (hq0 n x) (hI0 x) (hqle n hn x)
        rw [Real.norm_eq_abs,abs_of_nonneg hd.1]
        exact hd.2
    · exact hbi
    · exact .of_forall fun x => (Real.continuous_mul_log.tendsto (1+I x)).comp
        ((tendsto_const_nhds (x := (1 : ℝ))).add (hqt x))
  exact ⟨q,(fun n => ⟨hqB n,hq0 n,hqm n⟩),hl1,hent⟩

/-- Standard realization facts for the conservative closed-form resolvent
`r = lam (lam + A₀)⁻¹`, including its L¹ extension. This is a `Prop`
interface, not an assertion of the entropy comparison. The underlying
closed-form/Markov correspondence is Fukushima--Oshima--Takeda (2011),
Sections 1.3--1.4; literal operator construction from the represented domain
is not proved in this module. -/
structure ClosedFormL1ResolventFacts (θ : Measure U) (μ : Measure E)
    (D : FrozenDiffusionCalculus θ μ) (lam : ℝ) (r : (E → ℝ) → E → ℝ) : Prop where
  integrable : ∀ g : E → ℝ, Integrable g μ → Integrable (r g) μ
  contraction : ∀ g v : E → ℝ, Integrable g μ → Integrable v μ →
    (∫ x, |r g x-r v x| ∂μ) ≤ ∫ x, |g x-v x| ∂μ
  bounded : ∀ g : E → ℝ, BoundedMeasurable g → (∀ x, 0 ≤ g x) →
    (∫ x, g x ∂μ) = 1 →
    BoundedMeasurable (r g) ∧ (∀ x, 0 ≤ r g x) ∧ (∫ x, r g x ∂μ) = 1 ∧
      (fun z : U×E => 1+r g z.2) ∈ D.domain ∧
        (∀ v ∈ D.domain, BoundedMeasurable v →
          (∫ z, D.gamma (fun y : U×E => 1+r g y.2) v z ∂θ.prod μ) =
            lam*∫ z, (g z.2-r g z.2)*v z ∂θ.prod μ)

/-- Standard weak realization and Markov bounds for the killed resolvent
`h = (lam + A_w + κ)⁻¹ κ`. These are primitive operator facts; no Fisher,
weighted-energy, moment, or entropy conclusion is part of this interface. -/
structure ClosedFormKilledResolventFacts (θ : Measure U) (μ : Measure E)
    (D : FrozenDiffusionCalculus θ μ) (w κ : U×E → ℝ) (lam : ℝ)
    (h : U×E → ℝ) : Prop where
  bounded : BoundedMeasurable h
  nonnegative : ∀ z, 0 ≤ h z
  le_one : ∀ z, h z ≤ 1
  domain_mem : h ∈ D.domain
  equation : let M := ∫ z, Real.exp (w z) ∂θ.prod μ
    ∀ v ∈ D.domain, BoundedMeasurable v →
      (∫ z, D.gamma h v z ∂normalizedTilt (θ.prod μ) w M) +
        (∫ z, (lam+κ z)*h z*v z ∂normalizedTilt (θ.prod μ) w M) =
          ∫ z, κ z*v z ∂normalizedTilt (θ.prod μ) w M

private lemma pairing_tendsto_of_l1 (μ : Measure X) (b : X → ℝ)
    (hb : BoundedMeasurable b) (g : ℕ → X → ℝ) (f : X → ℝ)
    (hg : ∀ n, Integrable (g n) μ) (hf : Integrable f μ)
    (hlim : Tendsto (fun n => ∫ x, |g n x-f x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, b x*g n x ∂μ) atTop (𝓝 (∫ x, b x*f x ∂μ)) := by
  obtain ⟨hbm,C,hC,hbC⟩ := hb
  have hbn : BoundedMeasurable b := ⟨hbm,C,hC,hbC⟩
  have hbound (n : ℕ) : |(∫ x, b x*g n x ∂μ)-(∫ x, b x*f x ∂μ)| ≤
      C*(∫ x, |g n x-f x| ∂μ) := by
    rw [← integral_sub (bm_mul_integrable μ hbn (hg n)) (bm_mul_integrable μ hbn hf)]
    calc
      _ = |∫ x, b x*(g n x-f x) ∂μ| := by
        congr 1; apply integral_congr_ae; exact .of_forall fun x => by ring
      _ ≤ ∫ x, |b x*(g n x-f x)| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, C*|g n x-f x| ∂μ := by
        apply integral_mono (bm_mul_integrable μ hbn ((hg n).sub hf)).abs
          (((hg n).sub hf).abs.const_mul C)
        intro x
        change |b x*(g n x-f x)| ≤ C*|g n x-f x|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hbC x)
          (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  have ht : Tendsto (fun n => |(∫ x, b x*g n x ∂μ)-(∫ x, b x*f x ∂μ)|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound
      (by simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hlim)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using ht)

private lemma tilt_pairing_tendsto_of_l1 (μ : Measure X) (w b : X → ℝ)
    (hw : BoundedMeasurable w) (hb : BoundedMeasurable b) {M : ℝ} (hM : 0 < M)
    (g : ℕ → X → ℝ) (f : X → ℝ) (hg : ∀ n, Integrable (g n) μ) (hf : Integrable f μ)
    (hlim : Tendsto (fun n => ∫ x, |g n x-f x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, b x*g n x ∂normalizedTilt μ w M) atTop
      (𝓝 (∫ x, b x*f x ∂normalizedTilt μ w M)) := by
  have ht := (pairing_tendsto_of_l1 μ (fun x => Real.exp (w x)*b x)
    (bm_mul (bm_exp hw) hb) g f hg hf hlim).div_const M
  simpa only [integral_normalizedTilt μ w hw.1 hM,mul_assoc] using ht

/-- The printed entropy comparison for every finite-entropy density,
including unbounded densities. The only literature premises are standard
closed-form resolvent realization and L¹ contraction; all quantitative
estimates and the approximation are proved in this file. -/
theorem entropy_resolvent_comparison
    (θ : Measure U) (μ : Measure E) [IsProbabilityMeasure θ] [IsProbabilityMeasure μ]
    (D : FrozenDiffusionCalculus θ μ) (w κ h : U×E → ℝ)
    (r : (E → ℝ) → E → ℝ) (f₀ : E → ℝ)
    (hw : BoundedMeasurable w) (hκb : BoundedMeasurable κ) (hκlo : ∀ z, 0 ≤ κ z)
    (hf₀ : Measurable f₀) (hf₀lo : ∀ x, 0 ≤ f₀ x) (hf₀mass : (∫ x, f₀ x ∂μ) = 1)
    (hEnt : Integrable (fun x => (1+f₀ x)*Real.log (1+f₀ x)) μ)
    {lam η ε : ℝ} (hlam : 0 < lam) (hηhalf : η ≤ 1/2)
    (haxis : ∀ᵐ x ∂μ, (∫ u, |Real.exp (w (u,x))-1| ∂θ) ≤ η)
    (haxis2 : ∀ᵐ x ∂μ,
      (∫ u, Real.exp (w (u,x))*(tiltDefect w (u,x))^2 ∂θ) ≤ ε)
    (hUnperturbed : ClosedFormL1ResolventFacts θ μ D lam r)
    (hKilled : ClosedFormKilledResolventFacts θ μ D w κ lam h) :
    let M := ∫ z, Real.exp (w z) ∂θ.prod μ
    let ν := normalizedTilt (θ.prod μ) w M
    let H₀ := ∫ x, (1+f₀ x)*Real.log (1+f₀ x) ∂μ
    let R := lam⁻¹*∫ z, κ z*(1+r f₀ z.2) ∂ν
    (∫ z, f₀ z.2*h z ∂θ.prod μ) ≤
      4*η+5*Real.sqrt ε+R+2*Real.sqrt (ε*H₀*(R+ε*(1+H₀))) := by
  have hf₀i : Integrable f₀ μ := Integrable.of_integral_ne_zero (by rw [hf₀mass]; norm_num)
  obtain ⟨q,hq,hql1,hqEnt⟩ := finite_entropy_density_approximation μ f₀ hf₀ hf₀lo hf₀mass hEnt
  have hη : 0 ≤ η := by
    obtain ⟨x,hx⟩ := haxis.exists
    exact (integral_nonneg (fun u => abs_nonneg _)).trans hx
  have hε : 0 ≤ ε := by
    obtain ⟨x,hx⟩ := haxis2.exists
    exact (integral_nonneg (fun u => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))).trans hx
  let ρ := θ.prod μ
  let M := ∫ z, Real.exp (w z) ∂ρ
  let ν := normalizedTilt ρ w M
  let H := ∫ x, (1+f₀ x)*Real.log (1+f₀ x) ∂μ
  let R (g : E → ℝ) := lam⁻¹*∫ z, κ z*(1+r g z.2) ∂ν
  have hMp : 0 < M := (normalizedTilt_probability_of_axis_moment θ μ w
    (bm_integrable ρ (bm_exp hw)) hηhalf haxis).1
  have hqi (n : ℕ) : Integrable (q n) μ := bm_integrable μ (hq n).1
  have hrqi (n : ℕ) : Integrable (r (q n)) μ := hUnperturbed.integrable _ (hqi n)
  have hrfi : Integrable (r f₀) μ := hUnperturbed.integrable _ hf₀i
  have hrL1 : Tendsto (fun n => ∫ x, |r (q n) x-r f₀ x| ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg fun x => abs_nonneg _)
      (fun n => hUnperturbed.contraction _ _ (hqi n) hf₀i) hql1
  have hql1prod : Tendsto (fun n => ∫ z : U×E, |q n z.2-f₀ z.2| ∂ρ) atTop (𝓝 0) := by
    convert hql1 using 1
    funext n
    exact frozen_integral θ μ _ ((hqi n).sub hf₀i).abs
  have hpair := pairing_tendsto_of_l1 ρ h hKilled.bounded
    (fun n z => q n z.2) (fun z => f₀ z.2)
    (fun n => (hqi n).comp_snd θ) (hf₀i.comp_snd θ) hql1prod
  have hpair' : Tendsto (fun n => ∫ z, q n z.2*h z ∂ρ) atTop
      (𝓝 (∫ z, f₀ z.2*h z ∂ρ)) := by simpa only [mul_comm] using hpair
  have hrL1prod : Tendsto
      (fun n => ∫ z : U×E, |(1+r (q n) z.2)-(1+r f₀ z.2)| ∂ρ) atTop (𝓝 0) := by
    convert hrL1 using 1
    funext n
    calc
      _ = ∫ z : U×E, |r (q n) z.2-r f₀ z.2| ∂ρ := by
        apply integral_congr_ae
        exact .of_forall fun z => by simp only [add_sub_add_left_eq_sub]
      _ = _ := frozen_integral θ μ _ ((hrqi n).sub hrfi).abs
  have hRlim : Tendsto (fun n => R (q n)) atTop (𝓝 (R f₀)) := by
    exact (tilt_pairing_tendsto_of_l1 ρ w κ hw hκb hMp
      (fun n z => 1+r (q n) z.2) (fun z => 1+r f₀ z.2)
      (fun n => (integrable_const (μ := ρ) (1 : ℝ)).add ((hrqi n).comp_snd θ))
      ((integrable_const (μ := ρ) (1 : ℝ)).add (hrfi.comp_snd θ)) hrL1prod).const_mul _
  have hroot := ((tendsto_const_nhds (x := ε)).mul hqEnt).mul
    (hRlim.add ((tendsto_const_nhds (x := ε)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add hqEnt)))
  have hright := ((tendsto_const_nhds (x := 4*η+5*Real.sqrt ε)).add hRlim).add
    (((Real.continuous_sqrt.tendsto _).comp hroot).const_mul 2)
  have hineq (n : ℕ) := by
    obtain ⟨hb,hn,hm⟩ := hq n
    obtain ⟨hrb,hrn,hrm,hdom,heq⟩ := hUnperturbed.bounded (q n) hb hn hm
    exact bounded_density_resolvent_comparison θ μ D w κ h (q n) (r (q n)) hw hκb
      hKilled.bounded hb hrb hn hrn hm hrm hKilled.nonnegative hKilled.le_one hκlo
      hlam hη hηhalf hε haxis haxis2 hdom hKilled.domain_mem heq hKilled.equation
  exact le_of_tendsto_of_tendsto hpair' hright (.of_forall hineq)

private lemma reference_rate_nonnegative
    (θ : Measure U) (μ : Measure E) [IsProbabilityMeasure θ] [IsProbabilityMeasure μ]
    (D : FrozenDiffusionCalculus θ μ) (w κ : U×E → ℝ) (r : (E → ℝ) → E → ℝ)
    (I : E → ℝ) (hw : BoundedMeasurable w) (hκb : BoundedMeasurable κ)
    (hκlo : ∀ z, 0 ≤ κ z) (hI : Measurable I) (hI0 : ∀ x, 0 ≤ I x)
    (hImass : (∫ x, I x ∂μ) = 1)
    (hEnt : Integrable (fun x => (1+I x)*Real.log (1+I x)) μ)
    {lam M : ℝ} (hlam : 0 < lam) (hM : 0 < M)
    (hr : ClosedFormL1ResolventFacts θ μ D lam r) :
    0 ≤ lam⁻¹*∫ z, κ z*(1+r I z.2) ∂normalizedTilt (θ.prod μ) w M := by
  have hIi : Integrable I μ := Integrable.of_integral_ne_zero (by rw [hImass]; norm_num)
  obtain ⟨q,hq,hql1,_⟩ := finite_entropy_density_approximation μ I hI hI0 hImass hEnt
  have hqi (n : ℕ) : Integrable (q n) μ := bm_integrable μ (hq n).1
  have hrqi (n : ℕ) : Integrable (r (q n)) μ := hr.integrable _ (hqi n)
  have hrIi : Integrable (r I) μ := hr.integrable _ hIi
  have hrl1 : Tendsto (fun n => ∫ x, |r (q n) x-r I x| ∂μ) atTop (𝓝 0) :=
    squeeze_zero (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun n => hr.contraction _ _ (hqi n) hIi) hql1
  have hp : Tendsto
      (fun n => ∫ z : U×E, |(1+r (q n) z.2)-(1+r I z.2)| ∂θ.prod μ) atTop (𝓝 0) := by
    convert hrl1 using 1
    funext n
    calc
      _ = ∫ z : U×E, |r (q n) z.2-r I z.2| ∂θ.prod μ := by
        apply integral_congr_ae
        exact .of_forall fun z => by simp only [add_sub_add_left_eq_sub]
      _ = _ := frozen_integral θ μ _ ((hrqi n).sub hrIi).abs
  have ht := (tilt_pairing_tendsto_of_l1 (θ.prod μ) w κ hw hκb hM
    (fun n z => 1+r (q n) z.2) (fun z => 1+r I z.2)
    (fun n => (integrable_const (μ := θ.prod μ) (1 : ℝ)).add ((hrqi n).comp_snd θ))
    ((integrable_const (μ := θ.prod μ) (1 : ℝ)).add (hrIi.comp_snd θ)) hp).const_mul lam⁻¹
  apply ge_of_tendsto ht
  exact .of_forall fun n => by
    obtain ⟨_,hn,_,_,_⟩ := hr.bounded (q n) (hq n).1 (hq n).2.1 (hq n).2.2
    apply mul_nonneg (inv_nonneg.mpr hlam.le)
    apply integral_nonneg
    intro z
    exact mul_nonneg (hκlo z) (by linarith [hn z.2])

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The standard Feynman--Kac identification for a specified process and
its actual exponential killing time, with zero at infinity. This explicit
`Prop` asserts only the killed-resolvent identification, never a numerical
entropy bound. The abstract measurable-space process construction and
identification have not been proved here; the usual reference is
Fukushima--Oshima--Takeda (2011), Section 6.1. -/
structure FeynmanKacResolventFacts (P : Measure Ω) (τ : Ω → ℝ≥0∞)
    (θ : Measure U) (μ : Measure E) (I : E → ℝ) (h : U×E → ℝ) (lam : ℝ) : Prop where
  identification : (∫ ω, killingLaplace τ (1/lam) ω ∂P) =
    ∫ z, I z.2*h z ∂θ.prod μ

/-- The exact numerical conclusions of `lem:ent-resolvent`, with a finite-entropy
initial density and a bounded measurable perturbation. All constants are
the printed constants, conditional on the primitive literature interfaces
for closed-form realization/L¹ contraction and Feynman--Kac identification.
Construction of the associated operators and actual killed process, and
their bridges to these interfaces, are not proved in this module. -/
theorem entropy_resolvent_transform_and_horizon
    (θ : Measure U) (μ : Measure E) [IsProbabilityMeasure θ] [IsProbabilityMeasure μ]
    (D : FrozenDiffusionCalculus θ μ) (w κ h : U×E → ℝ)
    (r : (E → ℝ) → E → ℝ) (f₀ : E → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (hw : BoundedMeasurable w) (hκb : BoundedMeasurable κ) (hκlo : ∀ z, 0 ≤ κ z)
    (hf₀ : Measurable f₀) (hf₀lo : ∀ x, 0 ≤ f₀ x) (hf₀mass : (∫ x, f₀ x ∂μ) = 1)
    (hEnt : Integrable (fun x => (1+f₀ x)*Real.log (1+f₀ x)) μ)
    {T η ε : ℝ} (hT : 0 < T) (hηhalf : η ≤ 1/2)
    (haxis : ∀ᵐ x ∂μ, (∫ u, |Real.exp (w (u,x))-1| ∂θ) ≤ η)
    (haxis2 : ∀ᵐ x ∂μ,
      (∫ u, Real.exp (w (u,x))*(tiltDefect w (u,x))^2 ∂θ) ≤ ε)
    (hUnperturbed : ClosedFormL1ResolventFacts θ μ D (1/T) r)
    (hKilled : ClosedFormKilledResolventFacts θ μ D w κ (1/T) h)
    (hFeynmanKac : FeynmanKacResolventFacts P τ θ μ f₀ h (1/T)) :
    let M := ∫ z, Real.exp (w z) ∂θ.prod μ
    let ν := normalizedTilt (θ.prod μ) w M
    let H₀ := ∫ x, (1+f₀ x)*Real.log (1+f₀ x) ∂μ
    let R := (1/T)⁻¹*∫ z, κ z*(1+r f₀ z.2) ∂ν
    (∫ ω, killingLaplace τ T ω ∂P) ≤
      4*η+5*Real.sqrt ε+R+2*Real.sqrt (ε*H₀*(R+ε*(1+H₀))) ∧
    P.real {ω | τ ω ≤ ENNReal.ofReal T} ≤
      14*(η+Real.sqrt ε+ε*(1+H₀)+R) := by
  dsimp only
  have hlam : 0 < 1/T := one_div_pos.mpr hT
  have heq := hFeynmanKac.identification
  simp only [one_div,inv_inv] at heq
  have hc := entropy_resolvent_comparison θ μ D w κ h r f₀ hw hκb hκlo
    hf₀ hf₀lo hf₀mass hEnt hlam hηhalf haxis haxis2 hUnperturbed hKilled
  have htransform := heq.le.trans hc
  refine ⟨htransform, ?_⟩
  have hη : 0 ≤ η := by
    obtain ⟨x,hx⟩ := haxis.exists
    exact (integral_nonneg (fun _ => abs_nonneg _)).trans hx
  have hε : 0 ≤ ε := by
    obtain ⟨x,hx⟩ := haxis2.exists
    exact (integral_nonneg (fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _))).trans hx
  have hH : 0 ≤ ∫ x, (1+f₀ x)*Real.log (1+f₀ x) ∂μ := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (by linarith [hf₀lo x]) (Real.log_nonneg (by linarith [hf₀lo x]))
  have hM : 0 < ∫ z, Real.exp (w z) ∂θ.prod μ :=
    (normalizedTilt_probability_of_axis_moment θ μ w
      (bm_integrable (θ.prod μ) (bm_exp hw)) hηhalf haxis).1
  have hR := reference_rate_nonnegative θ μ D w κ r f₀ hw hκb hκlo hf₀ hf₀lo hf₀mass
    hEnt hlam hM hUnperturbed
  exact killing_horizon_of_resolvent_transform P hτ hT hη hε hH hR htransform

end SlowEquilibration.SourceEntropyResolventAbstract
