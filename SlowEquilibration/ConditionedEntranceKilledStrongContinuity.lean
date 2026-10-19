-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFeynmanKacContinuous

/-! The physical bounded-killing Gibbs L² operators form an actual
strongly continuous contraction semigroup. Density and continuity are
proved, rather than recorded as a diffusion interface. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics SphericalReversibility
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def sourceKilledSmoothCore (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ) :
    Set (Lp ℝ 2 (mixtureGibbsLaw μ β J)) :=
  {U | ∃ f : Vector N → ℝ, U =ᵐ[mixtureGibbsLaw μ β J] f ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f}

theorem sourceKilledSmoothCore_dense (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) : Dense (sourceKilledSmoothCore μ J β) := by
  let := mixtureGibbsLaw_probability hN μ β J
  exact Lp.dense_hasCompactSupport_contDiff (μ := mixtureGibbsLaw μ β J)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

variable (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
  (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)

theorem sourceKilledOperator_apply_norm_le (t : ℝ≥0) (U : Lp ℝ 2 (mixtureGibbsLaw μ β J)) :
    ‖sourceKilledOperator hN μ J β κ hκ hκ0 t U‖ ≤ ‖U‖ :=
  ((sourceKilledOperator hN μ J β κ hκ hκ0 t).le_opNorm U).trans
    ((mul_le_mul_of_nonneg_right (sourceKilledOperator_norm_le hN μ J β κ hκ hκ0 t)
      (norm_nonneg U)).trans_eq (one_mul _))

theorem sourceKilledOperator_dist_le (t : ℝ≥0) (U V : Lp ℝ 2 (mixtureGibbsLaw μ β J)) :
    dist (sourceKilledOperator hN μ J β κ hκ hκ0 t U) (sourceKilledOperator hN μ J β κ hκ hκ0 t V) ≤ dist U V := by
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  exact sourceKilledOperator_apply_norm_le hN μ J β κ hκ hκ0 t (U-V)

theorem sourceKilledOperator_smooth_continuous (U : Lp ℝ 2 (mixtureGibbsLaw μ β J))
    (hU : U ∈ sourceKilledSmoothCore μ J β) :
    Continuous (fun t => sourceKilledOperator hN μ J β κ hκ hκ0 t U) := by
  let := mixtureGibbsLaw_probability hN μ β J
  obtain ⟨f,hUf,hfc,hf⟩ := hU
  obtain ⟨C0,hC0⟩ := hfc.exists_bound_of_continuous hf.continuous
  let C : ℝ := max C0 0
  have hC : ∀ x, ‖f x‖ ≤ C := fun x => (hC0 x).trans (le_max_left _ _)
  have hb (t : ℝ≥0) (x : Vector N) : ‖sourceKilledExpectation μ J β κ t f x‖ ≤ C :=
    killedExpectation_norm_le (VectorBrownian.law N) κ hκ0 (sourceProcess μ J β x) t f C
      (.of_forall (fun _ => hC _))
  have hm (t : ℝ≥0) : StronglyMeasurable (sourceKilledExpectation μ J β κ t f) :=
    sourceKilledExpectation_stronglyMeasurable μ J β κ hκ hκ0 t f hf.continuous.stronglyMeasurable
  have ht (x : Vector N) : Continuous (fun t => sourceKilledExpectation μ J β κ t f x) :=
    sourceKilledExpectation_time_continuous μ J β κ hκ hκ0 f hf.continuous C hC x
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let F : ℝ≥0 → Vector N → ℝ := fun t x =>
    sourceKilledExpectation μ J β κ t f x-sourceKilledExpectation μ J β κ t₀ f x
  have hFm (t) : AEStronglyMeasurable (fun x => F t x ^ 2) (mixtureGibbsLaw μ β J) :=
    ((hm t).sub (hm t₀)).pow 2 |>.aestronglyMeasurable
  have hFb (t) (x) : ‖F t x ^ 2‖ ≤ (2*C)^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have he : ‖F t x‖ ≤ 2*C := (norm_sub_le _ _).trans
      ((add_le_add (hb t x) (hb t₀ x)).trans_eq (by ring))
    simpa only [Real.norm_eq_abs,sq_abs] using
      (sq_le_sq₀ (norm_nonneg (F t x)) (by dsimp [C]; positivity : 0 ≤ 2*C)).mpr he
  have hFt (x) : Tendsto (fun t => F t x ^ 2) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous (fun t => F t x ^ 2) := ((ht x).sub continuous_const).pow 2
    simpa only [F,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (hc.continuousAt (x := t₀)).tendsto
  have hI : Tendsto (fun t => ∫ x, F t x ^ 2 ∂mixtureGibbsLaw μ β J) (𝓝 t₀) (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2*C)^2) (.of_forall hFm) (.of_forall (fun t => .of_forall (hFb t)))
      (integrable_const _) (.of_forall hFt)
  have hn (t : ℝ≥0) :
      ‖sourceKilledOperator hN μ J β κ hκ hκ0 t U-sourceKilledOperator hN μ J β κ hκ hκ0 t₀ U‖ ^ 2 =
        ∫ x, F t x ^ 2 ∂mixtureGibbsLaw μ β J := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [sourceKilledOperator_ae_expectation hN μ J β κ hκ hκ0 t U f hf.continuous.stronglyMeasurable hUf,
      sourceKilledOperator_ae_expectation hN μ J β κ hκ hκ0 t₀ U f hf.continuous.stronglyMeasurable hUf,
      Lp.coeFn_sub (sourceKilledOperator hN μ J β κ hκ hκ0 t U)
        (sourceKilledOperator hN μ J β κ hκ hκ0 t₀ U)] with x htx ht₀x hs
    simp only [hs,Pi.sub_apply,htx,ht₀x,RCLike.inner_apply,conj_trivial,F,pow_two]
  have hsq : Tendsto
      (fun t => ‖sourceKilledOperator hN μ J β κ hκ hκ0 t U-sourceKilledOperator hN μ J β κ hκ hκ0 t₀ U‖ ^ 2)
      (𝓝 t₀) (𝓝 0) := hI.congr' (.of_forall (fun t => (hn t).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

theorem sourceKilledOperator_apply_continuous (U : Lp ℝ 2 (mixtureGibbsLaw μ β J)) :
    Continuous (fun t => sourceKilledOperator hN μ J β κ hκ hκ0 t U) := by
  let Q := sourceKilledOperator hN μ J β κ hκ hκ0
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨V,hV,hUV⟩ := (sourceKilledSmoothCore_dense hN μ J β).exists_dist_lt U (show 0 < ε/3 by positivity)
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    (sourceKilledOperator_smooth_continuous hN μ J β κ hκ hκ0 V hV).continuousAt (ε/3) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro t ht
  have hmid := hclose ht
  have htriangle := dist_triangle (Q t U) (Q t V) (Q t₀ U)
  have htriangle' := dist_triangle (Q t V) (Q t₀ V) (Q t₀ U)
  have hl := sourceKilledOperator_dist_le hN μ J β κ hκ hκ0 t U V
  have hr := sourceKilledOperator_dist_le hN μ J β κ hκ hκ0 t₀ V U
  rw [dist_comm V U] at hr
  linarith

/-- Genuine semigroup data for the manuscript's original physically
killed mixed diffusion on its actual normalized Gibbs Hilbert space. -/
def sourceKilledSemigroupData : SemigroupLaplace.Data (Lp ℝ 2 (mixtureGibbsLaw μ β J)) where
  P := sourceKilledOperator hN μ J β κ hκ hκ0
  zero := sourceKilledOperator_zero hN μ J β κ hκ hκ0
  add := sourceKilledOperator_add hN μ J β κ hκ hκ0
  norm_le := sourceKilledOperator_apply_norm_le hN μ J β κ hκ hκ0
  continuous := sourceKilledOperator_apply_continuous hN μ J β κ hκ hκ0

end SlowEquilibration.ConditionedEntrance.FeynmanKac
