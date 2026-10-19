-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalInfiniteSDEStationarity
public import SlowEquilibration.SphericalInfiniteOperators
public import SlowEquilibration.SphericalL2Semigroup
public import SlowEquilibration.SemigroupLaplace

/-! The actual infinite-field transition kernels act as a strongly
continuous contraction semigroup on the original Gibbs L² space. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal InnerProductSpace ContDiff
namespace SlowEquilibration

namespace SphericalC1Dynamics
open SphericalAging SphericalAging.HardSphereDynamics
theorem expectation_time_continuous {N : ℕ} (β : ℝ) (g : State N → State N)
    (hg : ContDiff ℝ 1 g) (f : State N → ℝ) (hf : Continuous f)
    (C : ℝ≥0) (hC : ∀ y,‖f y‖≤C) (x : State N) :
    Continuous (fun t => expectation β g hg t f x) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (C : ℝ))
    (.of_forall (fun t => (hf.stronglyMeasurable.comp_measurable
      (process_measurable β g hg x t)).aestronglyMeasurable))
    (.of_forall (fun t => .of_forall (fun omega => hC (process β g hg x t omega))))
    (integrable_const _) ((process_continuous β g hg x).mono (fun omega homega =>
      (hf.comp homega).continuousAt.tendsto))
end SphericalC1Dynamics

namespace SphericalInfinitePhysical
open SphericalModel SphericalInfiniteModel SphericalL2Semigroup SphericalAging.HardSphereDynamics
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
  (hJ : J∈summableJetDisorder μ) (β : ℝ)

abbrev Space := LiteralGibbsL2 n μ J β

/-- This operator averages the actual Brownian transition kernel under
the proved original invariant Gibbs probability. -/
def P (t : ℝ≥0) : Space n μ J β →L[ℝ] Space n μ J β := by
  let := literal_gibbsLaw_probability n μ β J hJ
  exact StationaryKernel.operator (gibbsLaw (n+1) β (field μ J))
    (infiniteTransitionKernel n μ J β t) (infiniteTransitionKernel_gibbs_invariant n μ J hJ β t)

theorem P_ae (t : ℝ≥0) (U : Space n μ J β) :
    P n μ J hJ β t U =ᵐ[gibbsLaw (n+1) β (field μ J)]
      fun x => ∫ y,U y ∂infiniteTransitionKernel n μ J β t x := by
  let := literal_gibbsLaw_probability n μ β J hJ
  exact StationaryKernel.operator_ae _ _ _ U

theorem P_norm_le (t : ℝ≥0) : ‖P n μ J hJ β t‖≤1 := by
  let := literal_gibbsLaw_probability n μ β J hJ
  exact StationaryKernel.operator_norm_le _ _ _

theorem P_apply_norm_le (t : ℝ≥0) (U : Space n μ J β) : ‖P n μ J hJ β t U‖≤‖U‖ :=
  ((P n μ J hJ β t).le_opNorm U).trans
    ((mul_le_mul_of_nonneg_right (P_norm_le n μ J hJ β t) (norm_nonneg U)).trans_eq (one_mul _))

theorem P_zero : P n μ J hJ β 0=ContinuousLinearMap.id ℝ (Space n μ J β) := by
  apply ContinuousLinearMap.ext
  intro U
  apply Lp.ext
  filter_upwards [P_ae n μ J hJ β 0 U] with x hx
  rw [hx,infiniteTransitionKernel_zero]
  exact integral_dirac U x

theorem P_add (s t : ℝ≥0) :
    P n μ J hJ β (s+t)=(P n μ J hJ β s).comp (P n μ J hJ β t) := by
  let π := gibbsLaw (n+1) β (field μ J)
  let := literal_gibbsLaw_probability n μ β J hJ
  let K := infiniteTransitionKernel n μ J β
  have hInv (r) : K r ∘ₘ π=π := infiniteTransitionKernel_gibbs_invariant n μ J hJ β r
  apply ContinuousLinearMap.ext
  intro U
  have hi : Integrable (U : Vector (n+1) → ℝ) (K (s+t) ∘ₘ π) := by
    rw [hInv]
    exact (Lp.memLp U).integrable (by norm_num)
  have hslice := (Measure.integrable_comp_iff hi.aestronglyMeasurable).mp hi
  have hrep : (P n μ J hJ β t U : Vector (n+1) → ℝ) =ᵐ[K s ∘ₘ π]
      (fun x => ∫ y,U y ∂K t x) := by rw [hInv];exact P_ae n μ J hJ β t U
  have hpull := Measure.ae_ae_of_ae_comp hrep
  apply Lp.ext
  filter_upwards [P_ae n μ J hJ β (s+t) U,P_ae n μ J hJ β s (P n μ J hJ β t U),
    hslice.1,hpull] with x hst hs hi hx
  change (P n μ J hJ β (s+t) U) x=(P n μ J hJ β s (P n μ J hJ β t U)) x
  rw [hst,hs,infiniteTransitionKernel_semigroup]
  change Integrable (U : Vector (n+1) → ℝ) (infiniteTransitionKernel n μ J β (s+t) x) at hi
  rw [infiniteTransitionKernel_semigroup] at hi
  have hx' : (P n μ J hJ β t U : Vector (n+1) → ℝ) =ᵐ[infiniteTransitionKernel n μ J β s x]
      (fun z => ∫ y,U y ∂infiniteTransitionKernel n μ J β t z) := hx
  exact (Kernel.integral_comp hi).trans (integral_congr_ae hx'.symm)

theorem P_ae_expectation (t : ℝ≥0) (U : Space n μ J β) {f : Vector (n+1) → ℝ}
    (hf : StronglyMeasurable f) (hUf : U =ᵐ[gibbsLaw (n+1) β (field μ J)] f) :
    P n μ J hJ β t U =ᵐ[gibbsLaw (n+1) β (field μ J)] infiniteExpectation n μ J β t f := by
  have hcongr := StationaryKernel.ae_average_congr (gibbsLaw (n+1) β (field μ J))
    (infiniteTransitionKernel n μ J β t) (infiniteTransitionKernel_gibbs_invariant n μ J hJ β t) hUf
  filter_upwards [P_ae n μ J hJ β t U,hcongr] with x hx hc
  exact hx.trans (hc.trans (SphericalC1Dynamics.expectation_eq_kernel β _ _ t f hf x).symm)

def smoothCore : Set (Space n μ J β) :=
  {U | ∃ f : Vector (n+1) → ℝ,U =ᵐ[gibbsLaw (n+1) β (field μ J)] f ∧
    HasCompactSupport f ∧ ContDiff ℝ ∞ f}

include hJ in
theorem smoothCore_dense : Dense (smoothCore n μ J β) := by
  let := literal_gibbsLaw_probability n μ β J hJ
  exact Lp.dense_hasCompactSupport_contDiff (by norm_num : (2 : ℝ≥0∞)≠⊤)

theorem P_dist_le (t : ℝ≥0) (U V : Space n μ J β) :
    dist (P n μ J hJ β t U) (P n μ J hJ β t V)≤dist U V := by
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  exact P_apply_norm_le n μ J hJ β t (U-V)

theorem P_smooth_continuous (U : Space n μ J β) (hU : U∈smoothCore n μ J β) :
    Continuous (fun t => P n μ J hJ β t U) := by
  let := literal_gibbsLaw_probability n μ β J hJ
  obtain ⟨f,hUf,hfc,hf⟩ := hU
  obtain ⟨C0,hC0⟩ := hfc.exists_bound_of_continuous hf.continuous
  let C : ℝ≥0 := ⟨max C0 0,le_max_right _ _⟩
  have hC : ∀ x,‖f x‖≤C := fun x => (hC0 x).trans (le_max_left _ _)
  have hb (t : ℝ≥0) (x : Vector (n+1)) : ‖infiniteExpectation n μ J β t f x‖≤C :=
    SphericalC1Dynamics.expectation_norm_le β _ _ t f C hC x
  have hm (t : ℝ≥0) : StronglyMeasurable (infiniteExpectation n μ J β t f) :=
    SphericalC1Dynamics.expectation_stronglyMeasurable β _ _ t f hf.continuous.stronglyMeasurable
  have ht (x : Vector (n+1)) : Continuous (fun t => infiniteExpectation n μ J β t f x) :=
    SphericalC1Dynamics.expectation_time_continuous β _ _ f hf.continuous C hC x
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let E : ℝ≥0 → Vector (n+1) → ℝ := fun t x =>
    infiniteExpectation n μ J β t f x-infiniteExpectation n μ J β t₀ f x
  have hEm (t) : AEStronglyMeasurable (fun x => E t x^2) (gibbsLaw (n+1) β (field μ J)) :=
    ((hm t).sub (hm t₀)).pow 2 |>.aestronglyMeasurable
  have hEb (t) (x) : ‖E t x^2‖≤(2*(C : ℝ))^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have he : ‖E t x‖≤2*(C : ℝ) := (norm_sub_le _ _).trans
      ((add_le_add (hb t x) (hb t₀ x)).trans_eq (by ring))
    simpa only [Real.norm_eq_abs,sq_abs] using
      (sq_le_sq₀ (norm_nonneg (E t x)) (by positivity : 0≤2*(C : ℝ))).mpr he
  have hEt (x) : Tendsto (fun t => E t x^2) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous (fun t => E t x^2) := ((ht x).sub continuous_const).pow 2
    have hh := hc.continuousAt (x := t₀) |>.tendsto
    simpa only [E,sub_self,zero_pow (by norm_num : (2 : ℕ)≠0)] using hh
  have hI : Tendsto (fun t => ∫ x,E t x^2 ∂gibbsLaw (n+1) β (field μ J)) (𝓝 t₀) (𝓝 0) := by
    simpa only [integral_zero] using
      tendsto_integral_filter_of_dominated_convergence (fun _ => (2*(C : ℝ))^2)
        (.of_forall hEm) (.of_forall (fun t => .of_forall (hEb t)))
        (integrable_const _) (.of_forall hEt)
  have hn (t : ℝ≥0) : ‖P n μ J hJ β t U-P n μ J hJ β t₀ U‖^2=
      ∫ x,E t x^2 ∂gibbsLaw (n+1) β (field μ J) := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [P_ae_expectation n μ J hJ β t U hf.continuous.stronglyMeasurable hUf,
      P_ae_expectation n μ J hJ β t₀ U hf.continuous.stronglyMeasurable hUf,
      Lp.coeFn_sub (P n μ J hJ β t U) (P n μ J hJ β t₀ U)] with x htx ht₀x hs
    simp only [hs,Pi.sub_apply,htx,ht₀x,RCLike.inner_apply,conj_trivial,E,pow_two]
  have hsq : Tendsto (fun t => ‖P n μ J hJ β t U-P n μ J hJ β t₀ U‖^2) (𝓝 t₀) (𝓝 0) :=
    hI.congr' (.of_forall (fun t => (hn t).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

theorem P_apply_continuous (U : Space n μ J β) : Continuous (fun t => P n μ J hJ β t U) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨V,hV,hUV⟩ := (smoothCore_dense n μ J hJ β).exists_dist_lt U (show 0<ε/3 by positivity)
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    (P_smooth_continuous n μ J hJ β V hV).continuousAt (ε/3) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro t ht
  have hmid := hclose ht
  have htriangle := dist_triangle (P n μ J hJ β t U) (P n μ J hJ β t V) (P n μ J hJ β t₀ U)
  have htriangle' := dist_triangle (P n μ J hJ β t V) (P n μ J hJ β t₀ V) (P n μ J hJ β t₀ U)
  have hl := P_dist_le n μ J hJ β t U V
  have hr := P_dist_le n μ J hJ β t₀ V U
  rw [dist_comm V U] at hr
  linarith

/-- Strongly continuous contraction data built from the actual Brownian
kernel, without prescribing any spectral expansion. -/
def semigroupData : SemigroupLaplace.Data (Space n μ J β) where
  P := P n μ J hJ β
  zero := P_zero n μ J hJ β
  add := P_add n μ J hJ β
  norm_le := P_apply_norm_le n μ J hJ β
  continuous := P_apply_continuous n μ J hJ β

end SphericalInfinitePhysical
end SlowEquilibration
