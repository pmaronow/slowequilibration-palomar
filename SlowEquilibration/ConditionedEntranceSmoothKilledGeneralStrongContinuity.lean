-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralSemigroup
public import SlowEquilibration.SemigroupLaplace

/-! Genuine strong continuity of the source smooth cutoff killed
semigroup, from physical path continuity and smooth L² density. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics SphericalReversibility
open FeynmanKac
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem expectation_time_continuous (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (f : Vector N → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (x : Vector N) :
    Continuous (fun t => expectation D β κ t f x) :=
  killedExpectation_time_continuous (VectorBrownian.law N) κ hκ hκ0
    (process D β x) (process_measurable D β x) (process_ae_continuous D β x) f hf C hC

theorem expectation_stronglyMeasurable (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (t : ℝ≥0) (f : Vector N → ℝ)
    (hf : StronglyMeasurable f) : StronglyMeasurable (expectation D β κ t f) := by
  let := kernel_finite D β κ hκ hκ0 t
  have h := hf.integral_kernel (κ := kernel D β κ hκ t)
  convert h using 1
  exact (funext (kernel_integral_actual D β κ hκ t f hf)).symm

theorem kernel_zero (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) (x : Vector N) :
    kernel D β κ hκ 0 x=Measure.dirac x := by
  let := kernel_finite D β κ hκ hκ0 0
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [kernel_integral_actual D β κ hκ 0 f f.continuous.stronglyMeasurable x]
  change (∫ omega, survival κ (process D β x) 0 omega * f (process D β x 0 omega)
    ∂VectorBrownian.law N) = _
  simp only [survival_zero,one_mul]
  rw [integral_congr_ae ((process_zero D β x).mono (fun _ h => congrArg f h))]
  simp

theorem operator_zero (D : FieldData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x,0 ≤ κ x) :
    operator D β κ hκ hκ0 0=ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro U
  apply Lp.ext
  filter_upwards [operator_ae D β κ hκ hκ0 0 U] with x hx
  rw [hx,kernel_zero D β κ hκ hκ0 x]
  exact integral_dirac U x

def smoothCore (D : FieldData N) (β : ℝ) :
    Set (Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :=
  {U | ∃ f : Vector N → ℝ, U =ᵐ[gibbsLaw N β D.hamiltonian] f ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f}

theorem smoothCore_dense (D : FieldData N) (β : ℝ) : Dense (smoothCore D β) := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  exact Lp.dense_hasCompactSupport_contDiff (μ := gibbsLaw N β D.hamiltonian)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)

variable (D : FieldData N) (β : ℝ)
  (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)

theorem operator_apply_norm_le (t : ℝ≥0) (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    ‖operator D β κ hκ hκ0 t U‖ ≤ ‖U‖ :=
  ((operator D β κ hκ hκ0 t).le_opNorm U).trans
    ((mul_le_mul_of_nonneg_right (operator_norm_le D β κ hκ hκ0 t)
      (norm_nonneg U)).trans_eq (one_mul _))

theorem operator_dist_le (t : ℝ≥0) (U V : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    dist (operator D β κ hκ hκ0 t U) (operator D β κ hκ hκ0 t V) ≤ dist U V := by
  rw [dist_eq_norm,dist_eq_norm,← map_sub]
  exact operator_apply_norm_le D β κ hκ hκ0 t (U-V)

theorem operator_smooth_continuous (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian))
    (hU : U ∈ smoothCore D β) :
    Continuous (fun t => operator D β κ hκ hκ0 t U) := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  obtain ⟨f,hUf,hfc,hf⟩ := hU
  obtain ⟨C0,hC0⟩ := hfc.exists_bound_of_continuous hf.continuous
  let C : ℝ := max C0 0
  have hC : ∀ x, ‖f x‖ ≤ C := fun x => (hC0 x).trans (le_max_left _ _)
  have hb (t : ℝ≥0) (x : Vector N) : ‖expectation D β κ t f x‖ ≤ C :=
    killedExpectation_norm_le (VectorBrownian.law N) κ hκ0 (process D β x) t f C
      (.of_forall (fun _ => hC _))
  have hm (t : ℝ≥0) : StronglyMeasurable (expectation D β κ t f) :=
    expectation_stronglyMeasurable D β κ hκ hκ0 t f hf.continuous.stronglyMeasurable
  have ht (x : Vector N) : Continuous (fun t => expectation D β κ t f x) :=
    expectation_time_continuous D β κ hκ hκ0 f hf.continuous C hC x
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let F : ℝ≥0 → Vector N → ℝ := fun t x =>
    expectation D β κ t f x-expectation D β κ t₀ f x
  have hFm (t) : AEStronglyMeasurable (fun x => F t x ^ 2) (gibbsLaw N β D.hamiltonian) :=
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
  have hI : Tendsto (fun t => ∫ x, F t x ^ 2 ∂gibbsLaw N β D.hamiltonian) (𝓝 t₀) (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (fun _ => (2*C)^2) (.of_forall hFm) (.of_forall (fun t => .of_forall (hFb t)))
      (integrable_const _) (.of_forall hFt)
  have hn (t : ℝ≥0) :
      ‖operator D β κ hκ hκ0 t U-operator D β κ hκ hκ0 t₀ U‖ ^ 2 =
        ∫ x, F t x ^ 2 ∂gibbsLaw N β D.hamiltonian := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [operator_ae_expectation D β κ hκ hκ0 t U f hf.continuous.stronglyMeasurable hUf,
      operator_ae_expectation D β κ hκ hκ0 t₀ U f hf.continuous.stronglyMeasurable hUf,
      Lp.coeFn_sub (operator D β κ hκ hκ0 t U)
        (operator D β κ hκ hκ0 t₀ U)] with x htx ht₀x hs
    simp only [hs,Pi.sub_apply,htx,ht₀x,RCLike.inner_apply,conj_trivial,F,pow_two]
  have hsq : Tendsto
      (fun t => ‖operator D β κ hκ hκ0 t U-operator D β κ hκ hκ0 t₀ U‖ ^ 2)
      (𝓝 t₀) (𝓝 0) := hI.congr' (.of_forall (fun t => (hn t).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh

theorem operator_apply_continuous (U : Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) :
    Continuous (fun t => operator D β κ hκ hκ0 t U) := by
  let Q := operator D β κ hκ hκ0
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨V,hV,hUV⟩ := (smoothCore_dense D β).exists_dist_lt U (show 0 < ε/3 by positivity)
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp
    (operator_smooth_continuous D β κ hκ hκ0 V hV).continuousAt (ε/3) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro t ht
  have hmid := hclose ht
  have htriangle := dist_triangle (Q t U) (Q t V) (Q t₀ U)
  have htriangle' := dist_triangle (Q t V) (Q t₀ V) (Q t₀ U)
  have hl := operator_dist_le D β κ hκ hκ0 t U V
  have hr := operator_dist_le D β κ hκ hκ0 t₀ V U
  rw [dist_comm V U] at hr
  linarith

/-- Genuine semigroup data for the manuscript's original physically
killed mixed diffusion on its actual normalized Gibbs Hilbert space. -/
def semigroupData : SemigroupLaplace.Data (Lp ℝ 2 (gibbsLaw N β D.hamiltonian)) where
  P := operator D β κ hκ hκ0
  zero := operator_zero D β κ hκ hκ0
  add := operator_add D β κ hκ hκ0
  norm_le := operator_apply_norm_le D β κ hκ hκ0
  continuous := operator_apply_continuous D β κ hκ hκ0

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
