module

public import SphericalAging.SphereGibbsEntropy
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.ParametricIntegral

public section

/-! Spherical integration by parts follows from genuine orthogonal exponential
flows and the actual rotation invariance of the constructed surface measure. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace NNReal
namespace SphericalAging.SphericalIntegrationByParts
open FiniteModel SphereInitialLaw

@[expose] abbrev Operator (N : ℕ) := Vector N →L[ℝ] Vector N

local instance {N : ℕ} : NormedAlgebra ℚ (Operator N) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Operator N)

@[expose] def operatorFlow {N : ℕ} (A : Operator N) (t : ℝ) : Operator N := NormedSpace.exp (t • A)

/-- A genuine orthogonal exponential flow, constructed from the actual adjoint. -/
@[expose] def flowIsometry {N : ℕ} (A : Operator N) (hA : star A=-A) (t : ℝ) :
    Vector N ≃ₗᵢ[ℝ] Vector N :=
  Unitary.linearIsometryEquiv ⟨operatorFlow A t,by
    apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    simp only [skewAdjoint.mem_iff,star_smul,star_trivial,hA,smul_neg]⟩

theorem flowIsometry_apply {N : ℕ} (A : Operator N) (hA : star A=-A) (t : ℝ) (x : Vector N) :
    flowIsometry A hA t x=operatorFlow A t x := rfl

theorem operatorFlow_norm {N : ℕ} (A : Operator N) (hA : star A=-A) (t : ℝ) (x : Vector N) :
    ‖operatorFlow A t x‖=‖x‖ := (flowIsometry A hA t).norm_map x

theorem operatorFlow_zero {N : ℕ} (A : Operator N) (x : Vector N) : operatorFlow A 0 x=x := by
  change (NormedSpace.exp ((0 : ℝ) • A)) x=x
  rw [show (0 : ℝ) • A=0 from zero_smul ℝ A,NormedSpace.exp_zero]
  rfl

theorem operatorFlow_continuous {N : ℕ} (A : Operator N) : Continuous (operatorFlow A) :=
  (differentiable_exp_smul_const ℝ A).continuous

theorem operatorFlow_hasDerivAt {N : ℕ} (A : Operator N) (t : ℝ) :
    HasDerivAt (operatorFlow A) (A*operatorFlow A t) t :=
  hasDerivAt_exp_smul_const' A t

theorem operatorFlow_apply_hasDerivAt {N : ℕ} (A : Operator N) (t : ℝ) (x : Vector N) :
    HasDerivAt (fun s => operatorFlow A s x) (A (operatorFlow A t x)) t := by
  have hh := (operatorFlow_hasDerivAt A t).clm_apply (hasDerivAt_const t x)
  simpa only [mul_apply_eq_comp,map_zero,add_zero] using hh

/-- The exponential flow preserves the actual uniform spherical probability law. -/
theorem operatorFlow_preserves_sphereLaw {N : ℕ} (A : Operator N) (hA : star A=-A) (t : ℝ) :
    (sphereLaw N).map (operatorFlow A t)=sphereLaw N :=
  sphereLaw_rotation_invariant (flowIsometry A hA t)

theorem continuous_sphere_integrable {N : ℕ} (hN : 0<N) {f : Vector N → ℝ}
    (hf : Continuous f) : Integrable f (sphereLaw N) := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Vector N) (Real.sqrt N)).bddAbove_image hf.norm.continuousOn
  apply (integrable_const M).mono' hf.aestronglyMeasurable
  filter_upwards [sphereLaw_norm_ae hN] with x hx
  exact hM ⟨x,by simpa only [Metric.mem_closedBall,dist_zero_right] using hx.le,rfl⟩

/-- Integrals along genuine spherical rotations are exactly constant. -/
theorem integral_flow_eq {N : ℕ} (A : Operator N) (hA : star A=-A) (t : ℝ) (f : Vector N → ℝ) :
    (∫ x : Vector N,f (operatorFlow A t x) ∂sphereLaw N)=∫ x : Vector N,f x ∂sphereLaw N := by
  have hmp : MeasurePreserving (flowIsometry A hA t) (sphereLaw N) (sphereLaw N) :=
    ⟨(flowIsometry A hA t).continuous.measurable,operatorFlow_preserves_sphereLaw A hA t⟩
  exact hmp.integral_comp (flowIsometry A hA t).toHomeomorph.measurableEmbedding f

/-- The actual directional derivative along a rotation generator. -/
@[expose] def lieDerivative {N : ℕ} (A : Operator N) (f : Vector N → ℝ) (x : Vector N) :=
  fderiv ℝ f x (A x)

theorem lieDerivative_continuous {N : ℕ} (A : Operator N) {f : Vector N → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (lieDerivative A f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply A.continuous

theorem flow_function_hasDerivAt {N : ℕ} (A : Operator N) {f : Vector N → ℝ}
    (hf : ContDiff ℝ 1 f) (t : ℝ) (x : Vector N) :
    HasDerivAt (fun s => f (operatorFlow A s x)) (lieDerivative A f (operatorFlow A t x)) t :=
  ((hf.differentiable (by norm_num) (operatorFlow A t x)).hasFDerivAt).comp_hasDerivAt t
    (operatorFlow_apply_hasDerivAt A t x)


/-- Compactness gives an actual uniform bound for every rotated derivative. -/
theorem lieDerivative_flow_bound {N : ℕ} (A : Operator N) (hA : star A=-A)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ K : ℝ,∀ x : Vector N,‖x‖=Real.sqrt N → ∀ t : ℝ,
      ‖lieDerivative A f (operatorFlow A t x)‖ ≤ K := by
  have hd := hf.continuous_fderiv (by norm_num)
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Vector N) (Real.sqrt N)).bddAbove_image hd.norm.continuousOn
  have hM0 : 0≤M := (norm_nonneg (fderiv ℝ f 0)).trans
    (hM ⟨0,by simp [Metric.mem_closedBall,Real.sqrt_nonneg],rfl⟩)
  refine ⟨M*‖A‖*Real.sqrt N,?_⟩
  intro x hx t
  have hy : operatorFlow A t x ∈ Metric.closedBall (0 : Vector N) (Real.sqrt N) := by
    simp only [Metric.mem_closedBall,dist_zero_right,operatorFlow_norm A hA t x,hx,le_refl]
  have hm := hM ⟨operatorFlow A t x,hy,rfl⟩
  unfold lieDerivative
  calc
    _ ≤ ‖fderiv ℝ f (operatorFlow A t x)‖*‖A (operatorFlow A t x)‖ :=
      (fderiv ℝ f _).le_opNorm _
    _ ≤ M*(‖A‖*‖operatorFlow A t x‖) :=
      mul_le_mul hm (A.le_opNorm _) (norm_nonneg _) hM0
    _ = _ := by rw [operatorFlow_norm A hA t x,hx];ring

/-- Differentiating the invariant integral proves zero average for each actual
spherical rotation derivative. No integration-by-parts premise is assumed. -/
theorem integral_lieDerivative_eq_zero {N : ℕ} (hN : 0<N) (A : Operator N) (hA : star A=-A)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 1 f) :
    (∫ x : Vector N,lieDerivative A f x ∂sphereLaw N)=0 := by
  obtain ⟨K,hK⟩ := lieDerivative_flow_bound A hA hf
  have hc (t : ℝ) : Continuous (fun x => f (operatorFlow A t x)) :=
    hf.continuous.comp (operatorFlow A t).continuous
  have hD (t : ℝ) : Continuous (fun x => lieDerivative A f (operatorFlow A t x)) :=
    (lieDerivative_continuous A hf).comp (operatorFlow A t).continuous
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := sphereLaw N) (F := fun t x => f (operatorFlow A t x))
    (F' := fun t x => lieDerivative A f (operatorFlow A t x)) (bound := fun _ => K)
    (x₀ := (0 : ℝ)) (s := univ)
    (by simp)
    (Eventually.of_forall (fun t => (hc t).aestronglyMeasurable))
    (continuous_sphere_integrable hN (hc 0))
    (hD 0).aestronglyMeasurable
    (by
      filter_upwards [sphereLaw_norm_ae hN] with x hx t ht
      exact hK x hx t)
    (integrable_const K)
    (ae_of_all _ (fun x t ht => flow_function_hasDerivAt A hf t x))
  have hd := hi.2
  have he : (fun t : ℝ => ∫ x : Vector N,f (operatorFlow A t x) ∂sphereLaw N)=
      (fun _ => ∫ x : Vector N,f x ∂sphereLaw N) := by
    funext t
    exact integral_flow_eq A hA t f
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (∫ x : Vector N,f x ∂sphereLaw N))
  simpa only [operatorFlow_zero] using hz

theorem lieDerivative_mul {N : ℕ} (A : Operator N) {f g : Vector N → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : Vector N) :
    lieDerivative A (fun y => f y*g y) x=f x*lieDerivative A g x+g x*lieDerivative A f x := by
  unfold lieDerivative
  rw [fderiv_fun_mul (hf.differentiable (by norm_num) x) (hg.differentiable (by norm_num) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]

/-- Actual spherical integration by parts for every skew-adjoint generator. -/
theorem sphere_lie_integration_by_parts {N : ℕ} (hN : 0<N) (A : Operator N) (hA : star A=-A)
    {f g : Vector N → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    (∫ x : Vector N,f x*lieDerivative A g x ∂sphereLaw N)=
      -(∫ x : Vector N,g x*lieDerivative A f x ∂sphereLaw N) := by
  have hh := integral_lieDerivative_eq_zero hN A hA (hf.mul hg)
  simp_rw [lieDerivative_mul A hf hg] at hh
  rw [integral_add (f := fun x => f x*lieDerivative A g x)
    (g := fun x => g x*lieDerivative A f x) (continuous_sphere_integrable hN (hf.continuous.mul (lieDerivative_continuous A hg)))
    (continuous_sphere_integrable hN (hg.continuous.mul (lieDerivative_continuous A hf)))] at hh
  linarith only [hh]

end SphericalAging.SphericalIntegrationByParts
