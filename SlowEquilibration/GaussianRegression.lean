-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Tactic.FunProp

/-!
# Canonical whole-field finite Gaussian regression

The observation is an actual surjective continuous linear map of a genuine
standard Gaussian coefficient vector. Its canonical lift, orthogonal residual,
independence, and full Borel regression kernel are derived, not assumed.
-/

@[expose] public section

namespace SlowEquilibration.GaussianRegression

open MeasureTheory ProbabilityTheory Set Function
open scoped RealInnerProductSpace Topology ENNReal

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The genuine observation covariance operator. -/
def gram (A : E →L[ℝ] F) : F →L[ℝ] F := A.comp A.adjoint

/-- The ordinary canonical minimum-norm lift. -/
def lift (A : E →L[ℝ] F) : F →L[ℝ] E := A.adjoint.comp (gram A).inverse

/-- The ordinary full-coefficient residual, before its projection property is proved. -/
def residual (A : E →L[ℝ] F) : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - (lift A).comp A

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Surjectivity makes the actual observation covariance invertible. -/
theorem gram_isInvertible (A : E →L[ℝ] F) (hA : Surjective A) : (gram A).IsInvertible := by
  have hr : A.range = ⊤ := LinearMap.range_eq_top.mpr hA
  have hk : A.adjoint.ker = ⊥ := by
    rw [← A.orthogonal_range, hr]
    simp
  have hi : Injective A.adjoint := LinearMap.ker_eq_bot.mp hk
  have hG : Injective (gram A) := by
    change Injective (A ∘ A.adjoint)
    exact A.self_comp_adjoint_injective_iff.mpr hi
  let e := LinearEquiv.ofBijective (gram A).toLinearMap
    ⟨hG, LinearMap.injective_iff_surjective.mp hG⟩
  exact ⟨e.toContinuousLinearEquiv, rfl⟩

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma observation_lift (A : E →L[ℝ] F) (hA : Surjective A) :
    A.comp (lift A) = ContinuousLinearMap.id ℝ F := by
  unfold lift
  rw [← ContinuousLinearMap.comp_assoc]
  exact (gram_isInvertible A hA).self_comp_inverse

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma observation_lift_apply (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    A (lift A w) = w := by
  have h := congrArg (fun T : F →L[ℝ] F => T w) (observation_lift A hA)
  exact h

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma residual_mem_ker (A : E →L[ℝ] F) (hA : Surjective A) (x : E) : residual A x ∈ A.ker := by
  change A (residual A x) = 0
  simp only [residual, sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    map_sub, observation_lift_apply A hA, sub_self]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
lemma lift_orthogonal_ker (A : E →L[ℝ] F) (w : F) (x : E) (hx : x ∈ A.ker) :
    inner ℝ x (lift A w) = 0 := by
  have hx' : A x = 0 := hx
  rw [lift, ContinuousLinearMap.comp_apply, A.adjoint_inner_right, hx', inner_zero_left]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- The canonical algebraic residual is the actual orthogonal kernel projection. -/
theorem residual_eq_starProjection (A : E →L[ℝ] F) (hA : Surjective A) :
    residual A = A.ker.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (residual_mem_ker A hA x)
  intro y hy
  have he : x - residual A x = lift A (A x) := by
    simp only [residual, sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
      sub_sub_cancel]
  rw [he, real_inner_comm]
  exact lift_orthogonal_ker A (A x) y hy

/-- Genuine independence of the full residual vector from the observation. -/
theorem residual_observation_independent (A : E →L[ℝ] F) (hA : Surjective A) :
    IndepFun (residual A) A (stdGaussian E) := by
  have hG := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun ((residual A).prod A)
  apply hG.indepFun_of_covariance_inner
  intro x y
  change cov[fun z : E => inner ℝ x (residual A z),
    fun z : E => inner ℝ y (A z); stdGaussian E] = 0
  have h1 : (fun z : E => inner ℝ x (residual A z)) = fun z => inner ℝ (residual A x) z := by
    funext z
    rw [residual_eq_starProjection A hA]
    exact (A.ker.starProjection_isSymmetric x z).symm
  have h2 : (fun z : E => inner ℝ y (A z)) = fun z => inner ℝ (A.adjoint y) z := by
    funext z
    exact (A.adjoint_inner_left z y).symm
  rw [h1, h2, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply, A.adjoint_inner_right]
  have hz : A (residual A x) = 0 := residual_mem_ker A hA x
  rw [hz, inner_zero_left]

/-- The genuine observation law. -/
def observationLaw (A : E →L[ℝ] F) : Measure F := (stdGaussian E).map A

/-- The genuine full residual law, including all unobserved field coefficients. -/
def residualLaw (A : E →L[ℝ] F) : Measure E := (stdGaussian E).map (residual A)

instance observationLaw_probability (A : E →L[ℝ] F) : IsProbabilityMeasure (observationLaw A) := by
  unfold observationLaw
  infer_instance

instance residualLaw_probability (A : E →L[ℝ] F) : IsProbabilityMeasure (residualLaw A) := by
  unfold residualLaw
  infer_instance

/-- The actual joint observation/residual distribution factors as its true marginals. -/
theorem observation_residual_jointLaw (A : E →L[ℝ] F) (hA : Surjective A) :
    (stdGaussian E).map (fun x => (A x, residual A x)) =
      (observationLaw A).prod (residualLaw A) :=
  (residual_observation_independent A hA).symm.map_prod_eq_prod_map_map
    A.continuous.measurable.aemeasurable (residual A).continuous.measurable.aemeasurable

/-- Canonical regression of the full coefficient field at every observation,
including every specified point of zero observation probability. -/
def regressionKernel (A : E →L[ℝ] F) : Kernel F E where
  toFun w := (stdGaussian E).map (fun x => residual A x + lift A w)
  measurable' := by
    rw [Measure.measurable_measure]
    intro s hs
    simp only [Measure.map_apply (by fun_prop : Measurable
      (fun x : E => residual A x + lift A _)) hs]
    exact measurable_measure_prodMk_left (s := {p : F × E | residual A p.2 + lift A p.1 ∈ s})
      (hs.preimage (by fun_prop))

@[simp] lemma regressionKernel_apply (A : E →L[ℝ] F) (w : F) :
    regressionKernel A w = (stdGaussian E).map (fun x => residual A x + lift A w) := rfl

instance regressionKernel_markov (A : E →L[ℝ] F) : IsMarkovKernel (regressionKernel A) where
  isProbabilityMeasure w := by
    rw [regressionKernel_apply]
    infer_instance

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Every canonical conditional sample satisfies its actual observation,
proved pointwise before passing to the kernel law. -/
lemma regression_sample_observation (A : E →L[ℝ] F) (hA : Surjective A) (w : F) (x : E) :
    A (residual A x + lift A w) = w := by
  rw [map_add, observation_lift_apply A hA]
  have hz : A (residual A x) = 0 := residual_mem_ker A hA x
  rw [hz, zero_add]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Algebraic reconstruction retains every coefficient of the full field. -/
lemma residual_add_lift_observation (A : E →L[ℝ] F) (x : E) :
    residual A x + lift A (A x) = x := by
  simp only [residual, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, sub_add_cancel]

/-- Genuine joint field/observation law, reconstructed from proven independent
whole-vector residual and observation marginals. -/
theorem observation_field_jointLaw (A : E →L[ℝ] F) (hA : Surjective A) :
    (stdGaussian E).map (fun x => (A x, x)) =
      ((observationLaw A).prod (residualLaw A)).map
        (fun p => (p.1, p.2 + lift A p.1)) := by
  rw [← observation_residual_jointLaw A hA,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  apply Prod.ext
  · rfl
  · exact (residual_add_lift_observation A x).symm

/-- Canonical whole-field Gaussian regression/disintegration for every Borel
nonnegative mark, possibly unbounded and of infinite expectation. -/
theorem regression_disintegration (A : E →L[ℝ] F) (hA : Surjective A)
    (phi : F × E → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ x, phi (A x, x) ∂stdGaussian E) =
      ∫⁻ w, ∫⁻ y, phi (w, y) ∂regressionKernel A w ∂observationLaw A := by
  calc
    _ = ∫⁻ p, phi p ∂(stdGaussian E).map (fun x => (A x, x)) :=
      (lintegral_map hphi (by fun_prop)).symm
    _ = ∫⁻ w, ∫⁻ r, phi (w, r + lift A w) ∂residualLaw A ∂observationLaw A := by
      rw [observation_field_jointLaw A hA, lintegral_map hphi (by fun_prop)]
      exact lintegral_prod _ (hphi.comp (by fun_prop)).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro w
      have h1 : Measurable (fun r : E => phi (w, r + lift A w)) :=
        hphi.comp (measurable_const.prodMk (measurable_id.add measurable_const))
      have h0 : Measurable (fun y : E => phi (w, y)) :=
        hphi.comp (measurable_const.prodMk measurable_id)
      rw [regressionKernel_apply, residualLaw,
        lintegral_map h1 (residual A).continuous.measurable,
        lintegral_map h0 (by fun_prop)]

/-- Equality with an actual Markov-kernel disintegration of the genuine joint
coefficient law, rather than a conditional-law identity supplied as a premise. -/
theorem regression_compProd (A : E →L[ℝ] F) (hA : Surjective A) :
    (stdGaussian E).map (fun x => (A x, x)) = (observationLaw A).compProd (regressionKernel A) := by
  apply Measure.ext_of_lintegral
  intro phi hphi
  rw [lintegral_map hphi (by fun_prop), Measure.lintegral_compProd hphi]
  exact regression_disintegration A hA phi hphi

/-- The canonical kernel is supported on its exact observation fiber at every
specified observation, including observation zero. -/
theorem regressionKernel_observation_ae (A : E →L[ℝ] F) (hA : Surjective A) (w : F) :
    ∀ᵐ y ∂regressionKernel A w, A y = w := by
  rw [regressionKernel_apply]
  apply (ae_map_iff (by fun_prop : AEMeasurable
    (fun x : E => residual A x + lift A w) (stdGaussian E))
      ((measurableSet_singleton w).preimage A.continuous.measurable)).mpr
  exact Filter.Eventually.of_forall (regression_sample_observation A hA w)

end
end SlowEquilibration.GaussianRegression
