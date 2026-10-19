module

public import SphericalAging.AdaptiveGradientDisclosure
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.ConditionalExpectation

public section

/-! Actual standard Gaussian disorder splits into independent Gaussian
projections on any fixed tensor subspace and its orthogonal complement.
This is the fixed-subspace Gaussian regeneration used at the start of
source 10.6. Adaptive random-subspace conditioning remains separate. -/
noncomputable section
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.OrthogonalGaussianDisclosure
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open scoped InnerProductSpace BigOperators Topology

 theorem ordered_tensor_hasLaw (N p : ℕ) :
    HasLaw (WithLp.toLp 2 : Disorder N p→TensorSpace N p)
      (stdGaussian (TensorSpace N p)) (disorderLaw N p) := by
  refine ⟨(PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.aemeasurable,?_⟩
  exact map_pi_eq_stdGaussian

 theorem tensor_inner_covariance {N p : ℕ} (a b : TensorSpace N p) :
    cov[fun J : Disorder N p => ⟪a,WithLp.toLp 2 J⟫_ℝ,
      fun J : Disorder N p => ⟪b,WithLp.toLp 2 J⟫_ℝ;disorderLaw N p]=⟪a,b⟫_ℝ := by
  have ha : (fun J : Disorder N p => ⟪a,WithLp.toLp 2 J⟫_ℝ)=tensorLinear a.ofLp := by
    funext J
    simp [PiLp.inner_apply,tensorLinear,mul_comm]
  have hb : (fun J : Disorder N p => ⟪b,WithLp.toLp 2 J⟫_ℝ)=tensorLinear b.ofLp := by
    funext J
    simp [PiLp.inner_apply,tensorLinear,mul_comm]
  rw [ha,hb,covariance_eq_sub (tensorLinear_memLp _) (tensorLinear_memLp _)]
  simp only [Pi.mul_apply,tensorLinear_covariance,tensorLinear_mean,zero_mul,sub_zero]
  simp [PiLp.inner_apply,mul_comm]

 theorem tensor_projections_independent {N p : ℕ} (T : Submodule ℝ (TensorSpace N p)) :
    IndepFun (fun J : Disorder N p => T.starProjection (WithLp.toLp 2 J))
      (fun J : Disorder N p => Tᗮ.starProjection (WithLp.toLp 2 J)) (disorderLaw N p) := by
  have hG := ((ordered_tensor_hasLaw N p).hasGaussianLaw).map_fun
    (T.starProjection.prod Tᗮ.starProjection)
  apply hG.indepFun_of_covariance_inner
  intro a b
  have h₁ : (fun J : Disorder N p => ⟪a,T.starProjection (WithLp.toLp 2 J)⟫_ℝ)=
      fun J => ⟪T.starProjection a,WithLp.toLp 2 J⟫_ℝ := by
    funext J
    exact (T.inner_starProjection_left_eq_right a _).symm
  have h₂ : (fun J : Disorder N p => ⟪b,Tᗮ.starProjection (WithLp.toLp 2 J)⟫_ℝ)=
      fun J => ⟪Tᗮ.starProjection b,WithLp.toLp 2 J⟫_ℝ := by
    funext J
    exact (Tᗮ.inner_starProjection_left_eq_right b _).symm
  change cov[fun J : Disorder N p => ⟪a,T.starProjection (WithLp.toLp 2 J)⟫_ℝ,
    fun J : Disorder N p => ⟪b,Tᗮ.starProjection (WithLp.toLp 2 J)⟫_ℝ;disorderLaw N p]=0
  rw [h₁,h₂,tensor_inner_covariance]
  exact Submodule.inner_right_of_mem_orthogonal
    (T.orthogonalProjectionOnto a).property (Tᗮ.orthogonalProjectionOnto b).property

 theorem tensor_projection_pair_law {N p : ℕ} (T : Submodule ℝ (TensorSpace N p)) :
    (disorderLaw N p).map (fun J =>
      (T.starProjection (WithLp.toLp 2 J),Tᗮ.starProjection (WithLp.toLp 2 J)))=
      ((disorderLaw N p).map (fun J => T.starProjection (WithLp.toLp 2 J))).prod
      ((disorderLaw N p).map (fun J => Tᗮ.starProjection (WithLp.toLp 2 J))) := by
  exact (tensor_projections_independent T).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)

 theorem stdGaussian_projection_law {N p : ℕ} (T : Submodule ℝ (TensorSpace N p)) :
    (stdGaussian (TensorSpace N p)).map T.orthogonalProjectionOnto=stdGaussian T := by
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_stdGaussian,charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  have hi z : ⟪T.orthogonalProjectionOnto z,x⟫_ℝ=⟪z,(x : TensorSpace N p)⟫_ℝ := by
    simpa only [Submodule.adjoint_orthogonalProjectionOnto,Submodule.subtypeL_apply] using
      ((T.orthogonalProjectionOnto).adjoint_inner_right z x).symm
  simp_rw [hi]
  rw [←charFun_apply,charFun_stdGaussian]
  rfl

 theorem ordered_projection_hasLaw {N p : ℕ} (T : Submodule ℝ (TensorSpace N p)) :
    HasLaw (fun J : Disorder N p => T.orthogonalProjectionOnto (WithLp.toLp 2 J))
      (stdGaussian T) (disorderLaw N p) := by
  have hproj : HasLaw T.orthogonalProjectionOnto (stdGaussian T) (stdGaussian (TensorSpace N p)) :=
    ⟨by fun_prop,stdGaussian_projection_law T⟩
  exact hproj.comp (ordered_tensor_hasLaw N p)

 theorem tensor_subtype_projections_independent {N p : ℕ} (T : Submodule ℝ (TensorSpace N p)) :
    IndepFun (fun J : Disorder N p => T.orthogonalProjectionOnto (WithLp.toLp 2 J))
      (fun J : Disorder N p => Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J)) (disorderLaw N p) := by
  have hG := ((ordered_tensor_hasLaw N p).hasGaussianLaw).map_fun
    (T.orthogonalProjectionOnto.prod Tᗮ.orthogonalProjectionOnto)
  apply hG.indepFun_of_covariance_inner
  intro a b
  change cov[fun J : Disorder N p => ⟪a,T.orthogonalProjectionOnto (WithLp.toLp 2 J)⟫_ℝ,
    fun J : Disorder N p => ⟪b,Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J)⟫_ℝ;disorderLaw N p]=0
  have h₁ : (fun J : Disorder N p => ⟪a,T.orthogonalProjectionOnto (WithLp.toLp 2 J)⟫_ℝ)=
      fun J => ⟪(a : TensorSpace N p),WithLp.toLp 2 J⟫_ℝ := by
    funext J
    simpa only [Submodule.adjoint_orthogonalProjectionOnto,Submodule.subtypeL_apply] using
      ((T.orthogonalProjectionOnto).adjoint_inner_left (WithLp.toLp 2 J) a).symm
  have h₂ : (fun J : Disorder N p => ⟪b,Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J)⟫_ℝ)=
      fun J => ⟪(b : TensorSpace N p),WithLp.toLp 2 J⟫_ℝ := by
    funext J
    simpa only [Submodule.adjoint_orthogonalProjectionOnto,Submodule.subtypeL_apply] using
      ((Tᗮ.orthogonalProjectionOnto).adjoint_inner_left (WithLp.toLp 2 J) b).symm
  rw [h₁,h₂,tensor_inner_covariance]
  exact Submodule.inner_right_of_mem_orthogonal a.property b.property

@[expose]  def disclosedSigma {N p : ℕ} (T : Submodule ℝ (TensorSpace N p)) : MeasurableSpace (Disorder N p) :=
  MeasurableSpace.comap (fun J : Disorder N p => Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J)) inferInstance

set_option maxHeartbeats 200000 in
 theorem conditional_residual_standardGaussian {N p : ℕ} (T : Submodule ℝ (TensorSpace N p))
    (f : T→ℝ) (hf : StronglyMeasurable f) :
    (disorderLaw N p)[(fun J : Disorder N p => f (T.orthogonalProjectionOnto (WithLp.toLp 2 J))) |
      disclosedSigma T]=ᵐ[disorderLaw N p] fun _ => ∫x : T,f x ∂stdGaussian T := by
  let X := fun J : Disorder N p => T.orthogonalProjectionOnto (WithLp.toLp 2 J)
  let Y := fun J : Disorder N p => Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J)
  have hx : Measurable X := by fun_prop
  have hy : Measurable Y := by fun_prop
  have hm₁ : MeasurableSpace.comap X (inferInstance : MeasurableSpace T) ≤ (inferInstance : MeasurableSpace (Disorder N p)) := hx.comap_le
  have hm₂ : MeasurableSpace.comap Y (inferInstance : MeasurableSpace Tᗮ) ≤ (inferInstance : MeasurableSpace (Disorder N p)) := hy.comap_le
  have hi : Indep (MeasurableSpace.comap X inferInstance) (MeasurableSpace.comap Y inferInstance)
      (disorderLaw N p) := tensor_subtype_projections_independent T
  have hfx : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (f∘X) :=
    hf.comp_measurable (Measurable.of_comap_le le_rfl)
  have hce := condExp_indep_eq hm₁ hm₂ hfx hi
  have he : (∫J : Disorder N p,(f∘X) J ∂disorderLaw N p)=∫x : T,f x ∂stdGaussian T :=
    (ordered_projection_hasLaw T).integral_comp hf.aestronglyMeasurable
  change (disorderLaw N p)[f∘X | MeasurableSpace.comap Y inferInstance]=ᵐ[disorderLaw N p]
    fun _ => ∫x : T,f x ∂stdGaussian T
  exact hce.trans (ae_of_all _ (fun _ => he))

end SphericalAging.OrthogonalGaussianDisclosure
