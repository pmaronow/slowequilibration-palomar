module

public import SphericalAging.TensorOrthogonalAction

public section

/-! Actual Hamiltonian, gradient and hard-drift equivariance under the
literal tensor orthogonal action, with the genuine disorder law preserved. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.TensorHamiltonianRotation
open Set MeasureTheory ProbabilityTheory FiniteModel HardSphereDynamics LandscapeDerivatives
open AdaptiveGradientDisclosure TensorOrthogonalAction OrthogonalGaussianDisclosure
open scoped InnerProductSpace BigOperators

@[expose]  def rotatedDisorder {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (J : Disorder N p) : Disorder N p :=
  (action O (WithLp.toLp 2 J)).ofLp

 theorem Hamiltonian_eq_tensor_inner {N p : ℕ} (J : Disorder N p) (x : Vector N) :
    Hamiltonian N p J x=normalization N p*⟪WithLp.toLp 2 J,pureTensor (fun _ : Fin p => x)⟫_ℝ := by
  rw [Hamiltonian_eq_diagonal,GaussianLandscape.tensorForm_apply]
  simp only [pureTensor,PiLp.inner_apply,WithLp.ofLp_toLp,RCLike.inner_apply,conj_trivial,mul_comm]

 theorem Hamiltonian_rotated {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (J : Disorder N p) (x : Vector N) :
    Hamiltonian N p (rotatedDisorder O J) (O x)=Hamiltonian N p J x := by
  rw [Hamiltonian_eq_tensor_inner,Hamiltonian_eq_tensor_inner,rotatedDisorder,WithLp.toLp_ofLp,
    ←action_pureTensor,(action O).inner_map_map]

 theorem gradient_rotated {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (J : Disorder N p) (x : Vector N) :
    hamiltonianGradient (rotatedDisorder O J) (O x)=O (hamiltonianGradient J x) := by
  have hfun : Hamiltonian N p (rotatedDisorder O J)∘O=Hamiltonian N p J :=
    funext (Hamiltonian_rotated O J)
  have hD := ((Hamiltonian_hasFDerivAt (rotatedDisorder O J) (O x)).comp x
    O.toContinuousLinearMap.hasFDerivAt).fderiv
  rw [hfun] at hD
  apply ext_inner_right ℝ
  intro v
  obtain ⟨y,rfl⟩ := O.surjective v
  rw [O.inner_map_map]
  change ⟪gradient (Hamiltonian N p (rotatedDisorder O J)) (O x),O y⟫_ℝ=
    ⟪gradient (Hamiltonian N p J) x,y⟫_ℝ
  rw [inner_gradient_left,inner_gradient_left,hD,(Hamiltonian_hasFDerivAt (rotatedDisorder O J) (O x)).fderiv]
  rfl

 theorem projection_rotated {N : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (x y : Vector N) :
    projection (O x) (O y)=O (projection x y) := by
  simp only [projection,O.inner_map_map,map_sub,map_smul]

 theorem drift_rotated {N p : ℕ} (β : ℝ) (O : Vector N≃ₗᵢ[ℝ]Vector N) (J : Disorder N p) (x : Vector N) :
    hamiltonianDrift β (rotatedDisorder O J) (O x)=O (hamiltonianDrift β J x) := by
  simp only [hamiltonianDrift,drift,gradient_rotated,projection_rotated,map_sub,map_smul]

 theorem rotatedDisorder_measurable {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) :
    Measurable (rotatedDisorder (p:=p) O) :=
  (PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp
    ((action O).continuous.measurable.comp (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable)

 theorem rotatedDisorder_hasLaw {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) :
    HasLaw (rotatedDisorder (p:=p) O) (disorderLaw N p) (disorderLaw N p) := by
  have hi : HasLaw (fun J : Disorder N p => action O (WithLp.toLp 2 J))
      (stdGaussian (TensorSpace N p)) (disorderLaw N p) :=
    (action_gaussian O).hasLaw.comp (ordered_tensor_hasLaw N p)
  have hback : HasLaw (WithLp.ofLp : TensorSpace N p→Disorder N p)
      (disorderLaw N p) (stdGaussian (TensorSpace N p)) := by
    refine ⟨(PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.aemeasurable,?_⟩
    rw [←(ordered_tensor_hasLaw N p).map_eq,Measure.map_map (by fun_prop) (by fun_prop)]
    rw [show (WithLp.ofLp : TensorSpace N p→Disorder N p)∘WithLp.toLp 2=id by funext J;rfl]
    exact Measure.map_id
  exact hback.comp hi

end SphericalAging.TensorHamiltonianRotation
