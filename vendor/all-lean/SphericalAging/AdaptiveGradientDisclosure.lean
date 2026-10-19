module

public import SphericalAging.LandscapeDerivatives
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

public section

/-! The actual ordered tensor model's deterministic disclosure identity.
Every gradient query at x in W depends only on the orthogonal projection
of disorder outside (W-perp) tensor p. This is the algebraic part of
source 10.6; conditional Gaussian regeneration is a separate prerequisite. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveGradientDisclosure
open Set FiniteModel GaussianLandscape LandscapeDerivatives
open scoped InnerProductSpace BigOperators

@[expose] abbrev TensorSpace (N p : ℕ) := EuclideanSpace ℝ (TensorIndex N p)

@[expose] def pureTensor {N p : ℕ} (v : Fin p→Vector N) : TensorSpace N p :=
  WithLp.toLp 2 (fun I => ∏k : Fin p,v k (I k))

@[expose] def residualTensorSpace {N p : ℕ} (W : Submodule ℝ (Vector N)) : Submodule ℝ (TensorSpace N p) :=
  Submodule.span ℝ (range (fun v : Fin p→Wᗮ => pureTensor (fun k => (v k : Vector N))))

@[expose] def gradientTensor {N p : ℕ} (x y : Vector N) : TensorSpace N p :=
  ∑i : Fin p,pureTensor (Function.update (fun _ => x) i y)

theorem pureTensor_inner {N p : ℕ} (v w : Fin p→Vector N) :
    ⟪pureTensor v,pureTensor w⟫_ℝ=∏k : Fin p,⟪v k,w k⟫_ℝ := by
  classical
  calc
    _ = ∑I : TensorIndex N p,∏k : Fin p,v k (I k)*w k (I k) := by
      simp [pureTensor,PiLp.inner_apply,←Finset.prod_mul_distrib,mul_comm]
    _ = ∏k : Fin p,∑i : Fin N,v k i*w k i := (Fintype.prod_sum (fun k : Fin p => fun i : Fin N => v k i*w k i)).symm
    _ = _ := by simp [PiLp.inner_apply,mul_comm]

theorem updatedTensor_orthogonal {N p : ℕ} (hp : 2≤p) (W : Submodule ℝ (Vector N))
    {x : Vector N} (hx : x∈W) (y : Vector N) (i : Fin p) (v : Fin p→Wᗮ) :
    ⟪pureTensor (fun k => (v k : Vector N)),pureTensor (Function.update (fun _ => x) i y)⟫_ℝ=0 := by
  classical
  letI : Nontrivial (Fin p) := Fintype.one_lt_card_iff_nontrivial.mp (by simp only [Fintype.card_fin];omega)
  obtain ⟨j,hji⟩ := exists_ne i
  rw [pureTensor_inner]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [Function.update_of_ne hji]
  exact Submodule.inner_left_of_mem_orthogonal hx (v j).property

theorem gradientTensor_mem_orthogonal {N p : ℕ} (hp : 2≤p) (W : Submodule ℝ (Vector N))
    {x : Vector N} (hx : x∈W) (y : Vector N) : gradientTensor (p:=p) x y∈(residualTensorSpace (p:=p) W)ᗮ := by
  classical
  intro R hR
  induction hR using Submodule.span_induction with
  | mem R hR =>
    obtain ⟨v,rfl⟩ := hR
    rw [gradientTensor,inner_sum]
    exact Finset.sum_eq_zero (fun i _ => updatedTensor_orthogonal hp W hx y i v)
  | zero => exact inner_zero_left _
  | add u v hu hv ihu ihv => rw [inner_add_left,ihu,ihv,add_zero]
  | smul c v hv ih => rw [real_inner_smul_left,ih,mul_zero]

theorem Hamiltonian_fderiv_eq_tensor_inner {N p : ℕ} (J : Disorder N p) (x y : Vector N) :
    fderiv ℝ (Hamiltonian N p J) x y=
      normalization N p*⟪WithLp.toLp 2 J,gradientTensor x y⟫_ℝ := by
  classical
  rw [(Hamiltonian_hasFDerivAt J x).fderiv]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,diagonalDerivative_apply,
    gradientTensor,inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [tensorForm_apply]
  simp only [pureTensor,PiLp.inner_apply,WithLp.ofLp_toLp,RCLike.inner_apply,conj_trivial,mul_comm]

theorem residual_fderiv_zero {N p : ℕ} (hp : 2≤p) (W : Submodule ℝ (Vector N))
    {R : TensorSpace N p} (hR : R∈residualTensorSpace W) {x : Vector N} (hx : x∈W) :
    fderiv ℝ (Hamiltonian N p R.ofLp) x=0 := by
  ext y
  rw [Hamiltonian_fderiv_eq_tensor_inner,WithLp.toLp_ofLp,
    Submodule.inner_right_of_mem_orthogonal hR (gradientTensor_mem_orthogonal hp W hx y),mul_zero]
  rfl

theorem residual_gradient_zero {N p : ℕ} (hp : 2≤p) (W : Submodule ℝ (Vector N))
    {R : TensorSpace N p} (hR : R∈residualTensorSpace W) {x : Vector N} (hx : x∈W) :
    gradient (Hamiltonian N p R.ofLp) x=0 := by
  rw [gradient,residual_fderiv_zero hp W hR hx,map_zero]

/-- Literal orthogonal projection onto the disclosed tensor subspace. -/
@[expose] def disclosedDisorder {N p : ℕ} (W : Submodule ℝ (Vector N)) (J : Disorder N p) : Disorder N p :=
  ((residualTensorSpace W)ᗮ.starProjection (WithLp.toLp 2 J)).ofLp

/-- Source 10.6(ii), deterministic identity for the actual gradient. -/
theorem gradient_eq_disclosed {N p : ℕ} (hp : 2≤p) (W : Submodule ℝ (Vector N))
    (J : Disorder N p) {x : Vector N} (hx : x∈W) :
    gradient (Hamiltonian N p J) x=gradient (Hamiltonian N p (disclosedDisorder W J)) x := by
  have he : fderiv ℝ (Hamiltonian N p J) x=
      fderiv ℝ (Hamiltonian N p (disclosedDisorder W J)) x := by
    ext y
    rw [Hamiltonian_fderiv_eq_tensor_inner,Hamiltonian_fderiv_eq_tensor_inner]
    congr 1
    rw [disclosedDisorder,WithLp.toLp_ofLp,Submodule.starProjection_orthogonal_val,inner_sub_left]
    have hR : (residualTensorSpace W).starProjection (WithLp.toLp 2 J)∈residualTensorSpace W :=
      ((residualTensorSpace W).orthogonalProjectionOnto (WithLp.toLp 2 J)).property
    rw [Submodule.inner_right_of_mem_orthogonal hR (gradientTensor_mem_orthogonal hp W hx y),sub_zero]
  simp only [gradient,he]

end SphericalAging.AdaptiveGradientDisclosure
