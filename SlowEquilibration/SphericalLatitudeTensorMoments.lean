-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalUniformWickMoments
public import SlowEquilibration.SphericalLatitudeFrameParseval
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact affine-latitude tensor moments for the literal physical latitude
measure. The actual tangent frame gives the source projection covariance
Π_x, and the Gaussian-derived even coefficient is uniformly bounded. -/

@[expose] public section
namespace SlowEquilibration.SphericalLatitudeTensorMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open SphericalUniformWickMoments FourPapersCommon
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def latitudeScale (n : ℕ) (r : ℝ) : ℝ := Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))
def latitudeWickCoefficient (n : ℕ) (r : ℝ) (p : ℕ) : ℝ :=
  (latitudeScale n r)^p*sphereWickCoefficient n p

/-- Finite-dimensional curvature normalization is controlled uniformly
in latitude and dimension, including the actual n+1 over n correction. -/
theorem latitudeWickCoefficient_even_mem {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    (hr : |r| ≤ 1) (j : ℕ) : latitudeWickCoefficient n r (2*j) ∈ Icc 0 (2^j) := by
  have hm := sphereWickCoefficient_even_mem_unit hn j
  have hratio : ((n+1 : ℕ) : ℝ)/(n : ℝ) ≤ 2 := by
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).mpr
    push_cast
    linarith
  have hrad : 0 ≤ ((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2) := by
    have hs : 0 ≤ 1-r^2 := by nlinarith [abs_le.mp hr]
    positivity
  have hradle : ((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2) ≤ 2 := by
    calc
      _ ≤ ((n+1 : ℕ) : ℝ)/(n : ℝ)*1 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg r]) (by positivity)
      _ ≤ 2 := by simpa only [mul_one] using hratio
  have he : (latitudeScale n r)^(2*j)=
      (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))^j := by
    rw [pow_mul,latitudeScale,Real.sq_sqrt hrad]
  constructor
  · exact mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) hm.1
  · unfold latitudeWickCoefficient
    rw [he]
    apply (mul_le_mul_of_nonneg_left hm.2 (pow_nonneg hrad j)).trans
    simp only [mul_one]
    exact pow_le_pow_left₀ hrad hradle j

private theorem inner_frame {n : ℕ} (e : Vector n →ₗᵢ[ℝ] Vector (n+1))
    (a : Vector (n+1)) (y : Vector n) :
    inner ℝ a (e y)=inner ℝ (e.toContinuousLinearMap.adjoint a) y :=
  (e.toContinuousLinearMap.adjoint_inner_left y a).symm

/-- Exact centered latitude Wick identity with its concrete frame covariance. -/
theorem actual_latitude_centered_product_eq_wick {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (r : ℝ)
    {κ : Type} [DecidableEq κ] (I : Finset κ) (a : κ → Vector (n+1)) :
    (∫ v : Vector (n+1),∏ i ∈ I,inner ℝ (a i) (v-r•u)
      ∂SphericalModel.latitudeLaw u e r)=
      latitudeWickCoefficient n r I.card*
        covarianceWickSum (fun i j => inner ℝ (e.toContinuousLinearMap.adjoint (a i))
          (e.toContinuousLinearMap.adjoint (a j))) I := by
  rw [SphericalModel.latitudeLaw,integral_map
    (SphericalModel.latitudeMap_continuous u e r).measurable.aemeasurable (by fun_prop)]
  simp only [SphericalModel.latitudeMap,add_sub_cancel_left,
    real_inner_smul_right,inner_frame,Finset.prod_mul_distrib,Finset.prod_const]
  rw [integral_const_mul,actual_sphere_finset_linear_product_eq_wick hn]
  unfold latitudeWickCoefficient latitudeScale
  ring

/-- The actual canonical latitude covariance is the source Π_x contraction. -/
theorem actual_latitude_centered_projection_wick {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (r : ℝ)
    {κ : Type} [DecidableEq κ] (I : Finset κ) (a : κ → Vector (n+1)) :
    (∫ v : Vector (n+1),∏ i ∈ I,inner ℝ (a i) (v-r•u)
      ∂SphericalModel.latitudeLaw u (SphericalModel.latitudeFrameAt u) r)=
      latitudeWickCoefficient n r I.card*
        covarianceWickSum (fun i j => inner ℝ (a i) (a j)-
          inner ℝ (a i) u*inner ℝ (a j) u/((n+1 : ℕ) : ℝ)) I := by
  rw [actual_latitude_centered_product_eq_wick hn]
  simp_rw [SphericalModel.latitudeFrameAt_adjoint_inner u hu]

/-- All odd centered physical latitude tensor moments vanish exactly. -/
theorem actual_latitude_centered_product_odd_zero {n : ℕ}
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (r : ℝ)
    {κ : Type} [DecidableEq κ] (I : Finset κ) (hI : Odd I.card)
    (a : κ → Vector (n+1)) :
    (∫ v : Vector (n+1),∏ i ∈ I,inner ℝ (a i) (v-r•u)
      ∂SphericalModel.latitudeLaw u e r)=0 := by
  rw [SphericalModel.latitudeLaw,integral_map
    (SphericalModel.latitudeMap_continuous u e r).measurable.aemeasurable (by fun_prop)]
  simp only [SphericalModel.latitudeMap,add_sub_cancel_left,
    real_inner_smul_right,inner_frame,Finset.prod_mul_distrib,Finset.prod_const]
  rw [integral_const_mul,actual_sphere_finset_linear_product_odd_zero _ hI,mul_zero]

/-- Literal affine latitude expansion, summing true Π_x Wick contractions
against the uncontracted center coordinates. -/
theorem actual_latitude_product_eq_wick_expansion {n : ℕ} (hn : 1 ≤ n)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (r : ℝ)
    {κ : Type} [DecidableEq κ] (I : Finset κ) (a : κ → Vector (n+1)) :
    (∫ v : Vector (n+1),∏ i ∈ I,inner ℝ (a i) v
      ∂SphericalModel.latitudeLaw u e r)=
      ∑ S ∈ I.powerset,(∏ i ∈ I\S,r*inner ℝ (a i) u)*
        (latitudeWickCoefficient n r S.card*
          covarianceWickSum (fun i j => inner ℝ (e.toContinuousLinearMap.adjoint (a i))
            (e.toContinuousLinearMap.adjoint (a j))) S) := by
  let f : κ → Vector n → ℝ := fun i y => latitudeScale n r*
    inner ℝ (e.toContinuousLinearMap.adjoint (a i)) y
  let g : κ → ℝ := fun i => r*inner ℝ (a i) u
  have hprod (y : Vector n) :
      (∏ i ∈ I,inner ℝ (a i) (SphericalModel.latitudeMap u e r y))=
        ∑ S ∈ I.powerset,(∏ i ∈ S,f i y)*(∏ i ∈ I\S,g i) := by
    simp only [SphericalModel.latitudeMap,inner_add_right,real_inner_smul_right,inner_frame]
    rw [show (fun i => r*inner ℝ (a i) u+
      Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-r^2))*
        inner ℝ (e.toContinuousLinearMap.adjoint (a i)) y)=(fun i => f i y+g i) by
          funext i;dsimp [f,g,latitudeScale];ring]
    exact Finset.prod_add _ _ I
  have hInt (S : Finset κ) : Integrable
      (fun y : Vector n => (∏ i ∈ S,f i y)*(∏ i ∈ I\S,g i)) (sphereLaw n) := by
    dsimp only [f]
    simp only [Finset.prod_mul_distrib,Finset.prod_const]
    exact ((sphere_finset_linear_product_integrable hn S
      (fun i => e.toContinuousLinearMap.adjoint (a i))).const_mul _).mul_const _
  rw [SphericalModel.latitudeLaw,integral_map
    (SphericalModel.latitudeMap_continuous u e r).measurable.aemeasurable (by fun_prop)]
  simp_rw [hprod]
  rw [integral_finsetSum _ (fun S _ => hInt S)]
  apply Finset.sum_congr rfl
  intro S hS
  dsimp only [f,g]
  simp only [Finset.prod_mul_distrib,Finset.prod_const]
  rw [integral_mul_const,integral_const_mul,actual_sphere_finset_linear_product_eq_wick hn]
  unfold latitudeWickCoefficient
  ring

/-- Literal Π_u entries on original ordered coordinate slots. -/
def latitudeProjectionCovariance {n p : ℕ} (u : Vector (n+1))
    (I : TensorIndex (n+1) p) (i j : Fin p) : ℝ :=
  (if I i=I j then 1 else 0)-u (I i)*u (I j)/((n+1 : ℕ) : ℝ)

/-- Finite actual tensor moment formula before choosing a disorder sample. -/
def orderedLatitudeWickMoment (n p : ℕ) (u : Vector (n+1)) (r : ℝ)
    (I : TensorIndex (n+1) p) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin p)).powerset,
    (∏ k ∈ Finset.univ\S,r*u (I k))*(latitudeWickCoefficient n r S.card*
      covarianceWickSum (latitudeProjectionCovariance u I) S)

/-- Exact mean of every original ordered monomial on the actual latitude. -/
theorem actual_latitude_tensorMonomial_eq_wick {n : ℕ} (hn : 1 ≤ n) (p : ℕ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (r : ℝ)
    (I : TensorIndex (n+1) p) :
    (∫ v : Vector (n+1),tensorMonomial v I
      ∂SphericalModel.latitudeLaw u (SphericalModel.latitudeFrameAt u) r)=
      orderedLatitudeWickMoment n p u r I := by
  have h := actual_latitude_product_eq_wick_expansion hn u
    (SphericalModel.latitudeFrameAt u) r Finset.univ
    (fun k : Fin p => EuclideanSpace.basisFun (Fin (n+1)) ℝ (I k))
  simp_rw [SphericalModel.latitudeFrameAt_adjoint_inner u hu] at h
  have he (i j : Fin p) :
      inner ℝ (EuclideanSpace.basisFun (Fin (n+1)) ℝ (I i))
        (EuclideanSpace.basisFun (Fin (n+1)) ℝ (I j))=
        if I i=I j then 1 else 0 :=
    orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin (n+1)) ℝ).orthonormal _ _
  simp only [EuclideanSpace.basisFun_inner,he] at h
  have hc : (fun i j => (if I i=I j then (1 : ℝ) else 0)-
      u (I i)*u (I j)/((n+1 : ℕ) : ℝ))=latitudeProjectionCovariance u I := by
    funext i j
    rfl
  rw [hc] at h
  exact h

/-- Integrability follows from true latitude support, with no moment premise. -/
theorem actual_latitude_tensorMonomial_integrable {n : ℕ} (hn : 1 ≤ n) (p : ℕ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r| ≤ 1)
    (I : TensorIndex (n+1) p) :
    Integrable (fun v : Vector (n+1) => tensorMonomial v I)
      (SphericalModel.latitudeLaw u (SphericalModel.latitudeFrameAt u) r) := by
  apply Integrable.of_bound (by unfold tensorMonomial;fun_prop) ((Real.sqrt (n+1 : ℕ))^p)
  filter_upwards [SphericalModel.latitudeLaw_support hn u hu
    (SphericalModel.latitudeFrameAt u) (SphericalModel.latitudeFrameAt_orthogonal u hu) hr] with v hv
  have hvn := SphericalAging.LandscapeDerivatives.sphere_norm v hv.1
  rw [Real.norm_eq_abs,tensorMonomial,Finset.abs_prod]
  calc
    _ ≤ ∏ _k : Fin p,Real.sqrt (n+1 : ℕ) := by
      apply Finset.prod_le_prod₀ (fun k _ => abs_nonneg _)
      intro k hk
      have hb := abs_real_inner_le_norm
        (EuclideanSpace.basisFun (Fin (n+1)) ℝ (I k)) v
      simpa only [EuclideanSpace.basisFun_inner,
        (EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one,hvn,one_mul] using hb
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- Actual physical Hamiltonian latitude mean, with all true ordered
coefficients and Π_u contractions retained in the finite Wick sum. -/
theorem actual_orderedHamiltonian_latitude_mean {n : ℕ} (hn : 1 ≤ n) (p : ℕ)
    (J : SphericalAging.FiniteModel.Disorder (n+1) p)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : |r| ≤ 1) :
    (∫ v : Vector (n+1),Hamiltonian (n+1) p J v
      ∂SphericalModel.latitudeLaw u (SphericalModel.latitudeFrameAt u) r)=
      normalization (n+1) p*∑ I : TensorIndex (n+1) p,J I*orderedLatitudeWickMoment n p u r I := by
  unfold Hamiltonian
  rw [integral_const_mul,integral_finsetSum _ (fun I _ =>
    (actual_latitude_tensorMonomial_integrable hn p u hu hr I).const_mul (J I))]
  apply congrArg (fun z => normalization (n+1) p*z)
  apply Finset.sum_congr rfl
  intro I hI
  rw [integral_const_mul,actual_latitude_tensorMonomial_eq_wick hn p u hu r I]

end
end SlowEquilibration.SphericalLatitudeTensorMoments
