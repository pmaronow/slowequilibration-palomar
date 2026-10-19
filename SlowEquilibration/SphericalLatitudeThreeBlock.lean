-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeGuerra
public import SlowEquilibration.GaussianThreeBlockComparison

@[expose] public section

/-! # Actual latitude interpolation with a held perturbation block

The original latitude and linear trial share the genuine three-block
Gaussian rotation. Every added perturbation coordinate is held fixed and
cancels exactly from the signed covariance kernel.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Metric
open scoped Topology RealInnerProductSpace BigOperators
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι : Type*} [Fintype ι] {n P : ℕ}

abbrev LatitudeThreeCoordinate (n P : ℕ) (ι : Type*) := Sum (LatitudeGuerraCoordinate n P) ι
abbrev LatitudeThreeDisorder (n P : ℕ) (ι : Type*) := EuclideanSpace ℝ (LatitudeThreeCoordinate n P ι)

def latitudeThreeLabel : LatitudeThreeCoordinate n P ι → Fin 3
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr _ => 2

def latitudeThreeFeature (c : Degree P → ℝ) (β κ : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (W : Vector n → EuclideanSpace ℝ ι)
    (x : Vector n) : LatitudeThreeDisorder n P ι :=
  WithLp.toLp 2 (fun i => match i with
    | Sum.inl j => latitudeGuerraFeature c β κ u e q x j
    | Sum.inr j => W x j)

def latitudeThreeLinear (c : Degree P → ℝ) (β κ : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (W : Vector n → EuclideanSpace ℝ ι)
    (x : Vector n) : LatitudeThreeDisorder n P ι →L[ℝ] ℝ :=
  innerSL ℝ (latitudeThreeFeature c β κ u e q W x)

omit [Fintype ι] in
theorem latitudeThreeFeature_continuous (c : Degree P → ℝ) (β κ : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (W : Vector n → EuclideanSpace ℝ ι)
    (hW : Continuous W) : Continuous (latitudeThreeFeature c β κ u e q W) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : LatitudeThreeCoordinate n P ι => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | inl j =>
      exact (PiLp.continuous_apply 2 (fun _ : LatitudeGuerraCoordinate n P => ℝ) j).comp
        (latitudeGuerraFeature_continuous c β κ u e q)
  | inr j => exact (PiLp.continuous_apply 2 (fun _ : ι => ℝ) j).comp hW

theorem latitudeThreeLinear_continuous (c : Degree P → ℝ) (β κ : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (W : Vector n → EuclideanSpace ℝ ι)
    (hW : Continuous W) : Continuous (latitudeThreeLinear c β κ u e q W) :=
  (innerSL ℝ).continuous.comp (latitudeThreeFeature_continuous c β κ u e q W hW)

/-- The operator norm contains exactly the original/trial feature norm and
the held perturbation feature norm. -/
theorem latitudeThreeFeature_norm_sq (c : Degree P → ℝ) (β κ : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (W : Vector n → EuclideanSpace ℝ ι)
    (x : Vector n) :
    ‖latitudeThreeFeature c β κ u e q W x‖^2=
      ‖latitudeGuerraFeature c β κ u e q x‖^2+‖W x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  simp only [latitudeThreeFeature,Fintype.sum_sum_type]

/-- Every actual latitude-plus-perturbation feature has a finite operator
bound on the physical tangent sphere, obtained from its genuine continuity. -/
theorem exists_latitudeThreeLinear_sphere_bound (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (W : Vector n → EuclideanSpace ℝ ι) (hW : Continuous W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : Vector n, ‖x‖^2=(n : ℝ) →
      ‖latitudeThreeLinear c β κ u e q W x‖ ≤ K := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector n) (Real.sqrt (n : ℝ))).exists_bound_of_continuousOn
    (latitudeThreeLinear_continuous c β κ u e q W hW).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  have hball : x∈Metric.closedBall (0 : Vector n) (Real.sqrt (n : ℝ)) := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    rw [← hx,Real.sqrt_sq (norm_nonneg x)]
  exact (hC x hball).trans (le_max_left _ _)

variable [DecidableEq ι]

theorem latitudeThree_coordinateObservable (c : Degree P → ℝ) (β κ : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (W : Vector n → EuclideanSpace ℝ ι)
    (x : Vector n) (i : LatitudeThreeCoordinate n P ι) :
    GaussianThreeBlockComparison.coordinateObservable (latitudeThreeLinear c β κ u e q W) i x=
      latitudeThreeFeature c β κ u e q W x i := by
  rw [GaussianThreeBlockComparison.coordinateObservable,latitudeThreeLinear,innerSL_apply_apply,
    EuclideanSpace.inner_single_right]
  simp only [conj_trivial,one_mul]

/-- Every perturbation coordinate has zero signed covariance contribution,
so the actual old latitude kernel is retained exactly. -/
theorem latitudeThree_signedKernel_eq (c : Degree P → ℝ) (β κ : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (W : Vector n → EuclideanSpace ℝ ι)
    (x y : Vector n) :
    GaussianThreeBlockComparison.signedKernel (latitudeThreeLinear c β κ u e q W) latitudeThreeLabel x y=
      GaussianSpinComparison.signedKernel (latitudeGuerraLinear c β κ u e q) latitudeGuerraLabel x y := by
  unfold GaussianThreeBlockComparison.signedKernel GaussianSpinComparison.signedKernel
  simp only [latitudeThree_coordinateObservable,latitudeGuerra_coordinateObservable,Fintype.sum_sum_type,
    GaussianThreeBlockComparison.covarianceSign,GaussianSpinComparison.covarianceSign,
    latitudeThreeLabel,latitudeGuerraLabel,latitudeThreeFeature,latitudeGuerraFeature,
    Bool.false_eq_true,ite_true,ite_false]
  norm_num

/-- Exact actual latitude covariance kernel with an arbitrary held finite
perturbation bank; no pressure or positivity assumption enters the identity. -/
theorem latitudeThree_signedKernel (hn : 1 ≤ n) (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p)
    (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) (W : Vector n → EuclideanSpace ℝ ι) (x y : Vector n) :
    GaussianThreeBlockComparison.signedKernel (latitudeThreeLinear c β κ u e q W) latitudeThreeLabel x y=
      κ*(n : ℝ)*overlap x y-β^2*((n+1 : ℕ) : ℝ)*
        covariancePolynomial c (q^2+(1-q^2)*overlap x y) := by
  rw [latitudeThree_signedKernel_eq]
  exact latitudeGuerra_signedKernel hn c hc β hκ u hu e he hq x y

/-- Literal original/trial coordinates of the three-block Gaussian bank. -/
def latitudeThreeLeft (D : LatitudeThreeDisorder n P ι) : LatitudeGuerraDisorder n P :=
  WithLp.toLp 2 (fun j => D (Sum.inl j))

/-- Literal coordinates of the held perturbation Gaussian bank. -/
def latitudeThreeRight (D : LatitudeThreeDisorder n P ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun j => D (Sum.inr j))

omit [DecidableEq ι] in
/-- The same actual perturbation field remains in place at every rotation,
including both physical and linear trial endpoints. -/
theorem latitudeThreeLinear_rotation (c : Degree P → ℝ) (β κ : ℝ) (u : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ) (W : Vector n → EuclideanSpace ℝ ι)
    (x : Vector n) (θ : ℝ) (D : LatitudeThreeDisorder n P ι) :
    latitudeThreeLinear c β κ u e q W x (GaussianThreeBlockComparison.rotation latitudeThreeLabel θ D)=
      latitudeGuerraLinear c β κ u e q x
        (GaussianSpinComparison.rotation latitudeGuerraLabel θ (latitudeThreeLeft D))+
          inner ℝ (W x) (latitudeThreeRight D) := by
  simp only [latitudeThreeLinear,latitudeGuerraLinear,innerSL_apply_apply,PiLp.inner_apply,
    RCLike.inner_apply,conj_trivial,Fintype.sum_sum_type,
    GaussianThreeBlockComparison.rotation_apply,GaussianSpinComparison.rotation_apply,
    GaussianThreeBlockComparison.rotationCoefficient,GaussianSpinComparison.rotationCoefficient,
    latitudeThreeLabel,latitudeGuerraLabel,latitudeThreeFeature,latitudeGuerraFeature,
    latitudeThreeLeft,latitudeThreeRight,ite_true]
  norm_num

end
end SlowEquilibration.SphericalModel
