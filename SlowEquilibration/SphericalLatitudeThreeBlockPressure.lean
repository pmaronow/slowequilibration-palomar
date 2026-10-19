-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeThreeBlock
public import SlowEquilibration.GaussianPerturbationPressureBudget

@[expose] public section

/-! # The actual held latitude perturbation pressure cost

An arbitrary finite held Gaussian feature changes the genuine latitude
rotation pressure by a quantity between zero and half its diagonal norm
budget. The estimate is uniform in the physical and linear endpoints.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n P : ℕ}

def latitudeHeldLabel : LatitudeThreeCoordinate n P ι → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

omit [DecidableEq ι] in
theorem latitudeThreeLeft_parameter (t : ℝ) (D : LatitudeThreeDisorder n P ι) :
    latitudeThreeLeft (GaussianPerturbationParameter.parameterOperator latitudeHeldLabel t D)=
      latitudeThreeLeft D := by
  ext j
  simp [latitudeThreeLeft,GaussianPerturbationParameter.parameterOperator,
    GaussianSpinComparison.coordinateMask,GaussianSpinComparison.diagonal_apply,latitudeHeldLabel]

omit [DecidableEq ι] in
theorem latitudeThreeRight_parameter (t : ℝ) (D : LatitudeThreeDisorder n P ι) :
    latitudeThreeRight (GaussianPerturbationParameter.parameterOperator latitudeHeldLabel t D)=
      t • latitudeThreeRight D := by
  ext j
  simp [latitudeThreeRight,GaussianPerturbationParameter.parameterOperator,
    GaussianSpinComparison.coordinateMask,GaussianSpinComparison.diagonal_apply,latitudeHeldLabel]

omit [DecidableEq ι] in
theorem latitudeThreeLinear_parameter (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (W : Vector n → EuclideanSpace ℝ ι) (x : Vector n) (θ t : ℝ)
    (D : LatitudeThreeDisorder n P ι) :
    GaussianThreeBlockComparison.rotatedLinear (latitudeThreeLinear c β κ u e q W)
      latitudeThreeLabel θ x (GaussianPerturbationParameter.parameterOperator latitudeHeldLabel t D)=
      latitudeGuerraLinear c β κ u e q x
        (GaussianSpinComparison.rotation latitudeGuerraLabel θ (latitudeThreeLeft D))+
          t*inner ℝ (W x) (latitudeThreeRight D) := by
  rw [GaussianThreeBlockComparison.rotatedLinear,ContinuousLinearMap.comp_apply,
    latitudeThreeLinear_rotation,latitudeThreeLeft_parameter,latitudeThreeRight_parameter,
    real_inner_smul_right]

theorem latitudeThree_selected_diagonal (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (W : Vector n → EuclideanSpace ℝ ι) (x : Vector n) (θ : ℝ) :
    (∑ i : LatitudeThreeCoordinate n P ι,if latitudeHeldLabel i=true then
      (GaussianSpinComparison.coordinateObservable
        (GaussianThreeBlockComparison.rotatedLinear (latitudeThreeLinear c β κ u e q W)
          latitudeThreeLabel θ) i x)^2 else 0)=‖W x‖^2 := by
  simp only [Fintype.sum_sum_type,latitudeHeldLabel,Bool.false_eq_true,ite_false,ite_true,
    Finset.sum_const_zero,zero_add]
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change (GaussianThreeBlockComparison.rotatedLinear (latitudeThreeLinear c β κ u e q W)
    latitudeThreeLabel θ x (EuclideanSpace.single (Sum.inr i) 1))^2=(W x i)^2
  rw [GaussianThreeBlockComparison.rotatedLinear_single]
  simp [GaussianThreeBlockComparison.rotationCoefficient,latitudeThreeLabel,
    latitudeThree_coordinateObservable,latitudeThreeFeature]

omit [DecidableEq ι] in
/-- Removing the held perturbation amplitude zero recovers exactly the
ordinary two-block Gaussian latitude mean; projection preserves its law. -/
theorem latitudeThree_parameterMean_zero (hn : 1 ≤ n) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) (W : Vector n → EuclideanSpace ℝ ι) (θ : ℝ) :
    GaussianPerturbationParameter.parameterMean (sphereLaw n)
      (GaussianThreeBlockComparison.rotatedLinear (latitudeThreeLinear c β κ u e q W)
        latitudeThreeLabel θ) latitudeHeldLabel 0=
      GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n)
        (latitudeGuerraLinear c β κ u e q) latitudeGuerraLabel θ := by
  have hi := GaussianSpinComparison.logPartition_rotated_gaussian_integrable (sphereLaw n)
    (latitudeGuerraLinear c β κ u e q) (latitudeGuerraLinear_measurable c β κ u e q)
    (Real.sqrt_nonneg _) (latitudeGuerraLinear_bound hn c hc β hκ u hu e he hq)
    latitudeGuerraLabel θ
  have hlaw := (projectGaussian_hasLaw
    (Sum.inl : LatitudeGuerraCoordinate n P → LatitudeThreeCoordinate n P ι)
    Sum.inl_injective).integral_comp hi.aestronglyMeasurable
  unfold GaussianPerturbationParameter.parameterMean GaussianSpinComparison.averagedRotatedLogPartition
  rw [show (fun D : LatitudeThreeDisorder n P ι =>
      GaussianPerturbationParameter.parameterLogPartition (sphereLaw n)
        (GaussianThreeBlockComparison.rotatedLinear (latitudeThreeLinear c β κ u e q W)
          latitudeThreeLabel θ) latitudeHeldLabel D 0)=
      (fun D => GaussianSpinInterpolation.logPartition (sphereLaw n)
        (latitudeGuerraLinear c β κ u e q)
          (GaussianSpinComparison.rotation latitudeGuerraLabel θ (projectGaussian Sum.inl D))) by
    funext D
    unfold GaussianPerturbationParameter.parameterLogPartition GaussianSpinInterpolation.logPartition
    congr 1
    unfold GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
    apply integral_congr_ae
    exact .of_forall fun x => by
      dsimp only
      rw [latitudeThreeLinear_parameter]
      simp only [zero_mul,add_zero,latitudeThreeLeft,projectGaussian]]
  exact hlaw

omit [DecidableEq ι] in
/-- Restoring held amplitude one is the literal three-block Gaussian
rotation pressure, with all physical and perturbation coordinates intact. -/
theorem latitudeThree_parameterMean_one (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q : ℝ)
    (W : Vector n → EuclideanSpace ℝ ι) (θ : ℝ) :
    GaussianPerturbationParameter.parameterMean (sphereLaw n)
      (GaussianThreeBlockComparison.rotatedLinear (latitudeThreeLinear c β κ u e q W)
        latitudeThreeLabel θ) latitudeHeldLabel 1=
      GaussianThreeBlockComparison.averagedRotatedLogPartition (sphereLaw n)
        (latitudeThreeLinear c β κ u e q W) latitudeThreeLabel θ := by
  unfold GaussianPerturbationParameter.parameterMean
    GaussianThreeBlockComparison.averagedRotatedLogPartition
  apply integral_congr_ae
  exact .of_forall fun (D : LatitudeThreeDisorder n P ι) => by
    have hOp : GaussianPerturbationParameter.parameterOperator latitudeHeldLabel 1 D=D := by
      ext i
      cases i <;> simp [GaussianPerturbationParameter.parameterOperator,
        GaussianSpinComparison.coordinateMask,GaussianSpinComparison.diagonal_apply,latitudeHeldLabel]
    dsimp only
    unfold GaussianPerturbationParameter.parameterLogPartition
    rw [hOp]
    rfl

/-- The true held Gaussian perturbation costs at most a/2 in unnormalized
pressure, uniformly throughout the actual latitude interpolation. -/
theorem latitudeThree_mean_increment_mem_Icc (hn : 1 ≤ n) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) (W : Vector n → EuclideanSpace ℝ ι) (hW : Continuous W)
    {a : ℝ} (ha : ∀ x : Vector n,‖x‖^2=(n : ℝ) → ‖W x‖^2 ≤ a) (θ : ℝ) :
    GaussianThreeBlockComparison.averagedRotatedLogPartition (sphereLaw n)
      (latitudeThreeLinear c β κ u e q W) latitudeThreeLabel θ-
      GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n)
        (latitudeGuerraLinear c β κ u e q) latitudeGuerraLabel θ ∈ Icc 0 (a/2) := by
  obtain ⟨K,hK,hb⟩ := exists_latitudeThreeLinear_sphere_bound c β κ u e q W hW
  have hbs : ∀ᵐ x ∂sphereLaw n,‖latitudeThreeLinear c β κ u e q W x‖ ≤ K :=
    (sphereLaw_support hn).mono fun x hx => hb x hx
  have hdiag : ∀ᵐ x ∂sphereLaw n,
      (∑ i : LatitudeThreeCoordinate n P ι,if latitudeHeldLabel i=true then
        (GaussianSpinComparison.coordinateObservable
          (GaussianThreeBlockComparison.rotatedLinear (latitudeThreeLinear c β κ u e q W)
            latitudeThreeLabel θ) i x)^2 else 0) ≤ a := by
    filter_upwards [sphereLaw_support hn] with x hx
    rw [latitudeThree_selected_diagonal]
    exact ha x hx
  have hm := GaussianPerturbationPressureBudget.parameterMean_one_sub_zero_mem_Icc (sphereLaw n)
    (GaussianThreeBlockComparison.rotatedLinear (latitudeThreeLinear c β κ u e q W) latitudeThreeLabel θ)
    (GaussianThreeBlockComparison.rotatedLinear_measurable _
      (latitudeThreeLinear_continuous c β κ u e q W hW).measurable latitudeThreeLabel θ)
    hK (GaussianThreeBlockComparison.rotatedLinear_bound (sphereLaw n) _ hK hbs latitudeThreeLabel θ)
    latitudeHeldLabel hdiag
  rw [latitudeThree_parameterMean_one,latitudeThree_parameterMean_zero hn c hc β hκ u hu e he hq] at hm
  exact hm

end
end SlowEquilibration.SphericalModel
