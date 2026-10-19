-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFeatureThreeBlock
public import SlowEquilibration.GaussianPerturbationPressureBudget
public import SlowEquilibration.SphericalGuerraBound

/-! True held Gaussian pressure cost for arbitrary continuous original
spherical features and an independent finite perturbation bank. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianFeatureDirac

open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {n : ℕ}

def heldLabel : ThreeCoordinate n ι κ → Bool
  | .inl _ => false
  | .inr _ => true

theorem threeLeft_parameter (t : ℝ) (D : EuclideanSpace ℝ (ThreeCoordinate n ι κ)) :
    threeLeft (GaussianPerturbationParameter.parameterOperator heldLabel t D)=threeLeft D := by
  ext j
  simp [threeLeft,GaussianPerturbationParameter.parameterOperator,
    GaussianSpinComparison.coordinateMask,GaussianSpinComparison.diagonal_apply,heldLabel]

theorem threeRight_parameter (t : ℝ) (D : EuclideanSpace ℝ (ThreeCoordinate n ι κ)) :
    threeRight (GaussianPerturbationParameter.parameterOperator heldLabel t D)=t • threeRight D := by
  ext j
  simp [threeRight,GaussianPerturbationParameter.parameterOperator,
    GaussianSpinComparison.coordinateMask,GaussianSpinComparison.diagonal_apply,heldLabel]

theorem threeLinear_parameter (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (x : Vector n) (θ t : ℝ)
    (D : EuclideanSpace ℝ (ThreeCoordinate n ι κ)) :
    GaussianThreeBlockComparison.rotatedLinear (threeLinear A β k W) threeLabel θ x
      (GaussianPerturbationParameter.parameterOperator heldLabel t D)=
      twoLinear A β k x (GaussianSpinComparison.rotation twoLabel θ (threeLeft D))+
        t*inner ℝ (W x) (threeRight D) := by
  rw [GaussianThreeBlockComparison.rotatedLinear,ContinuousLinearMap.comp_apply,
    threeLinear_rotation,threeLeft_parameter,threeRight_parameter,real_inner_smul_right]

theorem three_selected_diagonal (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (x : Vector n) (θ : ℝ) :
    (∑i : ThreeCoordinate n ι κ,if heldLabel i=true then
      (GaussianSpinComparison.coordinateObservable
        (GaussianThreeBlockComparison.rotatedLinear (threeLinear A β k W) threeLabel θ) i x)^2 else 0)=‖W x‖^2 := by
  simp only [Fintype.sum_sum_type,heldLabel,Bool.false_eq_true,ite_false,ite_true,
    Finset.sum_const_zero,zero_add]
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change (GaussianThreeBlockComparison.rotatedLinear (threeLinear A β k W) threeLabel θ x
    (EuclideanSpace.single (.inr i) 1))^2=(W x i)^2
  rw [GaussianThreeBlockComparison.rotatedLinear_single]
  simp [GaussianThreeBlockComparison.rotationCoefficient,threeLabel,three_coordinate,threeFeature]

theorem three_parameterMean_zero (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k : ℝ) (W : Vector n → EuclideanSpace ℝ κ) (θ : ℝ) :
    GaussianPerturbationParameter.parameterMean (sphereLaw n)
      (GaussianThreeBlockComparison.rotatedLinear (threeLinear A β k W) threeLabel θ) heldLabel 0=
      GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n) (twoLinear A β k) twoLabel θ := by
  obtain ⟨B,hB,hbound⟩ := exists_twoLinear_sphere_bound A hA β k
  have hLb : ∀ᵐ x ∂sphereLaw n,‖twoLinear A β k x‖≤B :=
    (sphereLaw_support hn).mono fun x hx => hbound x hx
  have hi := GaussianSpinComparison.logPartition_rotated_gaussian_integrable (sphereLaw n)
    (twoLinear A β k) (twoLinear_continuous A hA β k).measurable hB hLb twoLabel θ
  have hlaw := (SphericalModel.projectGaussian_hasLaw
    (Sum.inl : TwoCoordinate n ι → ThreeCoordinate n ι κ) Sum.inl_injective).integral_comp hi.aestronglyMeasurable
  unfold GaussianPerturbationParameter.parameterMean GaussianSpinComparison.averagedRotatedLogPartition
  rw [show (fun D : EuclideanSpace ℝ (ThreeCoordinate n ι κ) =>
      GaussianPerturbationParameter.parameterLogPartition (sphereLaw n)
        (GaussianThreeBlockComparison.rotatedLinear (threeLinear A β k W) threeLabel θ) heldLabel D 0)=
      (fun D => GaussianSpinInterpolation.logPartition (sphereLaw n) (twoLinear A β k)
        (GaussianSpinComparison.rotation twoLabel θ (SphericalModel.projectGaussian Sum.inl D))) by
    funext D
    unfold GaussianPerturbationParameter.parameterLogPartition GaussianSpinInterpolation.logPartition
    congr 1
    unfold GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
    apply integral_congr_ae
    exact .of_forall fun x => by
      dsimp only
      rw [threeLinear_parameter]
      simp only [zero_mul,add_zero,threeLeft,SphericalModel.projectGaussian]]
  exact hlaw

theorem three_parameterMean_one (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (θ : ℝ) :
    GaussianPerturbationParameter.parameterMean (sphereLaw n)
      (GaussianThreeBlockComparison.rotatedLinear (threeLinear A β k W) threeLabel θ) heldLabel 1=
      GaussianThreeBlockComparison.averagedRotatedLogPartition (sphereLaw n) (threeLinear A β k W) threeLabel θ := by
  unfold GaussianPerturbationParameter.parameterMean GaussianThreeBlockComparison.averagedRotatedLogPartition
  apply integral_congr_ae
  exact .of_forall fun (D : EuclideanSpace ℝ (ThreeCoordinate n ι κ)) => by
    have hOp : GaussianPerturbationParameter.parameterOperator heldLabel 1 D=D := by
      ext i
      cases i <;> simp [GaussianPerturbationParameter.parameterOperator,
        GaussianSpinComparison.coordinateMask,GaussianSpinComparison.diagonal_apply,heldLabel]
    dsimp only
    unfold GaussianPerturbationParameter.parameterLogPartition
    rw [hOp]
    rfl

/-- The actual held independent Gaussian bank costs between zero and half
its literal diagonal feature energy, uniformly in both original/trial endpoints. -/
theorem three_mean_increment_mem_Icc (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k : ℝ) (W : Vector n → EuclideanSpace ℝ κ) (hW : Continuous W)
    {a : ℝ} (ha : ∀x : Vector n,‖x‖^2=(n:ℝ) → ‖W x‖^2≤a) (θ : ℝ) :
    GaussianThreeBlockComparison.averagedRotatedLogPartition (sphereLaw n) (threeLinear A β k W) threeLabel θ-
      GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n) (twoLinear A β k) twoLabel θ∈Icc 0 (a/2) := by
  obtain ⟨B,hB,hbound⟩ := exists_threeLinear_sphere_bound A hA β k W hW
  have hLb : ∀ᵐ x ∂sphereLaw n,‖threeLinear A β k W x‖≤B :=
    (sphereLaw_support hn).mono fun x hx => hbound x hx
  have hdiag : ∀ᵐ x ∂sphereLaw n,
      (∑i : ThreeCoordinate n ι κ,if heldLabel i=true then
        (GaussianSpinComparison.coordinateObservable
          (GaussianThreeBlockComparison.rotatedLinear (threeLinear A β k W) threeLabel θ) i x)^2 else 0)≤a := by
    filter_upwards [sphereLaw_support hn] with x hx
    rw [three_selected_diagonal]
    exact ha x hx
  have hm := GaussianPerturbationPressureBudget.parameterMean_one_sub_zero_mem_Icc (sphereLaw n)
    (GaussianThreeBlockComparison.rotatedLinear (threeLinear A β k W) threeLabel θ)
    (GaussianThreeBlockComparison.rotatedLinear_measurable _
      (threeLinear_continuous A hA β k W hW).measurable threeLabel θ)
    hB (GaussianThreeBlockComparison.rotatedLinear_bound (sphereLaw n) _ hB hLb threeLabel θ) heldLabel hdiag
  rw [three_parameterMean_one,three_parameterMean_zero hn A hA β k] at hm
  exact hm

end SlowEquilibration.GaussianFeatureDirac
