-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianThreeBlockComparison
public import SlowEquilibration.SphericalBankPositivity

/-! Actual original-feature, linear-trial and held-feature Gaussian banks
for arbitrary continuous finite-dimensional spherical feature fields. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianFeatureDirac

open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ}
abbrev TwoCoordinate (n : ℕ) (ι : Type*) := ι ⊕ Fin n
abbrev ThreeCoordinate (n : ℕ) (ι κ : Type*) := (TwoCoordinate n ι) ⊕ κ

def twoLabel : TwoCoordinate n ι → Bool
  | .inl _ => true
  | .inr _ => false

def threeLabel : ThreeCoordinate n ι κ → Fin 3
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => 2

def twoFeature (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ) (x : Vector n) :
    EuclideanSpace ℝ (TwoCoordinate n ι) :=
  WithLp.toLp 2 (fun i => match i with | .inl j => β*A x j | .inr j => Real.sqrt k*x j)

def twoLinear (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ) (x : Vector n) :
    EuclideanSpace ℝ (TwoCoordinate n ι) →L[ℝ] ℝ := innerSL ℝ (twoFeature A β k x)

def threeFeature (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (x : Vector n) : EuclideanSpace ℝ (ThreeCoordinate n ι κ) :=
  WithLp.toLp 2 (fun i => match i with | .inl j => twoFeature A β k x j | .inr j => W x j)

def threeLinear (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (x : Vector n) :
    EuclideanSpace ℝ (ThreeCoordinate n ι κ) →L[ℝ] ℝ := innerSL ℝ (threeFeature A β k W x)

theorem twoFeature_continuous (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A) (β k : ℝ) :
    Continuous (twoFeature A β k) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : TwoCoordinate n ι => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | inl j => exact continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : ι => ℝ) j).comp hA)
  | inr j => exact continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)

theorem twoLinear_continuous (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A) (β k : ℝ) :
    Continuous (twoLinear A β k) := (innerSL ℝ).continuous.comp (twoFeature_continuous A hA β k)

theorem threeFeature_continuous (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (hW : Continuous W) : Continuous (threeFeature A β k W) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ThreeCoordinate n ι κ => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | inl j => exact (PiLp.continuous_apply 2 (fun _ : TwoCoordinate n ι => ℝ) j).comp (twoFeature_continuous A hA β k)
  | inr j => exact (PiLp.continuous_apply 2 (fun _ : κ => ℝ) j).comp hW

theorem threeLinear_continuous (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (hW : Continuous W) : Continuous (threeLinear A β k W) :=
  (innerSL ℝ).continuous.comp (threeFeature_continuous A hA β k W hW)

theorem twoFeature_norm_sq (A : Vector n → EuclideanSpace ℝ ι) (β : ℝ) {k : ℝ} (hk : 0≤k)
    (x : Vector n) : ‖twoFeature A β k x‖^2=β^2*‖A x‖^2+k*‖x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  simp only [twoFeature,Fintype.sum_sum_type,mul_pow,Real.sq_sqrt hk,Finset.mul_sum]

theorem threeFeature_norm_sq (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (x : Vector n) :
    ‖threeFeature A β k W x‖^2=‖twoFeature A β k x‖^2+‖W x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  simp only [threeFeature,Fintype.sum_sum_type]

theorem exists_twoLinear_sphere_bound (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A) (β k : ℝ) :
    ∃ B : ℝ, 0≤B ∧ ∀x : Vector n,‖x‖^2=(n:ℝ) → ‖twoLinear A β k x‖≤B := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector n) (Real.sqrt (n:ℝ))).exists_bound_of_continuousOn
    (twoLinear_continuous A hA β k).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  have hball : x∈Metric.closedBall (0 : Vector n) (Real.sqrt (n:ℝ)) := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    rw [← hx,Real.sqrt_sq (norm_nonneg x)]
  exact (hC x hball).trans (le_max_left _ _)

theorem exists_threeLinear_sphere_bound (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A)
    (β k : ℝ) (W : Vector n → EuclideanSpace ℝ κ) (hW : Continuous W) :
    ∃ B : ℝ, 0≤B ∧ ∀x : Vector n,‖x‖^2=(n:ℝ) → ‖threeLinear A β k W x‖≤B := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector n) (Real.sqrt (n:ℝ))).exists_bound_of_continuousOn
    (threeLinear_continuous A hA β k W hW).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  have hball : x∈Metric.closedBall (0 : Vector n) (Real.sqrt (n:ℝ)) := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    rw [← hx,Real.sqrt_sq (norm_nonneg x)]
  exact (hC x hball).trans (le_max_left _ _)

variable [DecidableEq ι] [DecidableEq κ]

theorem two_coordinate (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ) (x : Vector n)
    (i : TwoCoordinate n ι) :
    GaussianSpinComparison.coordinateObservable (twoLinear A β k) i x=twoFeature A β k x i := by
  rw [GaussianSpinComparison.coordinateObservable,twoLinear,innerSL_apply_apply,EuclideanSpace.inner_single_right]
  simp only [conj_trivial,one_mul]

theorem three_coordinate (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (x : Vector n) (i : ThreeCoordinate n ι κ) :
    GaussianThreeBlockComparison.coordinateObservable (threeLinear A β k W) i x=threeFeature A β k W x i := by
  rw [GaussianThreeBlockComparison.coordinateObservable,threeLinear,innerSL_apply_apply,EuclideanSpace.inner_single_right]
  simp only [conj_trivial,one_mul]

theorem three_signedKernel_eq (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (x y : Vector n) :
    GaussianThreeBlockComparison.signedKernel (threeLinear A β k W) threeLabel x y=
      GaussianSpinComparison.signedKernel (twoLinear A β k) twoLabel x y := by
  unfold GaussianThreeBlockComparison.signedKernel GaussianSpinComparison.signedKernel
  simp only [three_coordinate,two_coordinate,Fintype.sum_sum_type,
    GaussianThreeBlockComparison.covarianceSign,GaussianSpinComparison.covarianceSign,
    threeLabel,twoLabel,threeFeature,twoFeature,Bool.false_eq_true,ite_true,ite_false]
  norm_num

theorem two_signedKernel (A : Vector n → EuclideanSpace ℝ ι) (β : ℝ) {k : ℝ} (hk : 0≤k)
    (x y : Vector n) :
    GaussianSpinComparison.signedKernel (twoLinear A β k) twoLabel x y=
      k*inner ℝ x y-β^2*inner ℝ (A x) (A y) := by
  unfold GaussianSpinComparison.signedKernel
  simp only [two_coordinate,Fintype.sum_sum_type,GaussianSpinComparison.covarianceSign,
    twoLabel,twoFeature,Bool.false_eq_true,ite_true,ite_false]
  have hm : (∑i : ι,-1*((β*A x i)*(β*A y i))) =-β^2*inner ℝ (A x) (A y) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hl : (∑i : Fin n,1*((Real.sqrt k*x i)*(Real.sqrt k*y i)))=k*inner ℝ x y := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _=(Real.sqrt k)^2*(y i*x i) := by ring
      _=_ := by rw [Real.sq_sqrt hk]
  rw [hm,hl]
  ring

def threeLeft (D : EuclideanSpace ℝ (ThreeCoordinate n ι κ)) : EuclideanSpace ℝ (TwoCoordinate n ι) :=
  WithLp.toLp 2 (fun j => D (.inl j))
def threeRight (D : EuclideanSpace ℝ (ThreeCoordinate n ι κ)) : EuclideanSpace ℝ κ :=
  WithLp.toLp 2 (fun j => D (.inr j))

theorem threeLinear_rotation (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (W : Vector n → EuclideanSpace ℝ κ) (x : Vector n) (θ : ℝ)
    (D : EuclideanSpace ℝ (ThreeCoordinate n ι κ)) :
    threeLinear A β k W x (GaussianThreeBlockComparison.rotation threeLabel θ D)=
      twoLinear A β k x (GaussianSpinComparison.rotation twoLabel θ (threeLeft D))+
        inner ℝ (W x) (threeRight D) := by
  simp only [threeLinear,twoLinear,innerSL_apply_apply,PiLp.inner_apply,RCLike.inner_apply,
    conj_trivial,Fintype.sum_sum_type,GaussianThreeBlockComparison.rotation_apply,
    GaussianSpinComparison.rotation_apply,GaussianThreeBlockComparison.rotationCoefficient,
    GaussianSpinComparison.rotationCoefficient,threeLabel,twoLabel,threeFeature,twoFeature,threeLeft,threeRight,ite_true]
  norm_num

end SlowEquilibration.GaussianFeatureDirac
