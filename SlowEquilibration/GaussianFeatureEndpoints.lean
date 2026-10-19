-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFeatureHeldPressure
public import SlowEquilibration.SphericalQuenchedEndpoint

/-! Actual physical and linear trial Gaussian endpoints for arbitrary
continuous finite spherical features. Projection preserves the true bank law. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianFeatureDirac

open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

def originalLinear (A : Vector n → EuclideanSpace ℝ ι) (x : Vector n) := innerSL ℝ (A x)

def pressure (A : Vector n → EuclideanSpace ℝ ι) (β : ℝ) : ℝ :=
  GaussianSpinInterpolation.averagedLogPartition (sphereLaw n) (originalLinear A) β/((n+1:ℕ):ℝ)

theorem originalLinear_continuous (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A) :
    Continuous (originalLinear A) := (innerSL ℝ).continuous.comp hA

theorem exists_originalLinear_sphere_bound (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A) :
    ∃ B : ℝ,0≤B ∧ ∀x : Vector n,‖x‖^2=(n:ℝ) → ‖originalLinear A x‖≤B := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector n) (Real.sqrt (n:ℝ))).exists_bound_of_continuousOn
    (originalLinear_continuous A hA).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx
  have hball : x∈Metric.closedBall (0 : Vector n) (Real.sqrt (n:ℝ)) := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    rw [← hx,Real.sqrt_sq (norm_nonneg x)]
  exact (hC x hball).trans (le_max_left _ _)

theorem twoLinear_rotation_zero (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (x : Vector n) (D : EuclideanSpace ℝ (TwoCoordinate n ι)) :
    twoLinear A β k x (GaussianSpinComparison.rotation twoLabel 0 D)=
      originalLinear A x (β • SphericalModel.projectGaussian Sum.inl D) := by
  simp [twoLinear,originalLinear,innerSL_apply_apply,PiLp.inner_apply,RCLike.inner_apply,
    twoFeature,Fintype.sum_sum_type,GaussianSpinComparison.rotation_apply,
    GaussianSpinComparison.rotationCoefficient,twoLabel,SphericalModel.projectGaussian,
    Finset.mul_sum,mul_comm]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem twoLinear_rotation_pi_div_two (A : Vector n → EuclideanSpace ℝ ι) (β k : ℝ)
    (x : Vector n) (D : EuclideanSpace ℝ (TwoCoordinate n ι)) :
    twoLinear A β k x (GaussianSpinComparison.rotation twoLabel (Real.pi/2) D)=
      Real.sqrt k*inner ℝ (SphericalModel.projectGaussian Sum.inr D) x := by
  simp [twoLinear,innerSL_apply_apply,PiLp.inner_apply,RCLike.inner_apply,twoFeature,Fintype.sum_sum_type,
    GaussianSpinComparison.rotation_apply,GaussianSpinComparison.rotationCoefficient,twoLabel,
    SphericalModel.projectGaussian,Finset.mul_sum,mul_assoc,mul_comm]

/-- Exact original Gaussian endpoint, on the original finite coefficient bank. -/
theorem twoMean_zero_eq_original (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k : ℝ) :
    GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n) (twoLinear A β k) twoLabel 0=
      GaussianSpinInterpolation.averagedLogPartition (sphereLaw n) (originalLinear A) β := by
  obtain ⟨B,hB,hbound⟩ := exists_originalLinear_sphere_bound A hA
  have hLb : ∀ᵐ x ∂sphereLaw n,‖originalLinear A x‖≤B := (sphereLaw_support hn).mono fun x hx => hbound x hx
  have hi := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable (sphereLaw n)
    (originalLinear A) (originalLinear_continuous A hA).measurable hB hLb β
  have hlaw := (SphericalModel.projectGaussian_hasLaw (Sum.inl : ι → TwoCoordinate n ι)
    Sum.inl_injective).integral_comp hi.aestronglyMeasurable
  unfold GaussianSpinComparison.averagedRotatedLogPartition GaussianSpinInterpolation.averagedLogPartition
  calc
    _=(∫D : EuclideanSpace ℝ (TwoCoordinate n ι),
      GaussianSpinInterpolation.logPartition (sphereLaw n) (originalLinear A)
        (β • SphericalModel.projectGaussian Sum.inl D)
      ∂SYK.standardGaussianMeasureOnEuclidean (TwoCoordinate n ι)) := by
      apply integral_congr_ae
      exact .of_forall fun D => by
        dsimp only
        unfold GaussianSpinInterpolation.logPartition
        congr 1
        unfold GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight
        apply integral_congr_ae
        exact .of_forall fun x => by
          simp only [twoLinear_rotation_zero]
    _=_ := hlaw

/-- The true independent linear trial endpoint. -/
theorem twoMean_pi_div_two_eq_linear (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (β : ℝ) {k : ℝ} (hk : 0≤k) :
    GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw n) (twoLinear A β k) twoLabel (Real.pi/2)=
      (n:ℝ)*SphericalModel.linearSphereQuenchedPressure n k := by
  have hh := (SphericalModel.projectGaussian_hasLaw (Sum.inr : Fin n → TwoCoordinate n ι)
    Sum.inr_injective).integral_comp (SphericalModel.linearSphereLogPartition_integrable hn hk).aestronglyMeasurable
  have hne : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  rw [SphericalModel.linearSphereQuenchedPressure,mul_div_cancel₀ _ hne]
  unfold GaussianSpinComparison.averagedRotatedLogPartition
  calc
    _=(∫D : EuclideanSpace ℝ (TwoCoordinate n ι),
      Real.log (SphericalModel.partition n 1 (fun x => Real.sqrt k*inner ℝ (SphericalModel.projectGaussian Sum.inr D) x))
      ∂SYK.standardGaussianMeasureOnEuclidean (TwoCoordinate n ι)) := by
      apply integral_congr_ae
      exact .of_forall fun D => by
        change Real.log (GaussianSpinInterpolation.moment (sphereLaw n) (fun _ => 1) (twoLinear A β k)
          (GaussianSpinComparison.rotation twoLabel (Real.pi/2) D))=_
        congr 1
        apply integral_congr_ae
        exact .of_forall fun x => by
          simp only [GaussianSpinInterpolation.weight,one_mul,twoLinear_rotation_pi_div_two]
    _=_ := hh

end SlowEquilibration.GaussianFeatureDirac
