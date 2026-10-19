-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalBaseGibbsPartitionFamily
public import SlowEquilibration.ConditionedEntranceBaseResolventMeasurable
public import SlowEquilibration.SphericalJointKilledVariational

/-! Literal original-base endpoint forcing, with the actual normalizing
sphere partition and its true joint disorder/state continuity. No forcing,
partition, parameter-gradient, or physical-reference conclusion is supplied. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction NNReal ENNReal
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem baseInitialJoint_continuous (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    Continuous (baseInitialJoint (N := N) μ β) := by
  unfold baseInitialJoint uniformInitialDensity
  exact continuous_const.add ((mixturePartition_jointContinuous hN μ β).mul
    (Real.continuous_exp.comp ((field_jointContinuous (mixtureCoefficients μ)).const_mul (-β))))

theorem baseInitialJoint_pos (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (q : Disorder N μ.maxDegree×Vector N) : 0 < baseInitialJoint μ β q := by
  have H := uniformInitialDensity_pos hN β (fieldOfMixture μ q.1)
    (fieldOfMixture_contDiff μ q.1).continuous q.2
  unfold baseInitialJoint
  linarith

/-- The actual rate-scaled forcing for the frozen original-base reference. -/
def baseForcingJoint (μ : FiniteMixture) (β θ : ℝ)
    (q : Disorder N μ.maxDegree×Vector N) : ℝ := θ*baseInitialJoint μ β q

theorem baseForcingJoint_continuous (hN : 1 ≤ N) (μ : FiniteMixture) (β θ : ℝ) :
    Continuous (baseForcingJoint (N := N) μ β θ) :=
  (baseInitialJoint_continuous hN μ β).const_mul θ

theorem baseForcingJoint_pos (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    {θ : ℝ} (hθ : 0 < θ) (q : Disorder N μ.maxDegree×Vector N) :
    0 < baseForcingJoint μ β θ q := mul_pos hθ (baseInitialJoint_pos hN μ β q)

/-- Literal uniform-domain forcing after weighting by exp(beta H0),
retaining its genuine normalizing partition rather than an input scalar. -/
def baseWeightedForcingJoint (μ : FiniteMixture) (β θ : ℝ)
    (q : Disorder N μ.maxDegree×Vector N) : ℝ :=
  θ*(Real.exp (β*fieldOfMixture μ q.1 q.2)+partition N β (fieldOfMixture μ q.1))

theorem baseWeightedForcingJoint_continuous (hN : 1 ≤ N) (μ : FiniteMixture) (β θ : ℝ) :
    Continuous (baseWeightedForcingJoint (N := N) μ β θ) :=
  ((Real.continuous_exp.comp ((field_jointContinuous (mixtureCoefficients μ)).const_mul β)).add
    (mixturePartition_jointContinuous hN μ β)).const_mul θ

/-- Exact pointwise conversion of the actual original-base forcing to
its common-uniform-sphere variational forcing. -/
theorem baseForcingJoint_mul_exp (μ : FiniteMixture) (β θ : ℝ)
    (q : Disorder N μ.maxDegree×Vector N) :
    baseForcingJoint μ β θ q*Real.exp (β*fieldOfMixture μ q.1 q.2)=
      baseWeightedForcingJoint μ β θ q := by
  have he : Real.exp (-β*fieldOfMixture μ q.1 q.2)*
      Real.exp (β*fieldOfMixture μ q.1 q.2)=1 := by
    rw [← Real.exp_add,show -β*fieldOfMixture μ q.1 q.2+β*fieldOfMixture μ q.1 q.2=0 by ring,
      Real.exp_zero]
  unfold baseForcingJoint baseInitialJoint uniformInitialDensity baseWeightedForcingJoint
  calc
    _ = θ*(Real.exp (β*fieldOfMixture μ q.1 q.2)+
        partition N β (fieldOfMixture μ q.1)*
          (Real.exp (-β*fieldOfMixture μ q.1 q.2)*Real.exp (β*fieldOfMixture μ q.1 q.2))) := by ring
    _ = _ := by rw [he,mul_one]

def baseWeightedForcingFamily (hN : 1 ≤ N) (μ : FiniteMixture) (β θ : ℝ) :
    Disorder N μ.maxDegree→Vector N→ᵇℝ :=
  sphericalLocalizedFamily (baseWeightedForcingJoint μ β θ)
    (baseWeightedForcingJoint_continuous hN μ β θ)

theorem baseWeightedForcingFamily_continuous (hN : 1 ≤ N) (μ : FiniteMixture) (β θ : ℝ) :
    Continuous (baseWeightedForcingFamily hN μ β θ) :=
  sphericalLocalizedFamily_continuous _ _

theorem baseWeightedForcingFamily_apply (hN : 1 ≤ N) (μ : FiniteMixture) (β θ : ℝ)
    (J : Disorder N μ.maxDegree) (x : Vector N) :
    baseWeightedForcingFamily hN μ β θ J x=
      sphericalLocalizationBump N x*baseWeightedForcingJoint μ β θ (J,x) := rfl

theorem baseWeightedForcingFamily_ae (hN : 1 ≤ N) (μ : FiniteMixture) (β θ : ℝ)
    (J : Disorder N μ.maxDegree) :
    baseWeightedForcingFamily hN μ β θ J=ᵐ[sphereLaw N]
      fun x => baseWeightedForcingJoint μ β θ (J,x) := by
  have H := sphericalLocalizedFamily_ae hN 0 (fun _ => 0)
    (baseWeightedForcingJoint μ β θ) (baseWeightedForcingJoint_continuous hN μ β θ) J
  rw [gibbsLaw_zeroHamiltonian] at H
  exact H

def baseWeightedForcingL2 (hN : 1 ≤ N) (μ : FiniteMixture) (β θ : ℝ) :
    Disorder N μ.maxDegree→Lp ℝ 2 (sphereLaw N) :=
  let _ := sphereLaw_probability N
  fun J => BoundedContinuousFunction.toLp 2 (sphereLaw N) ℝ
    (baseWeightedForcingFamily hN μ β θ J)

theorem baseWeightedForcingL2_continuous (hN : 1 ≤ N) (μ : FiniteMixture) (β θ : ℝ) :
    Continuous (baseWeightedForcingL2 hN μ β θ) := by
  let _ := sphereLaw_probability N
  exact (BoundedContinuousFunction.toLp 2 (sphereLaw N) ℝ).continuous.comp
    (baseWeightedForcingFamily_continuous hN μ β θ)

theorem baseWeightedForcingL2_ae (hN : 1 ≤ N) (μ : FiniteMixture) (β θ : ℝ)
    (J : Disorder N μ.maxDegree) :
    baseWeightedForcingL2 hN μ β θ J=ᵐ[sphereLaw N]
      fun x => θ*(Real.exp (β*fieldOfMixture μ J x)+partition N β (fieldOfMixture μ J)) := by
  let _ := sphereLaw_probability N
  exact (BoundedContinuousFunction.coeFn_toLp 2 (sphereLaw N) ℝ
    (baseWeightedForcingFamily hN μ β θ J)).trans (baseWeightedForcingFamily_ae hN μ β θ J)

end SlowEquilibration.ConditionedEntrance
