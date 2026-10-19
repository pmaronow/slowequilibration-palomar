-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalDisorderKernelMeasurable
public import SlowEquilibration.SphericalGibbsKernel
public import SlowEquilibration.SphericalUniformStartEntropy

/-! Literal original-base physical reference Laplace expectations are
jointly Borel in the original disorder and initial point. The reference
function is frozen in the independent axis. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalDynamics
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def baseInitialJoint (μ : FiniteMixture) (β : ℝ)
    (q : Disorder N μ.maxDegree × Vector N) : ℝ :=
  1+uniformInitialDensity N β (fieldOfMixture μ q.1) q.2

theorem baseInitialJoint_measurable (μ : FiniteMixture) (β : ℝ) :
    Measurable (baseInitialJoint (N:=N) μ β) := by
  exact measurable_const.add (((partition_measurable (mixtureCoefficients μ) β).comp measurable_fst).mul
    (Real.measurable_exp.comp ((field_jointContinuous (mixtureCoefficients μ)).measurable.const_mul (-β))))

def baseReferenceExpectation (μ : FiniteMixture) (β : ℝ)
    (q : (Disorder N μ.maxDegree × Vector N) × ℝ≥0) : ℝ :=
  ∫ y,baseInitialJoint μ β (q.1.1,y) ∂mixedTransitionKernel μ q.1.1 β q.2 q.1.2

theorem baseReferenceExpectation_measurable (μ : FiniteMixture) (β : ℝ) :
    Measurable (baseReferenceExpectation (N:=N) μ β) :=
  mixedTransitionKernel_joint_integral_measurable μ β
    (fun z => baseInitialJoint μ β (z.1.1.1,z.2))
    ((baseInitialJoint_measurable μ β).comp
      ((measurable_fst.fst.fst).prodMk measurable_snd))

/-- Actual unconditioned Brownian transition expectation integrated at the
literal source rate; its disorder is unchanged by the reference process. -/
def uniformBaseReference (μ : FiniteMixture) (β : ℝ) (θ : ℝ≥0)
    (q : Disorder N μ.maxDegree × Vector N) : ℝ :=
  (θ : ℝ)*∫ t : ℝ in Ioi 0,Real.exp (-(θ : ℝ)*t)*baseReferenceExpectation μ β (q,t.toNNReal)

theorem uniformBaseReference_measurable (μ : FiniteMixture) (β : ℝ) (θ : ℝ≥0) :
    Measurable (uniformBaseReference (N:=N) μ β θ) := by
  have hm : Measurable (fun z : (Disorder N μ.maxDegree × Vector N) × ℝ =>
      Real.exp (-(θ : ℝ)*z.2)*baseReferenceExpectation μ β (z.1,z.2.toNNReal)) :=
    (Real.measurable_exp.comp (measurable_snd.const_mul (-(θ : ℝ)))).mul
      ((baseReferenceExpectation_measurable μ β).comp
        (measurable_fst.prodMk measurable_snd.real_toNNReal))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.const_mul (θ : ℝ)

theorem uniformBaseReference_frozen_axis_measurable (μ : FiniteMixture) (β : ℝ) (θ : ℝ≥0) :
    Measurable (fun q : Vector N × (Disorder N μ.maxDegree × Vector N) =>
      uniformBaseReference μ β θ q.2) :=
  (uniformBaseReference_measurable μ β θ).comp measurable_snd

theorem uniformBaseReference_frozen_axis_integral (μ : FiniteMixture) (β : ℝ) (θ : ℝ≥0)
    (J : Disorder N μ.maxDegree) (x : Vector N) :
    (∫ _u : Vector N,uniformBaseReference μ β θ (J,x) ∂sphereLaw N)=
      uniformBaseReference μ β θ (J,x) := by
  let := sphereLaw_probability N
  simp only [integral_const,probReal_univ,one_smul]

end SlowEquilibration.ConditionedEntrance
