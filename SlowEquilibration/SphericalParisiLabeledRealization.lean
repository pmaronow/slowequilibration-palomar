-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledTrace
public import SlowEquilibration.SphericalParisiLabeledBankPositivity

@[expose] public section

/-! The literal original/trial/perturbation banks with actual external
positive coefficients. All joint coordinate realization and exponent splits
are derived from the original iid Gaussian coordinates, retaining every
physical spin, label and interpolation rotation. -/

namespace SlowEquilibration.SphericalParisiLabeledRealization
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledThreeBlock
open SphericalParisiLabeledTrace SphericalParisiLabeledBankPositivity
open SphericalParisiUnitSpherePositivity SphericalPositivePerturbation
open GaussianCompactFeatureComparison GaussianSpinInterpolation
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

private theorem join_inl {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ κ) (i : ι) :
    sumJoin (u,w) (Sum.inl i)=u i := rfl
private theorem join_inr {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : EuclideanSpace ℝ ι) (w : EuclideanSpace ℝ κ) (i : κ) :
    sumJoin (u,w) (Sum.inr i)=w i := rfl
private theorem join_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u u' : EuclideanSpace ℝ ι) (w w' : EuclideanSpace ℝ κ) :
    inner ℝ (sumJoin (u,w)) (sumJoin (u',w'))=inner ℝ u u'+inner ℝ w w' := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

def parameterDisorder {N k K : ℕ} {d : σ → ℕ} (x : Fin K → ℝ)
    (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    EuclideanSpace ℝ (ThreeCoordinate N k K d) :=
  WithLp.toLp 2 (fun i => match i with
    | .inl _ => D i
    | .inr j => x j.1*D i)

omit [Fintype σ] [DecidableEq σ] in
theorem parameterDisorder_joint_continuous (N k K : ℕ) (d : σ → ℕ) :
    Continuous (fun p : (Fin K → ℝ) × EuclideanSpace ℝ (ThreeCoordinate N k K d) =>
      parameterDisorder p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  cases i with
  | inl j => exact (PiLp.continuous_apply 2 (fun _ : ThreeCoordinate N k K d => ℝ) (.inl j)).comp continuous_snd
  | inr j =>
      exact ((continuous_apply j.1).comp continuous_fst).mul
        ((PiLp.continuous_apply 2 (fun _ : ThreeCoordinate N k K d => ℝ) (.inr j)).comp continuous_snd)

omit [DecidableEq σ] in
theorem parameterDisorder_rotation {N k K : ℕ} (d : σ → ℕ) (x : Fin K → ℝ)
    (θ : ℝ) (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    GaussianThreeBlockComparison.rotation threeLabel θ (parameterDisorder x D)=
      parameterDisorder x (GaussianThreeBlockComparison.rotation threeLabel θ D) := by
  ext i
  cases i with
  | inl j => rfl
  | inr j =>
    simp only [GaussianThreeBlockComparison.rotation_apply,parameterDisorder]
    ring

omit [DecidableEq σ] in
/-- Actual external coefficients may be moved into the same perturbation
Gaussian coordinates, without changing any original or trial coordinate. -/
theorem actual_threeLinear_parameter_realization {N k K : ℕ}
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v : ℝ) (x : Fin K → ℝ)
    (z : UnitSphere N × Fin k) (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    threeLinear d c β q0 q1 v x z D=
      threeLinear d c β q0 q1 v (fun _ => 1) z (parameterDisorder x D) := by
  simp only [threeLinear,innerSL_apply_apply,PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  rw [Fintype.sum_sum_type]
  conv_rhs => rw [Fintype.sum_sum_type]
  simp only [threeFeature,join_inl,join_inr,parameterDisorder]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [SphericalPositivePerturbation.feature,coefficients,mul_one]
  ring

def realizedDisorder (N k K : ℕ) (d : σ → ℕ) (θ : ℝ)
    (p : (Fin K → ℝ) × EuclideanSpace ℝ (ThreeCoordinate N k K d)) :=
  GaussianThreeBlockComparison.rotation threeLabel θ (parameterDisorder p.1 p.2)

omit [DecidableEq σ] in
theorem realizedDisorder_continuous (N k K : ℕ) (d : σ → ℕ) (θ : ℝ) :
    Continuous (realizedDisorder N k K d θ) :=
  (GaussianThreeBlockComparison.rotation threeLabel θ).continuous.comp
    (parameterDisorder_joint_continuous N k K d)

def baseFeature {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 θ : ℝ)
    (z : UnitSphere N × Fin k) : EuclideanSpace ℝ (BaseCoordinate N k d) :=
  sumJoin ((β*Real.cos θ) • originalFeature d c (theta d c q1-theta d c q0) z,
    (β*Real.sin θ) • trialFeature (xi1 d c q0) (xi1 d c q1-xi1 d c q0) z)

def baseLinear {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 θ : ℝ)
    (z : UnitSphere N × Fin k) : EuclideanSpace ℝ (BaseCoordinate N k d) →L[ℝ] ℝ :=
  innerSL ℝ (baseFeature d c β q0 q1 θ z)

omit [DecidableEq σ] in
theorem baseLinear_continuous {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 θ : ℝ) :
    Continuous (baseLinear (N := N) (k := k) d c β q0 q1 θ) := by
  unfold baseLinear baseFeature
  exact (innerSL ℝ).continuous.comp (sumJoin.continuous.comp
    (((actual_originalFeature_continuous d c (theta d c q1-theta d c q0)).const_smul
      (β*Real.cos θ)).prodMk
      ((actual_trialFeature_continuous (xi1 d c q0) (xi1 d c q1-xi1 d c q0)).const_smul
        (β*Real.sin θ))))

omit [DecidableEq σ] in
theorem actual_threeLinear_rotation_split {N k K : ℕ}
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ : ℝ) (x : Fin K → ℝ)
    (z : UnitSphere N × Fin k) (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    threeLinear d c β q0 q1 v x z (GaussianThreeBlockComparison.rotation threeLabel θ D)=
      baseLinear d c β q0 q1 θ z (sumSplit D).1+
        unitSphereLinear (coefficients v x) z.1 (sumSplit D).2 := by
  have hR : (sumSplit (GaussianThreeBlockComparison.rotation threeLabel θ D))=
      (sumJoin (Real.cos θ • (sumSplit (sumSplit D).1).1,
        Real.sin θ • (sumSplit (sumSplit D).1).2),(sumSplit D).2) := by
    apply Prod.ext
    · ext (i|j) <;> simp [sumSplit,GaussianThreeBlockComparison.rotation_apply,
        GaussianThreeBlockComparison.rotationCoefficient,threeLabel,join_inl,join_inr]
    · ext i
      simp [sumSplit,GaussianThreeBlockComparison.rotation_apply,
        GaussianThreeBlockComparison.rotationCoefficient,threeLabel]
  unfold threeLinear
  rw [innerSL_apply_apply,threeFeature,
    ← sumJoin_sumSplit (GaussianThreeBlockComparison.rotation threeLabel θ D),join_inner,hR,join_inner]
  unfold baseLinear baseFeature unitSphereLinear SphericalPositivePerturbation.linear
  rw [innerSL_apply_apply,innerSL_apply_apply,← sumJoin_sumSplit (sumSplit D).1,join_inner]
  simp only [real_inner_smul_left,real_inner_smul_right,sumSplit_sumJoin]
  ring

omit [DecidableEq σ] in
/-- Exact Gibbs-law identity at every coefficient and rotation realization. -/
theorem actual_three_gibbs_realization {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v θ : ℝ) (x : Fin K → ℝ)
    (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    gibbsMeasure ν (GaussianThreeBlockComparison.rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ) D=
      gibbsMeasure ν (threeLinear d c β q0 q1 v (fun _ => 1)) (realizedDisorder N k K d θ (x,D)) := by
  apply gibbsMeasure_congr_field
  exact .of_forall fun z => by
    rw [GaussianThreeBlockComparison.rotatedLinear,ContinuousLinearMap.comp_apply,
      actual_threeLinear_parameter_realization,← parameterDisorder_rotation]
    rfl

end
end SlowEquilibration.SphericalParisiLabeledRealization
