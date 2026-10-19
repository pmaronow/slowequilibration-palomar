-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledStatistics
public import SlowEquilibration.GaussianPerturbationPressureBudget

@[expose] public section

/-! Exact held finite Gaussian perturbation cost for the literal spherical
spin-label model. Gaussian IBP proves monotonicity and the diagonal budget
bound, and the actual unperturbed field is obtained by coordinate deletion. -/

namespace SlowEquilibration.SphericalParisiLabeledHeldPressure
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledThreeBlock
open SphericalParisiLabeledTrace SphericalParisiLabeledRealization SphericalParisiLabeledStatistics
open SphericalPositivePerturbation GaussianCompactFeatureComparison GaussianSpinInterpolation
open GaussianThreeBlockComparison GaussianPerturbationParameter GaussianPerturbationPressureBudget
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def heldLabel {N k K : ℕ} {d : σ → ℕ} : ThreeCoordinate N k K d → Bool
  | .inl _ => false
  | .inr _ => true

omit [DecidableEq σ] in
theorem actual_held_operator_zero {N k K : ℕ} (d : σ → ℕ)
    (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    parameterOperator heldLabel 0 D=parameterDisorder (fun _ : Fin K => 0) D := by
  ext i
  cases i <;> simp [parameterOperator,GaussianSpinComparison.coordinateMask,
    GaussianSpinComparison.diagonal_apply,heldLabel,parameterDisorder]

omit [DecidableEq σ] in
theorem actual_held_operator_one {N k K : ℕ} (d : σ → ℕ)
    (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    parameterOperator heldLabel 1 D=D := by
  ext i
  cases i <;> simp [parameterOperator,GaussianSpinComparison.coordinateMask,
    GaussianSpinComparison.diagonal_apply,heldLabel]

omit [DecidableEq σ] in
theorem actual_held_zero_field {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v θ : ℝ) (x : Fin K → ℝ) (z : UnitSphere N × Fin k)
    (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ z (parameterOperator heldLabel 0 D)=
      threeLinear d c β q0 q1 v (fun _ : Fin K => 0) z (rotation threeLabel θ D) := by
  rw [rotatedLinear,ContinuousLinearMap.comp_apply,actual_held_operator_zero,
    parameterDisorder_rotation,actual_threeLinear_parameter_realization,
    actual_threeLinear_parameter_realization d c β q0 q1 v (fun _ : Fin K => 0)]
  congr 1
  ext i
  cases i with
  | inl j => rfl
  | inr j =>
      change x j.1*(0*_)=0*_
      ring

omit [DecidableEq σ] in
/-- Exact selected perturbation coordinate diagonal of the actual rotated
field, retaining every Gaussian coefficient and true metric unit spin. -/
theorem actual_held_selected_diagonal {N k K : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v θ : ℝ) (x : Fin K → ℝ) (z : UnitSphere N × Fin k) :
    (∑ i : ThreeCoordinate N k K d,if heldLabel i=true then
      (GaussianSpinComparison.coordinateObservable
        (rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ) i z)^2 else 0)=
      ∑ p : Fin K,(coefficients v x p)^2 := by
  simp only [Fintype.sum_sum_type,heldLabel,Bool.false_eq_true,ite_false,ite_true,
    Finset.sum_const_zero,zero_add]
  have hi (i : TensorCoordinate N K) :
      GaussianSpinComparison.coordinateObservable
        (rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ) (.inr i) z=
      SphericalPositivePerturbation.feature (coefficients v x) z.1.val i := by
    change (rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ z)
      (EuclideanSpace.single (.inr i) 1)=_
    rw [rotatedLinear_single,actual_three_coordinate]
    simp [rotationCoefficient,threeLabel,threeFeature,GaussianCompactFeatureComparison.sumJoin]
  simp_rw [hi]
  rw [← EuclideanSpace.real_norm_sq_eq]
  exact SphericalPositivePerturbation.feature_norm_sq _ _ (unit_norm z.1)

omit [DecidableEq σ] in
theorem actual_held_mean_one {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v θ : ℝ) (x : Fin K → ℝ) :
    parameterMean ν (rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ) heldLabel 1=
      averagedRotatedLogPartition ν (threeLinear d c β q0 q1 v x) threeLabel θ := by
  unfold parameterMean parameterLogPartition averagedRotatedLogPartition
  apply integral_congr_ae
  exact .of_forall fun D => by
    dsimp only
    rw [actual_held_operator_one]
    rfl

omit [DecidableEq σ] in
theorem actual_held_mean_zero {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v θ : ℝ) (x : Fin K → ℝ) :
    parameterMean ν (rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ) heldLabel 0=
      averagedRotatedLogPartition ν (threeLinear d c β q0 q1 v (fun _ : Fin K => 0)) threeLabel θ := by
  unfold parameterMean parameterLogPartition averagedRotatedLogPartition
  apply integral_congr_ae
  exact .of_forall fun D => by
    dsimp only
    unfold logPartition
    apply congrArg Real.log
    change (∫ z,1*Real.exp (rotatedLinear (threeLinear d c β q0 q1 v x) threeLabel θ z
      (parameterOperator heldLabel 0 D)) ∂ν)=
      ∫ z,1*Real.exp (threeLinear d c β q0 q1 v (fun _ : Fin K => 0) z
        (rotation threeLabel θ D)) ∂ν
    apply integral_congr_ae
    exact .of_forall fun z => by
      dsimp only
      rw [actual_held_zero_field]

omit [DecidableEq σ] in
/-- True finite held pressure cost is between zero and twice the squared
perturbation strength, with all original/trial coordinates held fixed. -/
theorem actual_held_pressure_increment_mem_Icc {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ : ℝ)
    (x : Fin K → ℝ) (hx : ∀ p,|x p| ≤ 2) :
    averagedRotatedLogPartition ν (threeLinear d c β q0 q1 v x) threeLabel θ-
      averagedRotatedLogPartition ν (threeLinear d c β q0 q1 v (fun _ : Fin K => 0)) threeLabel θ
      ∈ Icc (0 : ℝ) (2*v^2) := by
  let L := threeLinear (N := N) (k := k) d c β q0 q1 v x
  obtain ⟨C,hC,hbound⟩ := actual_threeLinear_bounded (N := N) (k := k) d c β q0 q1 v x
  have hL : Measurable L := (actual_threeLinear_continuous d c β q0 q1 v x).measurable
  have hb : ∀ᵐ z ∂ν,‖L z‖ ≤ C := .of_forall hbound
  have hdiag : ∀ᵐ z ∂ν,(∑ i : ThreeCoordinate N k K d,if heldLabel i=true then
      (GaussianSpinComparison.coordinateObservable (rotatedLinear L threeLabel θ) i z)^2 else 0) ≤ (2*v)^2 :=
    .of_forall fun z => by
      rw [actual_held_selected_diagonal]
      exact coefficients_budget v x hx
  have H := parameterMean_one_sub_zero_mem_Icc ν (rotatedLinear L threeLabel θ)
    (rotatedLinear_measurable L hL threeLabel θ) hC (rotatedLinear_bound ν L hC hb threeLabel θ) heldLabel hdiag
  rw [actual_held_mean_one,actual_held_mean_zero] at H
  simpa only [show (2*v)^2/2=2*v^2 by ring] using H

omit [DecidableEq σ] in
theorem actual_parameter_held_pressure_increment_mem_Icc {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ : ℝ) :
    parameterAveragedPressure (positiveCubeLaw K) ν (threeLinear d c β q0 q1 v) threeLabel θ-
      averagedRotatedLogPartition ν (threeLinear d c β q0 q1 v (fun _ : Fin K => 0)) threeLabel θ
      ∈ Icc (0 : ℝ) (2*v^2) := by
  let Q := averagedRotatedLogPartition ν (threeLinear d c β q0 q1 v (fun _ : Fin K => 0)) threeLabel θ
  let P := fun x : Fin K → ℝ => averagedRotatedLogPartition ν (threeLinear d c β q0 q1 v x) threeLabel θ
  have hi : Integrable P (positiveCubeLaw K) := actual_three_pressure_integrable ν d c β q0 q1 v θ
  have hb : ∀ᵐ x ∂positiveCubeLaw K,P x-Q ∈ Icc (0 : ℝ) (2*v^2) :=
    (positiveCubeLaw_abs_le_two K).mono fun x hx => actual_held_pressure_increment_mem_Icc ν d c β q0 q1 v θ x hx
  have hl := integral_nonneg_of_ae (hb.mono fun x hx => hx.1)
  have hu := integral_mono_ae (hi.sub (integrable_const Q)) (integrable_const (2*v^2))
    (hb.mono fun x hx => hx.2)
  rw [integral_sub hi (integrable_const Q)] at hl
  rw [integral_sub' hi (integrable_const Q)] at hu
  simp only [integral_const,probReal_univ,one_smul] at hl hu
  exact ⟨hl,hu⟩

end
end SlowEquilibration.SphericalParisiLabeledHeldPressure
