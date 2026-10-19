-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureKilledCommutatorEnergy
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceGradient

/-! The original tensor Hamiltonian as genuine general-field data, with
the linear entropy/Fisher constant supplied by tensor regularity. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
open MeasureTheory Filter Set SphericalModel SphericalForm
open SphericalAging HardSphereDynamics
open scoped NNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 600000

def FieldData.ofOriginal {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) : FieldData N := by
  have hH := fieldOfMixture_contDiff μ J
  let hBound := (isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).exists_bound_of_continuousOn
    hH.continuous.continuousOn
  let C := hBound.choose
  have hC := hBound.choose_spec
  refine { dimension_ge_one := hN
           hamiltonian := fieldOfMixture μ J
           hamiltonian_contDiff := hH.of_le (by simp)
           approximants := ⟨fun _ => μ,fun _ => J,C,fun _ => 0,?_,?_,?_,?_,?_⟩ }
  · intro j x hx
    have hn := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
    have hxball : x ∈ Metric.closedBall 0 (Real.sqrt (N : ℝ)) := by
      rw [Metric.mem_closedBall, dist_zero_right, hn]
    have hb := hC x hxball
    simpa only [Real.norm_eq_abs] using hb
  · intro x hx
    exact tendsto_const_nhds
  · intro j
    exact le_rfl
  · intro j x hx
    simp
  · exact tendsto_const_nhds

theorem FieldData.ofOriginal_hamiltonian {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree) :
    (FieldData.ofOriginal hN μ J).hamiltonian = fieldOfMixture μ J := rfl

theorem original_regular_hamiltonian_bound {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (hJ : J ∈ regularDisorder)
    (x : Vector N) (hx : OnSphere x) :
    |(FieldData.ofOriginal hN μ J).hamiltonian x| ≤
      derivativeConstant (mixtureCoefficients μ)*(N : ℝ) := by
  have hn := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  exact (field_regularDisorder_ball_bounds hN (mixtureCoefficients μ) J hJ x hn.le).1

/-- The genuine original-field reference has the source linear-in-N
Fisher constant; no entropy, spectral-gap or reference-equation hypothesis
is supplied by the caller. -/
theorem original_regular_reference_fisher {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (hJ : J ∈ regularDisorder)
    (β : ℝ) (hβ : 0 ≤ β) (θ : ℝ≥0) (hθ : 0 < θ) :
    let D := FieldData.ofOriginal hN μ J
    ∃ u : sphericalSobolevGraph hN β D.hamiltonian D.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map hN β D.hamiltonian D.hamiltonian_contDiff.continuous u =
        referenceRate D β θ (referenceInitialVector D β) ∧
      0 ≤ sphericalFisher hN β D.hamiltonian D.hamiltonian_contDiff.continuous u ∧
      sphericalFisher hN β D.hamiltonian D.hamiltonian_contDiff.continuous u ≤
        (θ : ℝ)*(2*Real.log 2+4*β*derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) := by
  dsimp only
  have hB : 0 ≤ derivativeConstant (mixtureCoefficients μ)*(N : ℝ) :=
    mul_nonneg (derivativeConstant_pos _).le (Nat.cast_nonneg N)
  have hf := referenceRate_initial_fisher_bound (FieldData.ofOriginal hN μ J)
    β hβ (derivativeConstant (mixtureCoefficients μ)*(N : ℝ)) hB
    (original_regular_hamiltonian_bound hN μ J hJ) θ hθ
  simpa only [mul_assoc] using hf

end SlowEquilibration.ConditionedEntrance.SmoothKilledGeneral
