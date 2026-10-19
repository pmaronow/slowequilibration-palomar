-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorBandMeasurable
public import SlowEquilibration.SphericalTaylorContinuousLaw

@[expose] public section

/-! At every actual affine critical point the literal original-field band
partition factors into the bottom energy and the actual residual partition. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalLatitudeChartKacRice SlowEquilibration.SphericalForm
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem spherical_partition_add_constant (N : ℕ) (β a : ℝ) (H : Vector N → ℝ) :
    partition N β (fun x => a+H x)=Real.exp (β*a)*partition N β H := by
  unfold partition
  simp_rw [mul_add,Real.exp_add]
  exact integral_const_mul _ _

theorem spherical_logPartition_add_constant {N : ℕ} (hN : 1≤N) (β a : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    Real.log (partition N β (fun x => a+H x))=β*a+Real.log (partition N β H) := by
  rw [spherical_partition_add_constant,Real.log_mul (Real.exp_ne_zero _) (partition_pos hN β hH).ne',
    Real.log_exp]

theorem transverseRemainderField_continuous {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q Q : ℝ) (J : Disorder (n+2) P)
    (y : Vector (n+1)) : Continuous (transverseRemainderField c w e q Q J y) := by
  apply taylorRemainder_parameter_continuous
  unfold transverseOffset
  exact (bottomTransverseFrame e y).continuous.const_smul
    (Real.sqrt (((n+2 : ℕ) : ℝ)*(1-Q)/(Q*(n : ℝ))))

def transverseBandPressure {n : ℕ} (μ : FiniteMixture) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q Q β : ℝ)
    (J : Disorder (n+2) μ.maxDegree) (y : Vector (n+1)) : ℝ :=
  Real.log (partition n β (fun z => fieldOfMixture μ J
    (transverseBandPoint (latitudeMap w e q y) (bottomTransverseFrame e y) Q z)))/((n+2 : ℕ) : ℝ)

/-- A deterministic identity at the actual field's own critical point.
This links the posterior residual estimate back to the physical original
Hamiltonian, with the precise bottom energy and normalization. -/
theorem latitude_critical_transverseBandPressure_identity {n : ℕ} (hn : 1≤n)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0<Q) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) {q : ℝ} (hq : |q|<1) (β : ℝ)
    (J : Disorder (n+2) μ.maxDegree) (y : Vector (n+1)) (hy : ‖y‖^2=((n+1 : ℕ) : ℝ))
    (hcrit : surfaceGradient (latitudeField (centerCoefficients (mixtureCoefficients μ) Q) J w e q) y=0) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    transverseBandPressure μ w e q Q β J y=
      β*latitudeField c J w e q y/((n+2 : ℕ) : ℝ)+
        transverseRemainderPressure c w e q Q β J y := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hfield (z : Vector n) : fieldOfMixture μ J
      (transverseBandPoint (latitudeMap w e q y) (bottomTransverseFrame e y) Q z)=
      latitudeField c J w e q y+transverseRemainderField c w e q Q J y z := by
    have hd := latitude_critical_transverse_derivative_zero c J w e hq y hy hcrit z
    rw [transverseRemainderField,taylorRemainderCLM_actual,transverseOffset,map_smul,hd,smul_zero,sub_zero]
    have hf := field_center_scale (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) hQ.le J
      (latitudeMap w e q y+transverseOffset (bottomTransverseFrame e y) Q z)
    change _=field c J (latitudeMap w e q y)+(field c J _-field c J (latitudeMap w e q y))
    rw [add_sub_cancel]
    exact hf.symm
  unfold transverseBandPressure transverseRemainderPressure
  simp_rw [hfield]
  rw [spherical_logPartition_add_constant hn β _ _
    (transverseRemainderField_continuous c w e q Q J y),add_div]

end
end SlowEquilibration.SphericalTaylorRemainder
