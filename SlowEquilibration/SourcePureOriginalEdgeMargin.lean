-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureOriginalComplexityEnvelope
public import SlowEquilibration.SourcePhysicalPurePairSelectionFailureProbability

/-! The source pure ground energy for the original amplitude-one field is
strictly outside the GOE spectral edge. -/

@[expose] public section
namespace SlowEquilibration.SourcePureOriginalEdgeMargin
noncomputable section
open Set SphericalMarkedWindows SphericalTAPCertificate
open TwoAtomStationarity PureStationarity
open SphericalPureCapSourceScalars
open PairConditionalDeterminantMoments
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem source_pure_original_ground_energy_above_edge
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    2*Real.sqrt ((p:ℝ)*((p:ℝ)-1)) <
      (p:ℝ)*pureEnergyConstant p (by omega) := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let q := Real.sqrt Q
  have hq : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hqp : 0 < q^p := pow_pos hq _
  have hqpow : Q^p = (q^p)^2 := by
    rw [←pow_mul,show p*2=2*p by omega,pow_mul,Real.sq_sqrt h.overlap_range.1.le]
  have hcov : Q^2*μ.xi2 Q =
      (p:ℝ)*((p:ℝ)-1)*Q^p := by
    rw [pure_xi2 p (by omega) Q]
    calc
      Q^2*((p:ℝ)*((p:ℝ)-1)*Q^(p-2)) =
          (p:ℝ)*((p:ℝ)-1)*(Q^2*Q^(p-2)) := by ring
      _ = (p:ℝ)*((p:ℝ)-1)*Q^p := by
        rw [←pow_add,show 2+(p-2)=p by omega]
  have hp1 : 1 ≤ (p:ℝ) := by exact_mod_cast (show 1 ≤ p by omega)
  have hbase : 0 ≤ (p:ℝ)*((p:ℝ)-1) := mul_nonneg (by positivity) (by linarith)
  have hsqrt : Real.sqrt (Q^2*μ.xi2 Q) =
      Real.sqrt ((p:ℝ)*((p:ℝ)-1))*q^p := by
    rw [hcov,hqpow,Real.sqrt_mul hbase,Real.sqrt_sq_eq_abs,
      abs_of_pos hqp]
  have hmark := source_pure_markK_eq_degree_mul_markE p (by omega)
    1 (by positivity) h
  have hcoords := sourcePure_certificate_scalar_coordinates p hp h
  have hedge : 2*Real.sqrt (Q^2*μ.xi2 Q) < markK μ β Q :=
    sourceContact_markK_above_edge μ h
  rw [hmark,hcoords.1,hsqrt] at hedge
  have hh : (2*Real.sqrt ((p:ℝ)*((p:ℝ)-1)))*q^p <
      ((p:ℝ)*pureEnergyConstant p (by omega))*q^p := by
    convert hedge using 1 <;> ring
  exact (mul_lt_mul_iff_of_pos_right hqp).mp hh

end
end SlowEquilibration.SourcePureOriginalEdgeMargin
