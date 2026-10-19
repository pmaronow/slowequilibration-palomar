-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceAxisDisintegrationL1
public import SlowEquilibration.ConditionedEntranceSquareCommutatorSignedReduction

/-! Integrate a signed source energy inequality against the exact
nonnegative fibre partition-ratio weight. The absolute values are taken
only after both commutators have been integrated. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 300000

theorem signed_fibre_energy_integral
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (t B A R K C : E → ℝ) (lam : ℝ)
    (ht : ∀ᵐ z ∂ν, 0 ≤ t z)
    (hB : Integrable (fun z => t z*B z) ν)
    (hA : Integrable (fun z => t z*A z) ν)
    (hR : Integrable (fun z => t z*R z) ν)
    (hK : Integrable (fun z => t z*K z) ν)
    (hC : Integrable (fun z => t z*C z) ν)
    (hpoint : ∀ᵐ z ∂ν, B z+lam/2*A z ≤
      R z-lam/2*K z-C z) :
    (∫ z, t z*B z ∂ν)+lam/2*(∫ z, t z*A z ∂ν) ≤
      (∫ z, t z*R z ∂ν)-lam/2*(∫ z, t z*K z ∂ν)-
        (∫ z, t z*C z ∂ν) := by
  have hp : ∀ᵐ z ∂ν,
      t z*B z+lam/2*(t z*A z) ≤
        t z*R z-lam/2*(t z*K z)-t z*C z := by
    filter_upwards [ht,hpoint] with z hz he
    have hh := mul_le_mul_of_nonneg_left he hz
    nlinarith
  have hiL : Integrable (fun z => t z*B z+lam/2*(t z*A z)) ν :=
    hB.add (hA.const_mul (lam/2))
  have hiR : Integrable (fun z => t z*R z-lam/2*(t z*K z)-t z*C z) ν :=
    (hR.sub (hK.const_mul (lam/2))).sub hC
  have hm := integral_mono_ae hiL hiR hp
  rw [integral_add hB (hA.const_mul (lam/2)),integral_const_mul] at hm
  have hRK : Integrable (fun z => t z*R z-lam/2*(t z*K z)) ν :=
    hR.sub (hK.const_mul (lam/2))
  have hrhs : (∫ z, t z*R z-lam/2*(t z*K z)-t z*C z ∂ν) =
      (∫ z, t z*R z ∂ν)-lam/2*(∫ z, t z*K z ∂ν)-
        (∫ z, t z*C z ∂ν) := by
    rw [integral_sub hRK hC,integral_sub hR (hK.const_mul (lam/2)),integral_const_mul]
  rw [hrhs] at hm
  exact hm

theorem signed_fibre_energy_integral_abs
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (t B A R K C : E → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (ht : ∀ᵐ z ∂ν, 0 ≤ t z)
    (hB : Integrable (fun z => t z*B z) ν)
    (hA : Integrable (fun z => t z*A z) ν)
    (hR : Integrable (fun z => t z*R z) ν)
    (hK : Integrable (fun z => t z*K z) ν)
    (hC : Integrable (fun z => t z*C z) ν)
    (hpoint : ∀ᵐ z ∂ν, B z+lam/2*A z ≤
      R z-lam/2*K z-C z) :
    (∫ z, t z*B z ∂ν)+lam/2*(∫ z, t z*A z ∂ν) ≤
      (∫ z, t z*R z ∂ν)+lam/2*|∫ z, t z*K z ∂ν|+
        |∫ z, t z*C z ∂ν| := by
  have h := signed_fibre_energy_integral ν t B A R K C lam ht hB hA hR hK hC hpoint
  have hk := neg_le_abs (∫ z, t z*K z ∂ν)
  have hc := neg_le_abs (∫ z, t z*C z ∂ν)
  have hkm := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ lam/2)
  linarith

end SlowEquilibration.ConditionedEntrance
