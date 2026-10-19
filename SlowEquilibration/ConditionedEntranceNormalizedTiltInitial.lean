-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceTiltCommutator
public import SlowEquilibration.ConditionedEntranceSmoothKilledGeneralUniformStart

/-! The actual initial law under a globally normalized exponential tilt.
The factor `M exp(-w)` cancels the tilt exactly, including its global
normalization. This is the initial-law step of the entrance comparison. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SmoothKilledGeneral
set_option autoImplicit false
set_option maxHeartbeats 300000

/-- Exact global change of initial density. Neither the initial density nor
the test function is required to be frozen in the tilt label. -/
theorem normalizedTilt_initial_pairing {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (w : E → ℝ) (hw : Measurable w) {M : ℝ} (hM : 0 < M)
    (f₀ h : E → ℝ) :
    (∫ z, (M * Real.exp (-w z) * f₀ z) * h z ∂normalizedTilt μ w M) =
      ∫ z, f₀ z * h z ∂μ := by
  rw [integral_normalizedTilt μ w hw hM]
  have he : (fun z => Real.exp (w z) * ((M * Real.exp (-w z) * f₀ z) * h z)) =
      fun z => M * (f₀ z * h z) := by
    funext z
    have hexp : Real.exp (w z) * Real.exp (-w z) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      Real.exp (w z) * ((M * Real.exp (-w z) * f₀ z) * h z) =
          M * (Real.exp (w z) * Real.exp (-w z)) * (f₀ z * h z) := by ring
      _ = M * (f₀ z * h z) := by rw [hexp, mul_one]
  rw [he, integral_const_mul]
  exact (mul_div_cancel_left₀ _ hM.ne')

/-- At a fixed field and axis, the transported physical initial pairing is
literally the original uniform sphere integral. The density is constructed
from the actual Gibbs Hamiltonian, not introduced as an abstract measure. -/
theorem normalizedTilt_uniformSphere_pairing {N : ℕ} (D : FieldData N) (β : ℝ)
    (w : Vector N → ℝ) (hw : Measurable w) {M : ℝ} (hM : 0 < M)
    (h : Vector N → ℝ) :
    (∫ x, (M * Real.exp (-w x) * uniformDensity D β x) * h x
      ∂normalizedTilt (gibbsLaw N β D.hamiltonian) w M) =
      ∫ x, h x ∂sphereLaw N := by
  rw [normalizedTilt_initial_pairing _ w hw hM (uniformDensity D β) h]
  exact uniformDensity_integral_change D β h

/-- With the axis frozen, the globally tilted initial law still has the
original independent uniform axis and uniform spin marginals. Fubini is
justified by the stated product integrability of the physical test. -/
theorem normalizedTilt_uniformSphere_product_pairing {N : ℕ} (D : FieldData N) (β : ℝ)
    (w : Vector N × Vector N → ℝ) (hw : Measurable w) {M : ℝ} (hM : 0 < M)
    (h : Vector N × Vector N → ℝ)
    (hi : Integrable (fun z => uniformDensity D β z.2 * h z)
      ((sphereLaw N).prod (gibbsLaw N β D.hamiltonian))) :
    (∫ z, (M * Real.exp (-w z) * uniformDensity D β z.2) * h z
      ∂normalizedTilt ((sphereLaw N).prod (gibbsLaw N β D.hamiltonian)) w M) =
      ∫ u,∫ x, h (u,x) ∂sphereLaw N ∂sphereLaw N := by
  let : IsProbabilityMeasure (gibbsLaw N β D.hamiltonian) :=
    gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  rw [normalizedTilt_initial_pairing _ w hw hM (fun z => uniformDensity D β z.2) h]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact .of_forall (fun u => uniformDensity_integral_change D β (fun x => h (u,x)))

/-- The global source first moment supplies an actual probability measure.
In particular, positivity of `M` is a conclusion once the moment has
fallen below one half. -/
theorem normalizedTilt_probability_of_axis_moment
    {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    (θ : Measure U) (μ : Measure E)
    [IsProbabilityMeasure θ] [IsProbabilityMeasure μ]
    (w : U × E → ℝ)
    (he : Integrable (fun z => Real.exp (w z)) (θ.prod μ))
    {η : ℝ} (hη : η ≤ 1/2)
    (haxis : ∀ᵐ x ∂μ,
      (∫ u, |Real.exp (w (u,x))-1| ∂θ) ≤ η) :
    let M := ∫ z, Real.exp (w z) ∂θ.prod μ
    0 < M ∧ IsProbabilityMeasure (normalizedTilt (θ.prod μ) w M) ∧
      |M-1| ≤ η := by
  dsimp only
  let M := ∫ z, Real.exp (w z) ∂θ.prod μ
  have hc : |M-1| ≤ η := exponential_mass_close_one θ μ w he rfl haxis
  have hM : 0 < M := by
    have hl := (abs_le.mp hc).1
    linarith
  exact ⟨hM,normalizedTilt_probability _ w hM he rfl,hc⟩

end SlowEquilibration.ConditionedEntrance
