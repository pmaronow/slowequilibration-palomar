-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledStrongContinuity
public import SlowEquilibration.ConditionedEntranceKilledCoreBounds

/-! Physical C² killing derivative and actual difference quotient bounds
for the original smooth cutoff diffusion. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalReversibility SphericalReversibility.Ito
open SphericalSmoothTensorStationarity FeynmanKac
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem expectation_generator_zero (D : SourceData N) (β : ℝ) (x : Vector N) (hx : OnSphere x)
    (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ y, 0 ≤ κ y)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ y, ‖κ y‖ ≤ K)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt (fun r : ℝ => expectation D β κ r.toNNReal f x)
      (coefficientGenerator β (smoothGradient D.hamiltonian D.hamiltonian_contDiff) f x - κ x * f x) (Ici 0) 0 := by
  obtain ⟨C0,hC0⟩ := (physicalSphere_compact N).exists_bound_of_continuousOn hf.continuous.continuousOn
  let C : ℝ := max C0 0
  have hC : ∀ᵐ ω ∂VectorBrownian.law N, ∀ t, ‖f (process D β x t ω)‖ ≤ C := by
    filter_upwards [process_onSphere D β x hx] with ω hs
    intro t
    exact (hC0 _ (hs t)).trans (le_max_left _ _)
  have he (t : ℝ≥0) : (∫ ω, f (process D β x t ω) ∂VectorBrownian.law N) =
      SphericalC1Dynamics.expectation β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
        (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) t f x := by
    unfold SphericalC1Dynamics.expectation
    apply integral_congr_ae
    exact (process_ae_actual D β x).mono (fun _ h => congrArg f (h t))
  have hd := SphericalC1Dynamics.expectation_hasDerivWithinAt_zero (by have := D.dimension_ge_one; omega) β
    (smoothGradient D.hamiltonian D.hamiltonian_contDiff) (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) x hx hf
  have hd' : HasDerivWithinAt
      (fun r : ℝ => ∫ ω, f (process D β x r.toNNReal ω) ∂VectorBrownian.law N)
      (coefficientGenerator β (smoothGradient D.hamiltonian D.hamiltonian_contDiff) f x) (Ici 0) 0 :=
    hd.congr_of_eventuallyEq (.of_forall (fun r => he r.toNNReal))
      (by simpa only [Real.toNNReal_zero] using he 0)
  exact killedExpectation_hasDerivWithinAt_zero (VectorBrownian.law N) κ hκ hκ0 K hK0 hK
    (process D β x) (process_measurable D β x)
    (process_ae_continuous D β x) x (process_zero D β x)
    f hf.continuous C (le_max_right _ _) hC _ hd'

theorem ordinary_expectation (D : SourceData N) (β : ℝ) (f : Vector N → ℝ) (x : Vector N) (t : ℝ≥0) :
    (∫ ω, f (process D β x t ω) ∂VectorBrownian.law N) =
      SphericalC1Dynamics.expectation β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
        (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) t f x := by
  unfold SphericalC1Dynamics.expectation
  apply integral_congr_ae
  exact (process_ae_actual D β x).mono (fun _ h => congrArg f (h t))

theorem expectation_slope_norm_le (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x, ‖κ x‖ ≤ K)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) (C M : ℝ)
    (hC : ∀ y, OnSphere y → ‖f y‖ ≤ C)
    (hM : ∀ y, OnSphere y → ‖coefficientGenerator β (smoothGradient D.hamiltonian D.hamiltonian_contDiff) f y‖ ≤ M)
    (x : Vector N) (hx : OnSphere x) (r : ℝ) (hr : 0 < r) :
    ‖slope (fun s : ℝ => expectation D β κ s.toNNReal f x) 0 r‖ ≤ M+K*C := by
  let Q : ℝ → ℝ := fun s => expectation D β κ s.toNNReal f x
  let E : ℝ → ℝ := fun s => SphericalC1Dynamics.expectation β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
    (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) s.toNNReal f x
  have hdef : ‖Q r-E r‖ ≤ K*r*C := by
    have hb : ∀ᵐ ω ∂VectorBrownian.law N, ‖f (process D β x r.toNNReal ω)‖ ≤ C :=
      (process_onSphere D β x hx).mono (fun _ h => hC _ (h _))
    have hd := killedExpectation_defect_norm_le (VectorBrownian.law N) κ hκ hκ0 K hK0 hK
      (process D β x) (process_measurable D β x) r.toNNReal f hf.continuous C hb
    rw [Real.coe_toNNReal r hr.le,ordinary_expectation D β f x r.toNNReal] at hd
    exact hd
  have hzero : Q 0 = E 0 := by
    rw [show Q 0 = ∫ ω, f (process D β x 0 ω) ∂VectorBrownian.law N by
      simp only [Q,expectation,Real.toNNReal_zero,killedExpectation_zero]]
    dsimp only [E]
    rw [Real.toNNReal_zero]
    exact ordinary_expectation D β f x 0
  have hEq : slope Q 0 r = slope E 0 r+r⁻¹*(Q r-E r) := by
    simp only [slope_def_module,sub_zero,smul_eq_mul,hzero]
    ring
  have hs := SphericalC1Dynamics.expectation_slope_norm_le (by have := D.dimension_ge_one; omega) β (smoothGradient D.hamiltonian D.hamiltonian_contDiff)
    (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) f hf M hM x hx r hr
  rw [hEq]
  calc
    _ ≤ ‖slope E 0 r‖+‖r⁻¹*(Q r-E r)‖ := norm_add_le _ _
    _ ≤ M+K*C := by
      apply add_le_add hs
      rw [norm_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_left hdef (inv_nonneg.mpr hr.le)).trans_eq (by field_simp)

end SlowEquilibration.ConditionedEntrance.SmoothKilled
