-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEMaximumDeterminant
public import SlowEquilibration.GOEClippedInverseOnGap

/-! Actual physical GOE shifted inverse gap events, with a genuine
exponentially small failure probability uniform in the exterior shift.
-/
@[expose] public section
namespace SlowEquilibration.GOEPhysicalGapEvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics GOEScaling GOEEdgeConcentration GOEMaximumDeterminant GOEClippedDeterminants
open OAI.CriticalSK
open scoped Topology Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

lemma euclideanCLM_gaussianToMatrix {m : ℕ} (A : GOEAsymptotics.GaussianMatrix m) :
    (Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ)) (gaussianToMatrix A) = gaussianMatrixCLM A := by
  apply ContinuousLinearMap.ext
  intro u
  apply PiLp.ext
  intro i
  rfl

def gapEvent (n : ℕ) (k κ : ℝ) : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  {W | ‖(Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ)) W‖ ≤ k - κ}

lemma gapEvent_measurable (n : ℕ) (k κ : ℝ) : MeasurableSet (gapEvent n k κ) := by
  apply measurableSet_le _ measurable_const
  exact ((Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.measurable).norm

/-- The actual physical GOE inverse gap failure is exponentially small.
The cutoff is the literal a_Nρ and every ambient dimension is retained. -/
theorem physical_gap_failure_eventually {b g ρ : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g / (2 * Real.sqrt b)) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n + 1 ≤ N → ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k →
      (SphericalGaussianJet.goeLaw (n + 1) N b).real
        (gapEvent n k (scaleFactor n N b * ρ))ᶜ ≤
          Real.exp (-(n + 1 : ℝ) * (g / Real.sqrt b) ^ 2 / (16 * Real.pi ^ 2)) := by
  have hsb := Real.sqrt_pos.mpr hb
  filter_upwards [gapBad_exponential_eventually (div_pos hg hsb)] with n hn
  intro N hmN k hk
  have hN : 0 < N := by omega
  let a := scaleFactor n N b
  have ha : 0 < a := scaleFactor_pos n hN hb
  have haB : a ≤ Real.sqrt b := scaleFactor_le_sqrt hN hmN hb.le
  have hκ : a * ρ ≤ g / 2 := by
    have hp := mul_le_mul_of_nonneg_left hρg hsb.le
    have hEq : Real.sqrt b * (g / (2 * Real.sqrt b)) = g / 2 := by field_simp
    exact (mul_le_mul_of_nonneg_right haB hρ.le).trans (hp.trans_eq hEq)
  have hmap : Measurable (fun A : GOEAsymptotics.GaussianMatrix (n + 1) => a • GOEDeterminantMoments.realization n A) := by
    exact (show Measurable (fun _ : GOEAsymptotics.GaussianMatrix (n + 1) => a) from measurable_const).smul
      (GOEDeterminantMoments.realization_measurable n)
  rw [← scaled_realization_law n hN hb.le, Measure.real,
    Measure.map_apply hmap (gapEvent_measurable n k (a * ρ)).compl]
  have hsub : (fun A : GOEAsymptotics.GaussianMatrix (n + 1) => a • GOEDeterminantMoments.realization n A) ⁻¹'
      (gapEvent n k (a * ρ))ᶜ ⊆ gapBad n (g / Real.sqrt b) := by
    intro A hA
    by_contra hbad
    have hrad : realizedRadius n A ≤ 2 + (g / Real.sqrt b) / 2 := le_of_not_gt hbad
    have hnorm : ‖(Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ))
        (a • GOEDeterminantMoments.realization n A)‖ ≤ a * realizedRadius n A := by
      rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ha,
        GOEDeterminantMoments.realization, euclideanCLM_gaussianToMatrix]
      exact mul_le_mul_of_nonneg_left (realized_operator_norm_le_radius n A) ha.le
    have hupper : a * realizedRadius n A ≤ 2 * Real.sqrt b + g / 2 := by
      calc
        _ ≤ a * (2 + (g / Real.sqrt b) / 2) := mul_le_mul_of_nonneg_left hrad ha.le
        _ ≤ Real.sqrt b * (2 + (g / Real.sqrt b) / 2) :=
          mul_le_mul_of_nonneg_right haB (by positivity)
        _ = _ := by field_simp
    apply hA
    change ‖(Matrix.toEuclideanCLM (n := Fin (n + 1)) (𝕜 := ℝ))
      (a • GOEDeterminantMoments.realization n A)‖ ≤ k - a * ρ
    linarith
  exact (measureReal_mono hsub).trans hn

end
end SlowEquilibration.GOEPhysicalGapEvent
