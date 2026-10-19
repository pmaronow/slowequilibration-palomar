-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumFirstMoments
public import SlowEquilibration.SphericalPhysicalWindowCountBridge

/-! The manuscript's centered expected-count input to critical-point
entrance transfer, for the exact original nonpure score-window count. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceMixedCriticalCenteredWindowCount
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem original_mixed_centered_critical_window_count_bounded
    (μ : FiniteMixture) {β x Q L R : ℝ} (hQ : 0 < Q)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R)
    {M : ℝ} (hM : 0 < M) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      (∫⁻ J, actualScoreWindowCount (n+1)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (n+2)
          (Icc (d.center n-M) (d.center n+M)) (Ioo L R))
        (fun _ _ => 1) J ∂disorderLaw (n+2) μ.maxDegree) ≤
          ENNReal.ofReal B := by
  obtain ⟨B,hB,hBound⟩ := d.uniform_window_bound (-M) M (by linarith)
  refine ⟨B,hB,?_⟩
  intro n
  have hFinite := sourceCriticalWindowMass_finite n μ hQ (Ioo L R)
    (d.center n-M) (d.center n+M)
  have hReal : sourceCriticalWindowMean n μ Q (Ioo L R)
      (d.center n-M) (d.center n+M) ≤ B := by
    simpa only [sub_eq_add_neg] using (hBound n).2
  rw [← sourceCriticalWindowMass_def]
  rw [← ENNReal.ofReal_toReal hFinite.ne]
  exact ENNReal.ofReal_le_ofReal hReal

end SlowEquilibration.SourceMixedCriticalCenteredWindowCount
