-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalCenterCountLimits

/-! The physical centered pure window, expressed as the scalar-value
window of the selected original-field count. Its exterior mark clipping
keeps it inside the fixed source value box in every dimension. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory
open SlowEquilibration.PairConditionalDeterminantMoments

def sourcePureCenteredNormalizedWindow
    (n : ℕ) (m : ℕ → ℝ) (E δ L R : ℝ) : Set ℝ :=
  (fun b : ℝ => ((n+3 : ℕ) : ℝ)*b) ⁻¹'
    (Icc (m (n+1)+L) (m (n+1)+R) ∩
      Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ)))

theorem sourcePureCenteredNormalizedWindow_measurable
    (n : ℕ) (m : ℕ → ℝ) (E δ L R : ℝ) :
    MeasurableSet (sourcePureCenteredNormalizedWindow n m E δ L R) := by
  exact (measurableSet_Icc.inter measurableSet_Ioo).preimage
    (measurable_const_mul ((n+3 : ℕ) : ℝ))

theorem sourcePureCenteredNormalizedWindow_subset_value_box
    (n : ℕ) (m : ℕ → ℝ) (E δ L R : ℝ) :
    sourcePureCenteredNormalizedWindow n m E δ L R ⊆ Icc (E-δ) (E+δ) := by
  intro b hb
  have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
  have hband := hb.2
  constructor
  · exact (lt_of_mul_lt_mul_left hband.1 hN.le).le
  · exact (lt_of_mul_lt_mul_left hband.2 hN.le).le

theorem sourcePureCenteredNormalizedWindow_critical_mean
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ L R : ℝ) (m : ℕ → ℝ) :
    sourceUnfilteredValueWindowMean (n+2) (FiniteMixture.pure p hp a ha) Q
      (sourcePureCenteredNormalizedWindow n m E δ L R) =
    sourcePureTruncatedCriticalWindowMean (n+1) p hp a ha Q
      (E-δ) (E+δ) (m (n+1)+L) (m (n+1)+R) := by
  rfl

end SlowEquilibration.SphericalMarkedWindows
