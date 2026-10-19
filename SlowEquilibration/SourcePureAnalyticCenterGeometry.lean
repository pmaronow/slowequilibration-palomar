-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureBadHessianRawWindow

/-! Source §9's deterministic log center lies within bounded distance of
the exact local-maximum center; every fixed physical window also lies in any
positive contact-value box in large dimensions. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory ExpectedTailCentering
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped Topology
set_option autoImplicit false

def sourcePureAnalyticCenter (N : ℕ) (E c : ℝ) : ℝ :=
  (N : ℝ)*E-Real.log (N : ℕ)/(2*c)

theorem sourcePure_analytic_window_eventually_in_selected_box
    {E c M δ L : ℝ} (hc : 0 < c) (_hM : 0 ≤ M) (hδ : 0 < δ)
    (m : ℕ → ℝ)
    (hcenter : ∀ᶠ j : ℕ in atTop,
      |m j-sourcePureAnalyticCenter (j+2) E c| ≤ M) :
    ∀ᶠ n : ℕ in atTop,
      Icc (sourcePureAnalyticCenter (n+3) E c-L)
        (sourcePureAnalyticCenter (n+3) E c+L) ⊆
      Icc (m (n+1)-(L+M)) (m (n+1)+(L+M)) ∩
        Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ)) := by
  have hzero : ∀ᶠ j : ℕ in atTop,
      |sourcePureAnalyticCenter (j+2) E c-
        ((j+2 : ℕ)*E-Real.log (j+2 : ℕ)/(2*c))| ≤ (0 : ℝ) := by
    filter_upwards [] with j
    simp [sourcePureAnalyticCenter]
  have hOff := (tendsto_add_atTop_nat 1).eventually
    (source_logarithmic_center_offset_bounds hc (le_refl (0 : ℝ))
      (half_pos hδ) (fun j => sourcePureAnalyticCenter (j+2) E c)
      hzero (-L) L)
  have hcenter' := (tendsto_add_atTop_nat 1).eventually hcenter
  filter_upwards [hOff,hcenter'] with n hn hcN
  intro z hz
  simp only [show n+1+2=n+3 by omega] at hn hcN
  rcases hz with ⟨hzLo,hzHi⟩
  have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
  have hhalf : 0 < δ/2 := half_pos hδ
  refine ⟨?_,?_⟩
  · have hcM := abs_le.mp hcN
    constructor <;> dsimp [sourcePureAnalyticCenter] at * <;> linarith
  · constructor
    · have hlo : ((n+3 : ℕ) : ℝ)*(E-δ) < ((n+3 : ℕ) : ℝ)*(E-δ/2) := by
        nlinarith
      exact hlo.trans_le (hn.1.trans hzLo)
    · have hhi : ((n+3 : ℕ) : ℝ)*(E+δ/2) < ((n+3 : ℕ) : ℝ)*(E+δ) := by
        nlinarith
      exact (hzHi.trans hn.2).trans_lt hhi

end SlowEquilibration.SphericalMarkedWindows
