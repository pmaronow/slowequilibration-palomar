-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPhysicalWindowCountBridge

/-! Actual fixed-window critical and maximum means have asymptotically
identical normalization, by the actual Hessian relative-error estimate. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory Filter SphericalModel SphericalSequentialRegression
open GOEMaximumDeterminant
open scoped Topology ENNReal
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem sourceWindowMean_relative_comparison (μ : FiniteMixture) {Q L R : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hL : sourceRadialEdge μ Q < L) :
    ∃ C : ℝ,0 < C ∧
      Tendsto (fun n : ℕ => maximumRelativeError C (Q^2*μ.xi2 Q) ((L-sourceRadialEdge μ Q)/2) n)
        atTop (𝓝 (0 : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop,
        0 ≤ maximumRelativeError C (Q^2*μ.xi2 Q) ((L-sourceRadialEdge μ Q)/2) n ∧
        maximumRelativeError C (Q^2*μ.xi2 Q) ((L-sourceRadialEdge μ Q)/2) n < 1 ∧
        ∀ l r : ℝ,
          (1-maximumRelativeError C (Q^2*μ.xi2 Q) ((L-sourceRadialEdge μ Q)/2) n)*
              sourceCriticalWindowMean n μ Q (Ioo L R) l r ≤ sourceMaximumWindowMean n μ Q (Ioo L R) l r ∧
          sourceMaximumWindowMean n μ Q (Ioo L R) l r ≤ sourceCriticalWindowMean n μ Q (Ioo L R) l r := by
  let g := (L-sourceRadialEdge μ Q)/2
  have hg : 0 < g := half_pos (sub_pos.mpr hL)
  have hb : 0 < Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨C,hC,hbound⟩ := mixed_physical_maximum_relative_comparison μ hQ (Z := R) hg
  refine ⟨C,hC,maximumRelativeError_tendsto_zero hb hg C,?_⟩
  filter_upwards [hbound] with n hn
  refine ⟨hn.1,hn.2.1,?_⟩
  intro l r
  have hMax : sourceMaximumWindowMass n μ Q (Ioo L R) l r=
      ∫⁻ H in Icc l r,∫⁻ k in Ioo L R,mixedLocalMaxPhysicalIntensity n μ Q H k :=
    by rw [sourceMaximumWindowMass_def];exact actual_mixed_localMax_physical_intensity n μ hQ hnp _ _ measurableSet_Icc measurableSet_Ioo
  have hAll : sourceCriticalWindowMass n μ Q (Ioo L R) l r=
      ∫⁻ H in Icc l r,∫⁻ k in Ioo L R,mixedCriticalPhysicalIntensity n μ Q H k :=
    by rw [sourceCriticalWindowMass_def];exact actual_mixed_critical_physical_intensity n μ hQ hnp _ _ measurableSet_Icc measurableSet_Ioo
  have hMarks : ∀ k∈Ioo L R,k∈Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) R := by
    intro k hk
    dsimp [g,sourceRadialEdge] at *
    constructor <;> linarith [hk.1,hk.2]
  have hlo : ENNReal.ofReal (1-maximumRelativeError C (Q^2*μ.xi2 Q) g n)*
      sourceCriticalWindowMass n μ Q (Ioo L R) l r ≤ sourceMaximumWindowMass n μ Q (Ioo L R) l r := by
    rw [hMax,hAll]
    calc
      _=(∫⁻ H in Icc l r,ENNReal.ofReal (1-maximumRelativeError C (Q^2*μ.xi2 Q) g n)*
          (∫⁻ k in Ioo L R,mixedCriticalPhysicalIntensity n μ Q H k)) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _=(∫⁻ H in Icc l r,∫⁻ k in Ioo L R,
          ENNReal.ofReal (1-maximumRelativeError C (Q^2*μ.xi2 Q) g n)*mixedCriticalPhysicalIntensity n μ Q H k) := by
        apply lintegral_congr
        intro H
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ _ := by
        apply lintegral_mono
        intro H
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
        exact (hn.2.2 H k (hMarks k hk)).1
  have hup : sourceMaximumWindowMass n μ Q (Ioo L R) l r ≤ sourceCriticalWindowMass n μ Q (Ioo L R) l r := by
    rw [hMax,hAll]
    apply lintegral_mono
    intro H
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
    exact (hn.2.2 H k (hMarks k hk)).2
  have hloReal := ENNReal.toReal_mono (sourceMaximumWindowMass_finite n μ hQ (Ioo L R) l r).ne hlo
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (sub_nonneg.mpr hn.2.1.le)] at hloReal
  have hupReal := ENNReal.toReal_mono (sourceCriticalWindowMass_finite n μ hQ (Ioo L R) l r).ne hup
  exact ⟨hloReal,hupReal⟩

end SlowEquilibration.SphericalMarkedWindows
