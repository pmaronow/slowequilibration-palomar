-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMaximumRelativeError

/-! Uniform asymptotic equality of the actual mixed physical critical-point
and maximum intensities. This supplies the error needed for fixed-window
first-moment limits, rather than only a constant-factor comparison. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory SphericalModel SphericalSequentialRegression
open GOEMaximumDeterminant GOEPhysicalPotential
open scoped Topology ENNReal
set_option maxHeartbeats 300000

theorem mixed_physical_maximum_relative_comparison (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0<Q) {g Z : ℝ} (hg : 0<g) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,0 ≤ maximumRelativeError C (Q^2*μ.xi2 Q) g n ∧
      maximumRelativeError C (Q^2*μ.xi2 Q) g n<1 ∧
      ∀ H k : ℝ,k∈Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+g) Z →
        ENNReal.ofReal (1-maximumRelativeError C (Q^2*μ.xi2 Q) g n)*
          mixedCriticalPhysicalIntensity n μ Q H k  ≤  mixedLocalMaxPhysicalIntensity n μ Q H k ∧
        mixedLocalMaxPhysicalIntensity n μ Q H k  ≤  mixedCriticalPhysicalIntensity n μ Q H k := by
  have hb : 0<Q^2*μ.xi2 Q := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  obtain ⟨C,hC,hbound⟩ := maximumMean_relative_error_bounds (Z := Z) hb hg
  have ht := maximumRelativeError_tendsto_zero hb hg C
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,ht.eventually (gt_mem_nhds (show (0 : ℝ)<1 by norm_num))]
    with n hn hsmall
  have hNonneg : 0 ≤ maximumRelativeError C (Q^2*μ.xi2 Q) g n := by
    unfold maximumRelativeError
    positivity
  refine ⟨hNonneg,hsmall,?_⟩
  intro H k hk
  obtain ⟨hl,hu⟩ := hn k hk
  have he := ENNReal.ofReal_le_ofReal hl
  rw [ENNReal.ofReal_mul (sub_nonneg.mpr hsmall.le)] at he
  have he' := ENNReal.ofReal_le_ofReal hu
  unfold mixedCriticalPhysicalIntensity mixedLocalMaxPhysicalIntensity
    mixedCriticalIntensity mixedNegativeIntensity
  let p := ENNReal.ofReal ((n+2 : ℕ) : ℝ)⁻¹
  let q := sphereKRPrefactor (n+1) μ Q*physicalScorePdf (n+2) μ Q
    (WithLp.toLp 2 ![H/(n+2 : ℕ),k])
  change ENNReal.ofReal (1-maximumRelativeError C (Q^2*μ.xi2 Q) g n)*
      (p*(q*ENNReal.ofReal (physicalMean n (n+2) (Q^2*μ.xi2 Q) k))) ≤
      p*(q*ENNReal.ofReal (maximumMean n (n+2) (Q^2*μ.xi2 Q) k)) ∧
    p*(q*ENNReal.ofReal (maximumMean n (n+2) (Q^2*μ.xi2 Q) k)) ≤
      p*(q*ENNReal.ofReal (physicalMean n (n+2) (Q^2*μ.xi2 Q) k))
  constructor
  · calc
      _=p*(q*(ENNReal.ofReal (1-maximumRelativeError C (Q^2*μ.xi2 Q) g n)*
        ENNReal.ofReal (physicalMean n (n+2) (Q^2*μ.xi2 Q) k))) := by ac_rfl
      _≤_ := mul_le_mul_right (mul_le_mul_right he q) p
  · exact mul_le_mul_right (mul_le_mul_right he' q) p

end SlowEquilibration.SphericalMarkedWindows
