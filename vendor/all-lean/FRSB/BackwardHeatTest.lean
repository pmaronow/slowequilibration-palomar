module
public import FRSB.BackwardHeatBounds

@[expose] public section

/-! Globally regular capped backward tests. The upper-time cap remains
strictly below the terminal time, so every time derivative uses positive
Gaussian variance. On the stochastic interval the cap is the identity. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Paper StochasticCalculus
open scoped Topology ContDiff
namespace FRSB

theorem continuous_backwardHeatQuotient_jets {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D)
    (hp : ∀ v x, gaussianHeatFlow D v x ≠ 0) :
    Continuous (fun p : ℝ × ℝ => backwardHeatQuotient N D p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => backwardHeatQuotientDx N D p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => backwardHeatQuotientDxx N D p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => backwardHeatQuotientDv N D p.1 p.2) := by
  have hn0 := continuous_gaussianHeatFlow hN
  have hd0 := continuous_gaussianHeatFlow hD
  have hn1 : Continuous (fun p : ℝ × ℝ => gaussianHeatFlow (deriv N) p.1 p.2) := by
    simpa only [iteratedDeriv_one] using continuous_gaussianHeatFlow_jet hN (j := 1) (by norm_num)
  have hd1 : Continuous (fun p : ℝ × ℝ => gaussianHeatFlow (deriv D) p.1 p.2) := by
    simpa only [iteratedDeriv_one] using continuous_gaussianHeatFlow_jet hD (j := 1) (by norm_num)
  have hn2 := continuous_gaussianHeatFlow_jet hN (j := 2) (by norm_num)
  have hd2 := continuous_gaussianHeatFlow_jet hD (j := 2) (by norm_num)
  have hp2 : ∀ p : ℝ × ℝ, gaussianHeatFlow D p.1 p.2 ^ 2 ≠ 0 :=
    fun p => pow_ne_zero 2 (hp p.1 p.2)
  refine ⟨hn0.div hd0 (fun p => hp p.1 p.2), ?_, ?_, ?_⟩
  · exact ((hn1.mul hd0).sub (hn0.mul hd1)).div (hd0.pow 2) hp2
  · exact (((hn2.mul hd0).sub (hn0.mul hd2)).mul (hd0.pow 2) |>.sub
      (((hn1.mul hd0).sub (hn0.mul hd1)).mul ((continuous_const.mul hd0).mul hd1))).div
        ((hd0.pow 2).pow 2) (fun p => pow_ne_zero 2 (hp2 p))
  · exact (((continuous_const.mul hn2).mul hd0).sub
      (hn0.mul (continuous_const.mul hd2))).div (hd0.pow 2) hp2

def cappedBackwardHeatQuotient (N D : ℝ → ℝ) (β b c δ t x : ℝ) : ℝ :=
  backwardHeatQuotient N D (β ^ 2 * (b - hjbTimeCap c δ t)) x

theorem cappedBackwardHeatQuotient_of_le (N D : ℝ → ℝ) (β b c δ t x : ℝ)
    (ht : t ≤ c) :
    cappedBackwardHeatQuotient N D β b c δ t x =
      backwardHeatQuotient N D (β ^ 2 * (b - t)) x := by
  simp only [cappedBackwardHeatQuotient, hjbTimeCap_of_le c δ t ht]

theorem cappedBackwardHeatQuotient_variance_pos (β b c δ t : ℝ)
    (hβ : β ≠ 0) (hδ : 0 < δ) (hcb : c + δ ≤ b) :
    0 < β ^ 2 * (b - hjbTimeCap c δ t) :=
  mul_pos (sq_pos_of_ne_zero hβ)
    (sub_pos.mpr ((hjbTimeCap_lt c hδ t).trans_le hcb))

theorem hasDerivAt_cappedBackwardHeatQuotient_time {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D)
    (hp : ∀ v x, gaussianHeatFlow D v x ≠ 0)
    (β b c δ t x : ℝ) (hβ : β ≠ 0) (hδ : 0 < δ) (hcb : c + δ ≤ b) :
    HasDerivAt (fun s => cappedBackwardHeatQuotient N D β b c δ s x)
      ((-β ^ 2 * hjbTimeCapD c δ t) *
        backwardHeatQuotientDv N D (β ^ 2 * (b - hjbTimeCap c δ t)) x) t := by
  have hd := (hasDerivAt_backwardHeatQuotient_variance hN hD
    (cappedBackwardHeatQuotient_variance_pos β b c δ t hβ hδ hcb) x (hp _ _)).comp t
      (((hasDerivAt_const t b).sub (hasDerivAt_hjbTimeCap c hδ t)).const_mul (β ^ 2))
  convert hd using 1
  · rfl
  · ring

theorem hasDerivAt_cappedBackwardHeatQuotient_spatial {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D)
    (hp : ∀ v x, gaussianHeatFlow D v x ≠ 0) (β b c δ t x : ℝ) :
    HasDerivAt (cappedBackwardHeatQuotient N D β b c δ t)
      (backwardHeatQuotientDx N D (β ^ 2 * (b - hjbTimeCap c δ t)) x) x :=
  hasDerivAt_backwardHeatQuotient_spatial hN hD _ x (hp _ x)

theorem contDiff_cappedBackwardHeatQuotient_spatial {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D)
    (hp : ∀ v x, gaussianHeatFlow D v x ≠ 0) (β b c δ t : ℝ) :
    ContDiff ℝ 2 (cappedBackwardHeatQuotient N D β b c δ t) :=
  (contDiff_gaussianHeatFlow_spatial hN _).div
    (contDiff_gaussianHeatFlow_spatial hD _) (fun x => hp _ x)

theorem cappedBackwardHeatQuotient_ito_derivatives {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D)
    (hp : ∀ v x, gaussianHeatFlow D v x ≠ 0)
    (β b c δ t x : ℝ) (hβ : β ≠ 0) (hδ : 0 < δ) (hcb : c + δ ≤ b) :
    itoTimeDerivative (cappedBackwardHeatQuotient N D β b c δ) t x =
      (-β ^ 2 * hjbTimeCapD c δ t) *
        backwardHeatQuotientDv N D (β ^ 2 * (b - hjbTimeCap c δ t)) x ∧
    itoSpaceDerivative (cappedBackwardHeatQuotient N D β b c δ) t x =
      backwardHeatQuotientDx N D (β ^ 2 * (b - hjbTimeCap c δ t)) x ∧
    itoSpaceSecondDerivative (cappedBackwardHeatQuotient N D β b c δ) t x =
      backwardHeatQuotientDxx N D (β ^ 2 * (b - hjbTimeCap c δ t)) x := by
  refine ⟨(hasDerivAt_cappedBackwardHeatQuotient_time hN hD hp β b c δ t x hβ hδ hcb).deriv,
    (hasDerivAt_cappedBackwardHeatQuotient_spatial hN hD hp β b c δ t x).deriv, ?_⟩
  unfold itoSpaceSecondDerivative
  have he : deriv (cappedBackwardHeatQuotient N D β b c δ t) =
      backwardHeatQuotientDx N D (β ^ 2 * (b - hjbTimeCap c δ t)) := by
    funext y
    exact (hasDerivAt_cappedBackwardHeatQuotient_spatial hN hD hp β b c δ t y).deriv
  rw [he]
  exact (hasDerivAt_backwardHeatQuotientDx hN hD _ x (hp _ x)).deriv

theorem cappedBackwardHeatQuotient_ito_continuous {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D)
    (hp : ∀ v x, gaussianHeatFlow D v x ≠ 0)
    (β b c δ : ℝ) (hβ : β ≠ 0) (hδ : 0 < δ) (hcb : c + δ ≤ b) :
    Continuous (fun p : ℝ × ℝ => cappedBackwardHeatQuotient N D β b c δ p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => itoTimeDerivative (cappedBackwardHeatQuotient N D β b c δ) p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => itoSpaceDerivative (cappedBackwardHeatQuotient N D β b c δ) p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative (cappedBackwardHeatQuotient N D β b c δ) p.1 p.2) := by
  obtain ⟨hf, hfx, hfxx, hfv⟩ := continuous_backwardHeatQuotient_jets hN hD hp
  have hc : Continuous (fun p : ℝ × ℝ => (β ^ 2 * (b - hjbTimeCap c δ p.1), p.2)) := by fun_prop
  refine ⟨hf.comp hc, ?_, ?_, ?_⟩
  · have he := funext (fun p : ℝ × ℝ =>
      (cappedBackwardHeatQuotient_ito_derivatives hN hD hp β b c δ p.1 p.2 hβ hδ hcb).1)
    rw [he]
    exact (continuous_const.mul ((continuous_hjbTimeCapD c δ).comp continuous_fst)).mul (hfv.comp hc)
  · have he := funext (fun p : ℝ × ℝ =>
      (cappedBackwardHeatQuotient_ito_derivatives hN hD hp β b c δ p.1 p.2 hβ hδ hcb).2.1)
    rw [he]
    exact hfx.comp hc
  · have he := funext (fun p : ℝ × ℝ =>
      (cappedBackwardHeatQuotient_ito_derivatives hN hD hp β b c δ p.1 p.2 hβ hδ hcb).2.2)
    rw [he]
    exact hfxx.comp hc

end FRSB
