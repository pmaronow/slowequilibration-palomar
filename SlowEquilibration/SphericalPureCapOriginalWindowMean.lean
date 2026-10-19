-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapOriginalMeanDepth
public import SlowEquilibration.SphericalPureCapSourceRatios

/-! Identification of the literal raw microscopic-window means with the
original pure Hamiltonian's value-conditioned partition expectations. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapOriginalWindowMean
noncomputable section
open MeasureTheory Set SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalPureOriginalConditionalBandBorel
open SphericalPureCapIntegralDecomposition SphericalPureCapSourceRatios
open SphericalTAPCriticalPureLatitudeVariance PureStationarity
set_option autoImplicit false

/-- On any closed positive latitude interval strictly inside the sphere,
the original conditioned mean equals the raw entropy-power integral. -/
theorem pure_original_conditioned_window_mean_raw
    (n p : ℕ) (hn : 3 ≤ n) (hp : 4 ≤ p)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (β H l r : ℝ) (hl : 0 < l) (hr : r < 1) (hlr : l ≤ r) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u (Icc l r))
      ∂valueConditionedLaw c u hu (s*H/(n+1 : ℕ))) =
      (latitudeNormalization n).toReal *
        (∫ z in l..r, rawDensity p (n+1) β H z) := by
  dsimp only
  have hinside : Icc l r ⊆ Ioo (-1:ℝ) 1 := by
    intro z hz
    exact ⟨by linarith [hl,hz.1],by linarith [hr,hz.2]⟩
  rw [pure_original_conditioned_band_mean_borel n p (by omega)
    (by omega) 1 (by positivity) hQ u hu β H (Icc l r)
      measurableSet_Icc hinside]
  congr 1
  rw [intervalIntegral.integral_of_le hlr,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro z hz
  have hz0 : 0 ≤ 1-z^2 := by nlinarith [hl,hr,hz.1,hz.2]
  have hres : β^2*sourcePureLatitudeVariance p 1 z =
      pureResidualCoefficient p β z := by
    rw [pureResidualCoefficient_eq p (by omega)]
    unfold sourcePureLatitudeVariance
    ring
  have hpow : (Real.sqrt (1-z^2))^(n-2) =
      (1-z^2)^((((n+1:ℕ):ℝ)-3)/2) := by
    rw [←Real.rpow_natCast,
      ←Real.rpow_div_two_eq_sqrt ((n-2:ℕ):ℝ) hz0]
    congr 1
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    ring
  unfold rawDensity
  dsimp only
  rw [hpow,←hres]
  congr 1
  ring

/-- The exact source numerator `sourceWindowMean` is the original posterior
expected band partition on the same microscopic interval. -/
theorem sourceWindowMean_eq_original_conditioned
    (n p : ℕ) (hn : 2 ≤ n) (hp : 4 ≤ p)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2 : ℕ))
    (β ep cp q w t : ℝ)
    (hl : 0 < q-w/Real.sqrt (n+2 : ℕ))
    (hr : q+w/Real.sqrt (n+2 : ℕ) < 1)
    (hw : 0 ≤ w) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u
        (Icc (q-w/Real.sqrt (n+2 : ℕ))
          (q+w/Real.sqrt (n+2 : ℕ))))
      ∂valueConditionedLaw c u hu
        (s*((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp))/(n+2 : ℕ))) =
      sourceWindowMean p β ep cp q w n t := by
  have hle : q-w/Real.sqrt (n+2 : ℕ) ≤
      q+w/Real.sqrt (n+2 : ℕ) := by
    have hs : 0 < Real.sqrt (n+2 : ℕ) := by positivity
    have hw' : 0 ≤ w/Real.sqrt (n+2 : ℕ) := div_nonneg hw hs.le
    linarith
  simpa only [sourceWindowMean,show n+1+1=n+2 by omega] using
    pure_original_conditioned_window_mean_raw (n+1) p (by omega) hp
      hQ u hu β
      ((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp))
      (q-w/Real.sqrt (n+2 : ℕ))
      (q+w/Real.sqrt (n+2 : ℕ)) hl hr hle

/-- The exact source denominator `sourceCapMean` is the original posterior
expected partition on the manuscript's half-open cap `[a,1)`. -/
theorem sourceCapMean_eq_original_conditioned
    (n p : ℕ) (hn : 2 ≤ n) (hp : 4 ≤ p)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2 : ℕ))
    (β ep cp a t : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u (Ico a 1))
      ∂valueConditionedLaw c u hu
        (s*((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp))/(n+2 : ℕ))) =
      sourceCapMean p β ep cp a n t := by
  simpa only [sourceCapMean,show n+1+1=n+2 by omega] using
    SphericalPureCapOriginalMeanDepth.pure_original_conditioned_cap_mean_raw
      (n+1) p (by omega) hp hQ u hu β
      ((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp)) a ha ha1

end
end SlowEquilibration.SphericalPureCapOriginalWindowMean
