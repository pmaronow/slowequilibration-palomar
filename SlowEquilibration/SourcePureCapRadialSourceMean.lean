-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelMarkedPhysical
public import SlowEquilibration.SphericalPureCapOriginalMeanDepth
public import SlowEquilibration.SphericalPureCapOriginalWindowMean

/-! Identify the original-field radial Borel means from marked Kac--Rice
with the source's exact raw cap and microscopic-window means. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapRadialSourceMean
noncomputable section
open Set MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalPureCapOriginalMeanDepth
open SphericalPureCapOriginalWindowMean SphericalPureCapSourceRatios
open SourcePureCapBorelRadialFirst SourcePureCapBorelPosteriorMeanRadial
open SourcePureLatitudeRadialDisintegration
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_radial_cap_mean_eq_source
    (n p : ℕ) (hn : 2 ≤ n) (hp : 4 ≤ p)
    (β ep cp a t : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    ∫⁻ s : Ioi (0:ℝ), radialMeanWeight (n+1) p β
      ((n+2:ℕ)*ep+t-Real.log (n+2:ℕ)/(2*cp)) (Ico a 1) s
      ∂radialLaw (n+1) =
    ENNReal.ofReal (sourceCapMean p β ep cp a n t) := by
  let H : ℝ := (n+2:ℕ)*ep+t-Real.log (n+2:ℕ)/(2*cp)
  have hrad := pure_original_posterior_borel_mean_radial
    (n+1) p (by omega) (by omega) β H u
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hu)
    (I := Ico a 1) measurableSet_Ico
  have hraw := pure_original_conditioned_cap_mean_raw
    (n+1) p (by omega) hp (Q:=1) (by norm_num) u
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hu)
    β H a ha ha1
  dsimp only at hrad hraw
  simp only [Real.sqrt_one, one_pow, one_mul] at hraw
  rw [hraw] at hrad
  simpa only [sourceCapMean,H,Nat.add_assoc,Nat.reduceAdd] using hrad.symm

theorem pure_original_radial_window_mean_eq_source
    (n p : ℕ) (hn : 2 ≤ n) (hp : 4 ≤ p)
    (β ep cp q w t : ℝ)
    (hl : 0 < q-w/Real.sqrt (n+2:ℕ))
    (hr : q+w/Real.sqrt (n+2:ℕ) < 1)
    (hw : 0 ≤ w)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    ∫⁻ s : Ioi (0:ℝ), radialMeanWeight (n+1) p β
      ((n+2:ℕ)*ep+t-Real.log (n+2:ℕ)/(2*cp))
      (Icc (q-w/Real.sqrt (n+2:ℕ)) (q+w/Real.sqrt (n+2:ℕ))) s
      ∂radialLaw (n+1) =
    ENNReal.ofReal (sourceWindowMean p β ep cp q w n t) := by
  let H : ℝ := (n+2:ℕ)*ep+t-Real.log (n+2:ℕ)/(2*cp)
  have hrad := pure_original_posterior_borel_mean_radial
    (n+1) p (by omega) (by omega) β H u
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hu)
    (I := Icc (q-w/Real.sqrt (n+2:ℕ)) (q+w/Real.sqrt (n+2:ℕ)))
    measurableSet_Icc
  have hle : q-w/Real.sqrt (n+2:ℕ) ≤ q+w/Real.sqrt (n+2:ℕ) := by
    have hs : 0 < Real.sqrt (n+2:ℕ) := by positivity
    have hh : 0 ≤ w/Real.sqrt (n+2:ℕ) := div_nonneg hw hs.le
    linarith
  have hraw := pure_original_conditioned_window_mean_raw
    (n+1) p (by omega) hp (Q:=1) (by norm_num) u
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hu)
    β H (q-w/Real.sqrt (n+2:ℕ))
      (q+w/Real.sqrt (n+2:ℕ)) hl hr hle
  dsimp only at hrad hraw
  simp only [Real.sqrt_one, one_pow, one_mul] at hraw
  rw [hraw] at hrad
  simpa only [sourceWindowMean,H,Nat.add_assoc,Nat.reduceAdd] using hrad.symm

end
end SlowEquilibration.SourcePureCapRadialSourceMean
