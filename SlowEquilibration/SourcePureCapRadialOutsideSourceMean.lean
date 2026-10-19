-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapRadialSourceMean
public import SlowEquilibration.SphericalPureCapOriginalOutside

/-! The physical original-field radial mean on the disconnected cap outside
a microscopic window is exactly the source cap mean minus window mean. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapRadialOutsideSourceMean
noncomputable section
open Set MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalPureCapOriginalMeanDepth
open SphericalPureCapOriginalWindowMean SphericalPureCapOriginalOutside
open SphericalPureCapSourceRatios
open SourcePureCapBorelRadialFirst SourcePureCapBorelPosteriorMeanRadial
open SourcePureLatitudeRadialDisintegration
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_radial_outside_mean_eq_source
    (n p : ℕ) (hn : 2 ≤ n) (hp : 4 ≤ p)
    (β ep cp a q w t : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hl : 0 < q-w/Real.sqrt (n+2:ℕ))
    (hr : q+w/Real.sqrt (n+2:ℕ) < 1)
    (hw : 0 ≤ w)
    (hWI : Icc (q-w/Real.sqrt (n+2:ℕ))
      (q+w/Real.sqrt (n+2:ℕ)) ⊆ Ico a 1)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) :
    ∫⁻ s : Ioi (0:ℝ), radialMeanWeight (n+1) p β
      ((n+2:ℕ)*ep+t-Real.log (n+2:ℕ)/(2*cp))
      (Ico a 1 \ Icc (q-w/Real.sqrt (n+2:ℕ))
        (q+w/Real.sqrt (n+2:ℕ))) s
      ∂radialLaw (n+1) =
    ENNReal.ofReal
      (sourceCapMean p β ep cp a n t-sourceWindowMean p β ep cp q w n t) := by
  let H : ℝ := (n+2:ℕ)*ep+t-Real.log (n+2:ℕ)/(2*cp)
  let W : Set ℝ := Icc (q-w/Real.sqrt (n+2:ℕ))
    (q+w/Real.sqrt (n+2:ℕ))
  have hrad := pure_original_posterior_borel_mean_radial
    (n+1) p (by omega) (by omega) β H u
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hu)
    (I := Ico a 1 \ W) (measurableSet_Ico.diff measurableSet_Icc)
  have hsdiff := pure_original_conditioned_band_mean_sdiff
    (n+1) p (by omega) hp (Q:=1) (by norm_num) u
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hu)
    β H (Ico a 1) W measurableSet_Ico measurableSet_Icc hWI
  have hcap := pure_original_conditioned_cap_mean_raw
    (n+1) p (by omega) hp (Q:=1) (by norm_num) u
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hu)
    β H a ha ha1
  have hle : q-w/Real.sqrt (n+2:ℕ) ≤ q+w/Real.sqrt (n+2:ℕ) := by
    have hs : 0 < Real.sqrt (n+2:ℕ) := by positivity
    have hh : 0 ≤ w/Real.sqrt (n+2:ℕ) := div_nonneg hw hs.le
    linarith
  have hwindow := pure_original_conditioned_window_mean_raw
    (n+1) p (by omega) hp (Q:=1) (by norm_num) u
    (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hu)
    β H (q-w/Real.sqrt (n+2:ℕ))
      (q+w/Real.sqrt (n+2:ℕ)) hl hr hle
  dsimp only at hrad hsdiff hcap hwindow
  simp only [Real.sqrt_one, one_pow, one_mul] at hsdiff hcap hwindow
  rw [hsdiff,hcap,hwindow] at hrad
  simpa only [sourceCapMean,sourceWindowMean,H,W,Nat.add_assoc,Nat.reduceAdd]
    using hrad.symm

end
end SlowEquilibration.SourcePureCapRadialOutsideSourceMean
