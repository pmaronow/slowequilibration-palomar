-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapOriginalWindowMean
public import SlowEquilibration.SphericalPureCapSourceLower
public import SlowEquilibration.NatLogWindowScales

/-! Source pure-cap Laplace ratios and microscopic lower bound for the
original value-conditioned disorder posterior. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapOriginalSourceRatios
noncomputable section
open Filter Set MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalTAPCertificate
open SphericalPureCapOriginalWindowMean SphericalPureCapSourceRatios
open SphericalPureCapSourceLower SphericalPureCapSourceScalars
open SourceGaussianWindowFraction SourceGaussianLaplaceRatio PureStationarity
open scoped Topology
set_option autoImplicit false

/-- The original posterior expected partition function in the half-open
source cap `[a,1)` at the logarithmically centered critical energy. -/
def originalSourceCapMean (p : ℕ) (hp : 2 ≤ p) (β Q ep cp a : ℝ)
    (u : ∀ n : ℕ, Vector (n+2))
    (hu : ∀ n : ℕ, ‖u n‖^2=(n+2:ℕ)) (n : ℕ) (t : ℝ) : ℝ :=
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  ∫ J, partitionOn β (field (mixtureCoefficients μ) J)
    (overlapRegion (u n) (Ico a 1))
    ∂valueConditionedLaw c (u n) (hu n)
      (s*(((n+2:ℕ):ℝ)*ep+t-Real.log (n+2:ℕ)/(2*cp))/(n+2:ℕ))

/-- The original posterior expected partition function in the closed
microscopic latitude window centered at `q`. -/
def originalSourceWindowMean (p : ℕ) (hp : 2 ≤ p) (β Q ep cp q w : ℝ)
    (u : ∀ n : ℕ, Vector (n+2))
    (hu : ∀ n : ℕ, ‖u n‖^2=(n+2:ℕ)) (n : ℕ) (t : ℝ) : ℝ :=
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  ∫ J, partitionOn β (field (mixtureCoefficients μ) J)
    (overlapRegion (u n)
      (Icc (q-w/Real.sqrt (n+2:ℕ)) (q+w/Real.sqrt (n+2:ℕ))))
    ∂valueConditionedLaw c (u n) (hu n)
      (s*(((n+2:ℕ):ℝ)*ep+t-Real.log (n+2:ℕ)/(2*cp))/(n+2:ℕ))

/-- For every fixed microscopic width, the original window lies strictly
inside the sphere in all sufficiently large dimensions. -/
theorem original_source_window_eventually_interior
    {Q w : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1) (_hw : 0 ≤ w) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧
      0 < Real.sqrt Q-w/Real.sqrt (n+2:ℕ) ∧
      Real.sqrt Q+w/Real.sqrt (n+2:ℕ) < 1 := by
  let q := Real.sqrt Q
  have hq0 : 0 < q := Real.sqrt_pos.mpr hQ0
  have hq1 : q < 1 := by
    have hh : Real.sqrt Q < Real.sqrt 1 := Real.sqrt_lt_sqrt hQ0.le hQ1
    simpa only [Real.sqrt_one,q] using hh
  let δ := min q (1-q)
  have hδ : 0 < δ := lt_min hq0 (by linarith)
  have hwidth : Tendsto (fun n : ℕ => w/Real.sqrt (n+2:ℕ))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [one_div,one_mul,div_eq_mul_inv,mul_zero] using
      NatLogWindowScales.inverse_sqrt_dimension_tendsto_zero.const_mul w
  filter_upwards [eventually_ge_atTop 2,
    hwidth.eventually (gt_mem_nhds hδ)] with n hn hsmall
  have hδq : δ ≤ q := min_le_left _ _
  have hδ1 : δ ≤ 1-q := min_le_right _ _
  exact ⟨hn,by dsimp [q] at *; linarith,by dsimp [q] at *; linarith⟩

/-- The full-cap ratio and microscopic Gaussian-window ratio for the
original value-conditioned posterior. The chosen cap works for every fixed
microscopic width and all energy shifts in the supplied compact interval. -/
theorem pure_original_cap_gaussian_ratios_uniform
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (u : ∀ n : ℕ, Vector (n+2))
    (hu : ∀ n : ℕ, ‖u n‖^2=(n+2:ℕ))
    (L : ℝ) (hL : 0 ≤ L) :
    let q := Real.sqrt Q
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    ∃ a b ε κ : ℝ,
      1/Real.sqrt 2 < a ∧ a < q-b ∧ 0 < b ∧ q+b < 1-ε ∧
      0 < ε ∧ ε < 1 ∧ 0 < κ ∧
      κ = SphericalPureLaplaceUniformLogCurvature.purePrintedKStar p hp β Q ∧
      pureResidualCoefficient p β a < 1/2 ∧ cp < β*a^p ∧
      ∀ w : ℝ, 0 < w →
        TendstoUniformlyOn
          (fun n t => originalSourceCapMean p (by omega) β Q ep cp a u hu n t /
            originalSourceCapMean p (by omega) β Q ep cp a u hu n 0)
          (fun t => Real.exp (β*t*q^p)) atTop (Icc (-L) L) ∧
        TendstoUniformlyOn
          (fun n t => originalSourceWindowMean p (by omega) β Q ep cp q w u hu n t /
            originalSourceCapMean p (by omega) β Q ep cp a u hu n 0)
          (fun t => Real.exp (β*t*q^p)*gaussianWindowFraction κ w)
          atTop (Icc (-L) L) ∧
        TendstoUniformlyOn
          (fun n t => (originalSourceCapMean p (by omega) β Q ep cp a u hu n t-
            originalSourceWindowMean p (by omega) β Q ep cp q w u hu n t) /
            originalSourceCapMean p (by omega) β Q ep cp a u hu n 0)
          (fun t => Real.exp (β*t*q^p)*(1-gaussianWindowFraction κ w))
          atTop (Icc (-L) L) := by
  dsimp only
  let q := Real.sqrt Q
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  obtain ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,hRatios⟩ :=
    sourcePure_cap_gaussian_ratios_uniform p hp h L hL
  refine ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,?_⟩
  have ha0 : 0 < a := lt_trans (by positivity : (0:ℝ)<1/Real.sqrt 2) ha
  have ha1 : a < 1 := by linarith
  have hCapEq : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      originalSourceCapMean p (by omega) β Q ep cp a u hu n t =
        sourceCapMean p β ep cp a n t := by
    filter_upwards [eventually_ge_atTop 2] with n hn t
    exact sourceCapMean_eq_original_conditioned n p hn hp
      h.overlap_range.1 (u n) (hu n) β ep cp a t ha0 ha1
  intro w hw
  have hInterior := original_source_window_eventually_interior
    h.overlap_range.1 h.overlap_range.2 hw.le
  have hWinEq : ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      originalSourceWindowMean p (by omega) β Q ep cp q w u hu n t =
        sourceWindowMean p β ep cp q w n t := by
    filter_upwards [hInterior] with n hn t
    exact sourceWindowMean_eq_original_conditioned n p hn.1 hp
      h.overlap_range.1 (u n) (hu n) β ep cp q w t hn.2.1 hn.2.2 hw.le
  obtain ⟨hFull,hWindow,hOutside⟩ := hRatios w hw
  refine ⟨?_,?_,?_⟩
  · apply hFull.congr
    filter_upwards [hCapEq] with n hn t ht
    change sourceCapMean p β ep cp a n t/sourceCapMean p β ep cp a n 0 =
      originalSourceCapMean p (by omega) β Q ep cp a u hu n t /
        originalSourceCapMean p (by omega) β Q ep cp a u hu n 0
    exact congrArg₂ (· / ·) (hn t).symm (hn 0).symm
  · apply hWindow.congr
    filter_upwards [hCapEq,hWinEq] with n hnC hnW t ht
    change sourceWindowMean p β ep cp q w n t/sourceCapMean p β ep cp a n 0 =
      originalSourceWindowMean p (by omega) β Q ep cp q w u hu n t /
        originalSourceCapMean p (by omega) β Q ep cp a u hu n 0
    exact congrArg₂ (· / ·) (hnW t).symm (hnC 0).symm
  · apply hOutside.congr
    filter_upwards [hCapEq,hWinEq] with n hnC hnW t ht
    change (sourceCapMean p β ep cp a n t-sourceWindowMean p β ep cp q w n t) /
      sourceCapMean p β ep cp a n 0 =
      (originalSourceCapMean p (by omega) β Q ep cp a u hu n t-
        originalSourceWindowMean p (by omega) β Q ep cp q w u hu n t) /
        originalSourceCapMean p (by omega) β Q ep cp a u hu n 0
    exact congrArg₂ (· / ·)
      (congrArg₂ (· - ·) (hnC t).symm (hnW t).symm) (hnC 0).symm

/-- The original posterior microscopic mean has a fixed positive fraction
of the original full-cap mean throughout a fixed centered energy interval. -/
theorem pure_original_cap_window_lower_uniform
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (u : ∀ n : ℕ, Vector (n+2))
    (hu : ∀ n : ℕ, ‖u n‖^2=(n+2:ℕ))
    (L : ℝ) (hL : 0 ≤ L) :
    let q := Real.sqrt Q
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    ∃ a κ r : ℝ, 1/Real.sqrt 2 < a ∧ a < q ∧
      0 < κ ∧ κ = SphericalPureLaplaceUniformLogCurvature.purePrintedKStar p hp β Q ∧
      0 < r ∧ r = Real.exp (-β*L*q^p)*gaussianWindowFraction κ 1/2 ∧
      ∀ᶠ n : ℕ in atTop, ∀ t ∈ Icc (-L) L,
        r*originalSourceCapMean p (by omega) β Q ep cp a u hu n 0 ≤
          originalSourceWindowMean p (by omega) β Q ep cp q 1 u hu n t := by
  dsimp only
  let q := Real.sqrt Q
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  obtain ⟨a,κ,r,ha,haq,hκ,hκEq,hr,hrEq,hRaw⟩ :=
    sourcePure_cap_window_lower_uniform p hp h L hL
  refine ⟨a,κ,r,ha,haq,hκ,hκEq,hr,hrEq,?_⟩
  have ha0 : 0 < a := lt_trans (by positivity : (0:ℝ)<1/Real.sqrt 2) ha
  have ha1 : a < 1 := by
    have hq1 : q < 1 := by
      have hh : Real.sqrt Q < Real.sqrt 1 :=
        Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
      simpa only [Real.sqrt_one,q] using hh
    exact haq.trans hq1
  have hCapEq : ∀ᶠ n : ℕ in atTop,
      originalSourceCapMean p (by omega) β Q ep cp a u hu n 0 =
        sourceCapMean p β ep cp a n 0 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact sourceCapMean_eq_original_conditioned n p hn hp
      h.overlap_range.1 (u n) (hu n) β ep cp a 0 ha0 ha1
  have hInterior := original_source_window_eventually_interior
    h.overlap_range.1 h.overlap_range.2 (by norm_num : (0:ℝ) ≤ 1)
  filter_upwards [hRaw,hCapEq,hInterior] with n hn hnC hnI t ht
  have hnW := sourceWindowMean_eq_original_conditioned n p hnI.1 hp
    h.overlap_range.1 (u n) (hu n) β ep cp q 1 t hnI.2.1 hnI.2.2
      (by norm_num : (0:ℝ) ≤ 1)
  change originalSourceWindowMean p (by omega) β Q ep cp q 1 u hu n t =
    sourceWindowMean p β ep cp q 1 n t at hnW
  calc
    r*originalSourceCapMean p (by omega) β Q ep cp a u hu n 0 =
        r*sourceCapMean p β ep cp a n 0 := by rw [hnC]
    _ ≤ sourceWindowMean p β ep cp q 1 n t := hn t ht
    _ = originalSourceWindowMean p (by omega) β Q ep cp q 1 u hu n t := hnW.symm

end
end SlowEquilibration.SphericalPureCapOriginalSourceRatios
