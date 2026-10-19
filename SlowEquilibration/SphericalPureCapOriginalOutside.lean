-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapOriginalSourceRatios

/-! Identify the actual posterior mean on the half-open source cap with
the closed microscopic window removed. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapOriginalOutside
noncomputable section
open Filter Set MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalTAPCertificate
open SphericalPureOriginalConditionalBandFubini
open SphericalPureCapOriginalSourceRatios SphericalPureCapSourceRatios
open SphericalPureCapSourceScalars SourceGaussianLaplaceRatio
open PureStationarity
open scoped Topology
set_option autoImplicit false

/-- Posterior linearity for a Borel latitude subset of another Borel set.
This is proved through the original Fubini identity and set-integral
subtraction, so no formal indicator independence is assumed. -/
theorem pure_original_conditioned_band_mean_sdiff
    (n p : ℕ) (hn : 2 ≤ n) (hp : 4 ≤ p)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (β H : ℝ) (I W : Set ℝ)
    (hI : MeasurableSet I) (hW : MeasurableSet W) (hWI : W ⊆ I) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u (I\W))
      ∂valueConditionedLaw c u hu (s*H/(n+1:ℕ))) =
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u I)
      ∂valueConditionedLaw c u hu (s*H/(n+1:ℕ))) -
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u W)
      ∂valueConditionedLaw c u hu (s*H/(n+1:ℕ))) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  let g := originalPureMeanProfile n p 1 β H u
  have hset : overlapRegion u (I\W) =
      overlapRegion u I \ overlapRegion u W := by
    ext z
    simp only [overlapRegion, Set.mem_ofPred_eq, Set.mem_sdiff]
  have hsub : overlapRegion u W ⊆ overlapRegion u I :=
    fun z hz => hWI hz
  have hg : IntegrableOn g (overlapRegion u I) (sphereLaw (n+1)) :=
    ((integrable_sphere_of_continuous (by omega : 1 ≤ n+1)
      (originalPureMeanProfile_continuous n p 1 β H u))).integrableOn
  rw [pure_original_conditioned_band_mean_sphere n p (by omega)
    1 (by positivity) hQ u hu β H (I\W) (hI.diff hW)]
  rw [pure_original_conditioned_band_mean_sphere n p (by omega)
    1 (by positivity) hQ u hu β H I hI]
  rw [pure_original_conditioned_band_mean_sphere n p (by omega)
    1 (by positivity) hQ u hu β H W hW]
  change (∫ z in overlapRegion u (I\W), g z ∂sphereLaw (n+1)) =
    (∫ z in overlapRegion u I, g z ∂sphereLaw (n+1)) -
    (∫ z in overlapRegion u W, g z ∂sphereLaw (n+1))
  rw [hset]
  exact setIntegral_sdiff (overlapRegion_measurable u hW) hg hsub

/-- The original conditional mean on the half-open cap with the closed
microscopic window removed. -/
def originalSourceOutsideMean (p : ℕ) (hp : 2 ≤ p) (β Q ep cp a q w : ℝ)
    (u : ∀ n : ℕ, Vector (n+2))
    (hu : ∀ n : ℕ, ‖u n‖^2=(n+2:ℕ)) (n : ℕ) (t : ℝ) : ℝ :=
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let s := (Real.sqrt Q)^p
  ∫ J, partitionOn β (field (mixtureCoefficients μ) J)
    (overlapRegion (u n)
      (Ico a 1 \ Icc (q-w/Real.sqrt (n+2:ℕ))
        (q+w/Real.sqrt (n+2:ℕ))))
    ∂valueConditionedLaw c (u n) (hu n)
      (s*(((n+2:ℕ):ℝ)*ep+t-Real.log (n+2:ℕ)/(2*cp))/(n+2:ℕ))

/-- For fixed cap and width, the microscopic window is eventually a subset
of the cap. -/
theorem original_source_window_eventually_inside_cap
    {Q a w : ℝ} (hQ0 : 0 < Q) (hQ1 : Q < 1)
    (ha : a < Real.sqrt Q) (_hw : 0 ≤ w) :
    ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧
      Icc (Real.sqrt Q-w/Real.sqrt (n+2:ℕ))
        (Real.sqrt Q+w/Real.sqrt (n+2:ℕ)) ⊆ Ico a 1 := by
  let q := Real.sqrt Q
  have hq1 : q < 1 := by
    have hh := Real.sqrt_lt_sqrt hQ0.le hQ1
    simpa only [Real.sqrt_one,q] using hh
  let δ := min (q-a) (1-q)
  have hδ : 0 < δ := lt_min (by dsimp [q]; linarith [ha]) (by linarith)
  have hwidth : Tendsto (fun n : ℕ => w/Real.sqrt (n+2:ℕ))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [one_div,one_mul,div_eq_mul_inv,mul_zero] using
      NatLogWindowScales.inverse_sqrt_dimension_tendsto_zero.const_mul w
  filter_upwards [eventually_ge_atTop 2,
    hwidth.eventually (gt_mem_nhds hδ)] with n hn hsmall
  have hleft : a ≤ q-w/Real.sqrt (n+2:ℕ) := by
    have hh : δ ≤ q-a := min_le_left _ _
    linarith
  have hright : q+w/Real.sqrt (n+2:ℕ) < 1 := by
    have hh : δ ≤ 1-q := min_le_right _ _
    linarith
  refine ⟨hn,?_⟩
  intro z hz
  exact ⟨hleft.trans hz.1,hz.2.trans_lt hright⟩

/-- At all sufficiently large dimensions, the posterior mean outside the
microscopic window is exactly the cap mean minus the window mean. -/
theorem original_source_outside_mean_eq_sub_eventually
    (p : ℕ) (hp : 4 ≤ p) {Q : ℝ}
    (hQ0 : 0 < Q) (hQ1 : Q < 1)
    (β ep cp a q w : ℝ)
    (ha : a < q) (hq : q = Real.sqrt Q) (hw : 0 ≤ w)
    (u : ∀ n : ℕ, Vector (n+2))
    (hu : ∀ n : ℕ, ‖u n‖^2=(n+2:ℕ)) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      originalSourceOutsideMean p (by omega) β Q ep cp a q w u hu n t =
        originalSourceCapMean p (by omega) β Q ep cp a u hu n t -
        originalSourceWindowMean p (by omega) β Q ep cp q w u hu n t := by
  subst q
  filter_upwards [original_source_window_eventually_inside_cap hQ0 hQ1 ha hw]
    with n hn t
  have hnorm : ‖u n‖^2=(n+1+1:ℕ) := by
    simpa only [Nat.add_assoc,Nat.reduceAdd] using hu n
  have hh := pure_original_conditioned_band_mean_sdiff
    (n+1) p (by omega) hp hQ0 (u n) hnorm β
    (((n+2:ℕ):ℝ)*ep+t-Real.log (n+2:ℕ)/(2*cp))
    (Ico a 1)
    (Icc (Real.sqrt Q-w/Real.sqrt (n+2:ℕ))
      (Real.sqrt Q+w/Real.sqrt (n+2:ℕ)))
    measurableSet_Ico measurableSet_Icc hn.2
  simpa only [originalSourceOutsideMean,originalSourceCapMean,
    originalSourceWindowMean,Nat.add_assoc,Nat.reduceAdd] using hh

/-- All three source `pc-laplace` ratios, with the third numerator being the
original posterior mean on `[a,1) \ I_{N,w}` itself. -/
theorem pure_original_cap_all_three_ratios_uniform
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
          (fun n t => originalSourceOutsideMean p (by omega) β Q ep cp a q w u hu n t /
            originalSourceCapMean p (by omega) β Q ep cp a u hu n 0)
          (fun t => Real.exp (β*t*q^p)*(1-gaussianWindowFraction κ w))
          atTop (Icc (-L) L) := by
  dsimp only
  let q := Real.sqrt Q
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  obtain ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,hRatios⟩ :=
    pure_original_cap_gaussian_ratios_uniform p hp h u hu L hL
  refine ⟨a,b,ε,κ,ha,hab,hb,hqε,hε,hε1,hκ,hκEq,hres,hdepth,?_⟩
  intro w hw
  obtain ⟨hFull,hWindow,hDiff⟩ := hRatios w hw
  refine ⟨hFull,hWindow,?_⟩
  have haq : a < q := by linarith
  have hOutside := original_source_outside_mean_eq_sub_eventually
    p hp h.overlap_range.1 h.overlap_range.2 β ep cp a q w haq rfl hw.le u hu
  apply hDiff.congr
  filter_upwards [hOutside] with n hn t ht
  change (originalSourceCapMean p (by omega) β Q ep cp a u hu n t-
      originalSourceWindowMean p (by omega) β Q ep cp q w u hu n t) /
      originalSourceCapMean p (by omega) β Q ep cp a u hu n 0 =
    originalSourceOutsideMean p (by omega) β Q ep cp a q w u hu n t /
      originalSourceCapMean p (by omega) β Q ep cp a u hu n 0
  exact congrArg (· / originalSourceCapMean p (by omega) β Q ep cp a u hu n 0)
    (hn t).symm

end
end SlowEquilibration.SphericalPureCapOriginalOutside
