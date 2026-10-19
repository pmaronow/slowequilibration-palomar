-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapMarkedSourceIntegral
public import SlowEquilibration.SourcePureOriginalIntensityEnvelope
public import SlowEquilibration.SourceMixedLowSumIntegral
public import SlowEquilibration.SphericalPureCapDepth
public import SlowEquilibration.SphericalPureCapCenteringIdentity
public import SlowEquilibration.SourcePureCriticalPhysicalWindowBridge

/-! The original-field deep-energy estimate `eq:pc-deep`.  The cap cutoff
is fixed before the physical deficit window, and all critical points are
counted with their literal partition-function mark. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapDeepEnergyIntegral
noncomputable section
open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalTAPCertificate PureStationarity
open SphericalPureCapSourceScalars SphericalPureCapSourceRatios
open SphericalPureCapCenteringIdentity SphericalMarkedWindows
open SphericalPureCapIntegralDecomposition SphericalPureCapDepth
open SourcePureCapMarkedSourceIntegral SourcePureCapBorelMarkedValue
open SourcePureOriginalIntensityEnvelope SourceMixedLowSumIntegral
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem source_cap_mean_nonneg (p n : ℕ) (β ep cp a t : ℝ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    0 ≤ sourceCapMean p β ep cp a n t := by
  unfold sourceCapMean
  apply mul_nonneg ENNReal.toReal_nonneg
  apply intervalIntegral.integral_nonneg ha1
  intro z hz
  have hz' : z ∈ Icc a 1 := by simpa only [uIcc_of_le ha1] using hz
  have hbase : 0 ≤ 1-z^2 := by nlinarith [ha,hz'.1,hz'.2]
  unfold rawDensity
  exact mul_nonneg (Real.rpow_nonneg hbase _) (Real.exp_pos _).le

/-- The literal scalar cap mean loses the exact source exponential factor
when the physical critical value is lowered. -/
theorem source_cap_mean_depth_le (p n : ℕ) (hn : 2 ≤ n)
    {β ep cp a v : ℝ} (hβ : 0 < β) (ha : 0 ≤ a) (ha1 : a < 1)
    (hv : 0 ≤ v) :
    sourceCapMean p β ep cp a n (-v) ≤
      Real.exp (-β*v*a^p)*sourceCapMean p β ep cp a n 0 := by
  have hh := pure_cap_normalized_integral_depth_le p
    (H := (n+2:ℕ)*ep-Real.log (n+2:ℕ)/(2*cp)) hβ ha ha1 hv
    (n+2) (by omega)
  have hminus : ((n+2:ℕ):ℝ)*ep-Real.log (n+2:ℕ)/(2*cp)-v =
      (n+2:ℕ)*ep+(-v)-Real.log (n+2:ℕ)/(2*cp) := by ring
  rw [hminus] at hh
  simpa only [sourceCapMean,rawDensity,show n+2-1=n+1 by omega,add_zero]
    using hh

/-- An extended-real version of the already proved exponential integral,
allowing an arbitrary nonnegative integrand without a separate integrability
premise.  Empty physical windows are included. -/
theorem cap_below_window_lintegral_bound
    (f : ℝ → ℝ≥0∞) (l m L rate A : ℝ)
    (hrate : 0 < rate) (hA : 0 ≤ A)
    (hbound : ∀ H ∈ Icc l (m-L),
      f H ≤ ENNReal.ofReal (A*Real.exp (rate*(H-m)))) :
    (∫⁻ H in Icc l (m-L), f H) ≤
      ENNReal.ofReal (A/rate*Real.exp (-rate*L)) := by
  have hInt : IntegrableOn (fun H : ℝ => A*Real.exp (rate*(H-m)))
      (Icc l (m-L)) := by
    have hc : Continuous (fun H : ℝ => A*Real.exp (rate*(H-m))) := by fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_Icc
  calc
    _ ≤ ∫⁻ H in Icc l (m-L),
        ENNReal.ofReal (A*Real.exp (rate*(H-m))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with H hH
      exact hbound H hH
    _ = ENNReal.ofReal (∫ H in Icc l (m-L),
        A*Real.exp (rate*(H-m)) ∂volume) :=
      (ofReal_integral_eq_lintegral_ofReal hInt
        (.of_forall fun _ => mul_nonneg hA (Real.exp_pos _).le)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (integral_below_window_exp_bound _ l m L rate A hrate hA hInt
        (by intro H hH; exact le_refl _))

/-- The exact source deep-energy bound for the original amplitude-one pure
field. The lower endpoint may vary arbitrarily above a fixed exterior-box
floor; hence this includes the manuscript's vanishing-deficit window.
There is no supplied count, Palm, or expected partition-sum estimate. -/
theorem pure_original_deep_energy_cap_sum
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    {a δ g Z : ℝ} (ha : a ∈ Ioo (0:ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2)
    (hdepth : pureIntensityConstant p (by omega) < β*a^p)
    (hδ : 0 < δ) (hg : 0 < g)
    (hLeft : 2*Real.sqrt ((FiniteMixture.pure p (by omega) 1 (by positivity)).xi2 1)+g ≤
      (p:ℝ)*(pureEnergyConstant p (by omega)-δ))
    (hRight : (p:ℝ)*(pureEnergyConstant p (by omega)+δ) ≤ Z)
    (u : ∀ d : ℕ, Vector (d+2)) (hu : ∀ d : ℕ, ‖u d‖^2=(d+2:ℕ)) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let ep := pureEnergyConstant p (by omega)
    let cp := pureIntensityConstant p (by omega)
    let m d := (d+2:ℕ)*ep-Real.log (d+2:ℕ)/(2*cp)
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ L : ℝ, 0 ≤ L → ∀ l : ℝ, (d+2:ℕ)*(ep-δ) ≤ l →
        (∫⁻ J, actualScoreWindowCount (d+1)
          (centerCoefficients (mixtureCoefficients μ) 1)
          (physicalEnergyWindow (d+2) (Icc l (m d-L)) univ)
          (originalBorelBandMark d μ β (Ico a 1)) J
          ∂disorderLaw (d+2) μ.maxDegree) ≤
        ENNReal.ofReal (C*sourceCapMean p β ep cp a d 0*
          Real.exp (-(β*a^p-cp)*L)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let m (d : ℕ) : ℝ := (d+2:ℕ)*ep-Real.log (d+2:ℕ)/(2*cp)
  have hcp : 0 < cp := pureIntensityConstant_pos p (by omega)
  have hrate : 0 < β*a^p-cp := sub_pos.mpr hdepth
  obtain ⟨Cmark,hCmark,hMark⟩ :=
    pure_original_marked_cap_source_integral p hp β ep cp a ha hsub hg u hu
  obtain ⟨Cenv,hCenv,hEnv⟩ :=
    pure_original_criticalPhysicalIntensity_centered_envelope p hp h hδ hg
      hLeft hRight m (M := 0) (by norm_num)
      (.of_forall fun d => by simp only [m,ep,cp,sub_self,abs_zero,le_refl])
  let C := Cenv*Cmark/(β*a^p-cp)
  have hC : 0 < C := div_pos (mul_pos hCenv hCmark) hrate
  refine ⟨C,hC,?_⟩
  filter_upwards [hMark,hEnv,eventually_ge_atTop 2] with d hmark henv hd
  intro L hL l hl
  let N : ℝ := (d+2:ℕ)
  let A := sourceCapMean p β ep cp a d 0
  have hN : 0 < N := by dsimp [N]; positivity
  have hm : m d ≤ N*ep := by
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by
      dsimp [N]
      exact_mod_cast (show 1 ≤ d+2 by omega))
    dsimp [m,N] at *
    exact sub_le_self _ (div_nonneg hlog (by positivity))
  have hA : 0 ≤ A := source_cap_mean_nonneg p d β ep cp a 0 ha.1.le ha.2.le
  have hBox (H : ℝ) (hH : H ∈ Icc l (m d-L)) :
      H ∈ Icc (N*(ep-δ)) (N*(ep+δ)) := by
    constructor
    · exact hl.trans hH.1
    · nlinarith [hH.2,hL,hm,hδ,hN]
  have hEdge (H : ℝ) (hH : H ∈ Icc l (m d-L)) :
      2*Real.sqrt (μ.xi2 1)+g ≤ (p:ℝ)*(H/(d+2:ℕ)) := by
    have hlow : ep-δ ≤ H/N := (le_div_iff₀ hN).mpr (by
      simpa only [mul_comm] using (hBox H hH).1)
    exact hLeft.trans (mul_le_mul_of_nonneg_left hlow (by positivity))
  have hKR := hmark (Icc l (m d-L)) measurableSet_Icc hEdge
  have hTail := cap_below_window_lintegral_bound
    (fun H => pureCriticalPhysicalIntensity d p (by omega) 1 (by positivity) 1 H *
      (ENNReal.ofReal Cmark*ENNReal.ofReal (sourceCapMean p β ep cp a d (H-m d))))
    l (m d) L (β*a^p-cp) (Cenv*Cmark*A) hrate (by positivity) (by
      intro H hH
      have hDensReal := henv H (hBox H hH)
      have hDens : pureCriticalPhysicalIntensity d p (by omega) 1 (by positivity) 1 H ≤
          ENNReal.ofReal (Cenv*Real.exp (cp*(m d-H))) := by
        rw [← ENNReal.ofReal_toReal
          (pureCriticalPhysicalIntensity_ne_top d p (by omega) 1 (by positivity) 1 H)]
        exact ENNReal.ofReal_le_ofReal hDensReal
      have hv : 0 ≤ m d-H := by linarith [hH.2,hL]
      have hMean := source_cap_mean_depth_le p d hd (ep:=ep) (cp:=cp)
        h.beta_pos ha.1.le ha.2 hv
      have hshift : -(m d-H)=H-m d := by ring
      rw [hshift] at hMean
      have hMean' : ENNReal.ofReal (sourceCapMean p β ep cp a d (H-m d)) ≤
          ENNReal.ofReal (Real.exp (-β*(m d-H)*a^p)*A) :=
        ENNReal.ofReal_le_ofReal hMean
      calc
        _ ≤ ENNReal.ofReal (Cenv*Real.exp (cp*(m d-H))) *
            (ENNReal.ofReal Cmark*
              ENNReal.ofReal (Real.exp (-β*(m d-H)*a^p)*A)) :=
          mul_le_mul' hDens (mul_le_mul' le_rfl hMean')
        _ = ENNReal.ofReal ((Cenv*Cmark*A)*Real.exp ((β*a^p-cp)*(H-m d))) := by
          rw [← ENNReal.ofReal_mul hCmark.le,
            ← ENNReal.ofReal_mul (mul_nonneg hCenv.le (Real.exp_pos _).le)]
          congr 1
          have he : Real.exp (cp*(m d-H))*Real.exp (-β*(m d-H)*a^p) =
              Real.exp ((β*a^p-cp)*(H-m d)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          calc
            _ = Cenv*Cmark*A*(Real.exp (cp*(m d-H))*
                Real.exp (-β*(m d-H)*a^p)) := by ring
            _ = _ := by rw [he])
  have hFinal : (Cenv*Cmark*A)/(β*a^p-cp)*Real.exp (-(β*a^p-cp)*L) =
      C*A*Real.exp (-(β*a^p-cp)*L) := by dsimp [C]; ring
  exact hKR.trans (hTail.trans_eq (congrArg ENNReal.ofReal hFinal))

end
end SlowEquilibration.SourcePureCapDeepEnergyIntegral
