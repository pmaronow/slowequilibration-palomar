-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureRetainedCenterFirstMoment
public import SlowEquilibration.SourcePureSameCenterProbability

/-! The original proper-pure retained centers, ordinary-center mean, and
logarithmic centering are selected together from one first-moment package.
The second-moment argument gives a small zero-count probability in wide
fixed centered windows, without selecting a Hessian-biased maximizer. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureDenominatorCenteredData
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open TwoAtomStationarity SphericalTAPCertificate
open PairConditionalDeterminantMoments LatitudeGroundTrial
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem pure_denominator_center_data
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E := markE μ β x Q
    let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    ∃ m : ℕ → ℝ, ∃ M C cut η ε δ : ℝ,
      0 < M ∧ 0 < δ ∧
      let G := gap μ Q (markY β Q) (markZ x Q) ε η
      (∀ᶠ n : ℕ in atTop,
        |m n-((n+2:ℕ)*E-Real.log (n+2:ℕ)/(2*(β*x)))| ≤ M) ∧
      (∀ L R : ℝ, L ≤ R → Tendsto (fun n : ℕ =>
        sourceUnfilteredValueWindowMean (n+2) μ Q
          (sourcePureCenteredNormalizedWindow n m E δ L R))
        atTop (𝓝 (Real.exp (-(β*x)*L)-Real.exp (-(β*x)*R)))) ∧
      (∀ L : ℝ, 0 < L →
        Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | (sourceRetainedValueWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
            (g/2) C ε η E G J).toReal = 0}) atTop ≤
            (1+(1-ε)/(cut^2-ε)) /
              (Real.exp ((β*x)*L)-Real.exp (-(β*x)*L))) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let E := markE μ β x Q
  let g := (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  obtain ⟨n₀,m,M,C,cut,η,ε,δ,C₂,D,hM,hδ,hC,hcut,hη,hε,hC₂,hD,
    hFallback,hCenter,hUnfiltered,hMean,hMoments⟩ :=
    source_pure_actual_retained_center_first_moment p hp alpha halpha h
  refine ⟨m,M,C,cut,η,ε,δ,hM,hδ,?_,hUnfiltered,?_⟩
  · filter_upwards [eventually_ge_atTop n₀] with n hn
    exact (hCenter n hn).2.2
  intro L hL
  let G := gap μ Q (markY β Q) (markZ x Q) ε η
  let I (n : ℕ) := sourcePureCenteredNormalizedWindow n m E δ (-L) L
  let aN (n : ℕ) := sourceRetainedValueWindowMean (n+2) μ Q (I n)
    (g/2) C ε η E G
  let X (n : ℕ) (J : Disorder (n+3) μ.maxDegree) :=
    (sourceRetainedValueWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) (I n)
      (g/2) C ε η E G J).toReal
  let W := Real.exp ((β*x)*L)-Real.exp (-(β*x)*L)
  let k := 1+(1-ε)/(cut^2-ε)
  have hb : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hW : 0 < W := by
    dsimp [W]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith [hb,hL]))
  have hmean : Tendsto aN atTop (𝓝 W) := by
    simpa only [aN,I,W,G,E,g,neg_mul,mul_neg,neg_neg] using
      (hMean (-L) L (by linarith))
  have ha : ∀ᶠ n : ℕ in atTop, 0 < aN n :=
    hmean.eventually (eventually_gt_nhds hW)
  have hbounds : ∀ᶠ n : ℕ in atTop,
      ProbabilityTheory.variance (X n) (disorderLaw (n+3) μ.maxDegree) ≤
        D*sourcePrintedPairError (3/8 : ℝ) n*(aN n)^2+k*aN n ∧
      MemLp (X n) 2 (disorderLaw (n+3) μ.maxDegree) ∧
      (∫ J, X n J ∂disorderLaw (n+3) μ.maxDegree) = aN n := by
    filter_upwards [hMoments] with n hn
    have hi := hn (I n) (sourcePureCenteredNormalizedWindow_measurable
      n m E δ (-L) L)
      (sourcePureCenteredNormalizedWindow_subset_value_box
        n m E δ (-L) L)
    exact ⟨hi.2.2.2.2,hi.2.2.1,hi.2.1⟩
  have hrat : Tendsto (fun n => D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n)
      atTop (𝓝 (k/W)) := by
    have hErr : Tendsto (fun n => D*sourcePrintedPairError (3/8 : ℝ) n)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul
        (sourcePrintedPairError_tendsto (by norm_num : (1/4 : ℝ) < 3/8)
          (by norm_num : (3/8 : ℝ) < 1/2)) :
          Tendsto (fun n => D*sourcePrintedPairError (3/8 : ℝ) n) atTop (𝓝 (D*0)))
    have hInv : Tendsto (fun n => k/aN n) atTop (𝓝 (k/W)) :=
      tendsto_const_nhds.div hmean hW.ne'
    simpa only [zero_add] using hErr.add hInv
  have hPzero : ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+3) μ.maxDegree).real {J | X n J=0} ≤
        D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n := by
    filter_upwards [ha,hbounds] with n han hn
    let v := D*sourcePrintedPairError (3/8 : ℝ) n*(aN n)^2+k*aN n
    have hCheb := source_zero_probability_of_variance_bound
      (disorderLaw (n+3) μ.maxDegree) (X n) (aN n) v
      hn.2.1 han hn.2.2 hn.1
    have hv : 0 ≤ v := (ProbabilityTheory.variance_nonneg (X n)
      (disorderLaw (n+3) μ.maxDegree)).trans hn.1
    have hReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hCheb
    rw [ENNReal.toReal_ofReal (div_nonneg hv (sq_nonneg _))] at hReal
    have hEq : v/(aN n)^2 =
        D*sourcePrintedPairError (3/8 : ℝ) n+k/aN n := by
      dsimp [v]
      field_simp
    exact hReal.trans_eq hEq
  have hLow : IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real {J | X n J=0}) :=
    isCoboundedUnder_le_of_le atTop (fun n => measureReal_nonneg)
  have hlim := (limsup_le_limsup hPzero hLow hrat.isBoundedUnder_le).trans_eq
    hrat.limsup_eq
  simpa only [X,I,G,E,g,k,W,sub_eq_add_neg] using hlim

end
end SlowEquilibration.SphericalPureDenominatorCenteredData
